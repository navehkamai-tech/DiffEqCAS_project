function factor_evidence(factor, sys::DESys)
    if _contains_equal(sys.ps, factor) && isempty(_evidence_domain(sys.domain, factor).blocks)
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, undetermined)
    end
    return domain_evidence(factor, sys.domain)
end

factor_sign(factor, sys::DESys) = factor_evidence(factor, sys).sign
factor_sign(factor, sys::DETree) =
    length(sys.active) == 1 ?
    factor_sign(factor, sys.nodes[first(sys.active)].system) :
    throw(ArgumentError("factor sign requires one selected branch"))

factor_divisibility(factor, sys::DESys) = factor_evidence(factor, sys).divisibility
factor_divisibility(factor, sys::DETree) =
    length(sys.active) == 1 ?
    factor_divisibility(factor, sys.nodes[first(sys.active)].system) :
    throw(ArgumentError("factor divisibility requires one selected branch"))

# ===========================================================================
# 1. Domain-Level Evidence & Feasibility Engine (Pure SymDomain, no DESys)
# ===========================================================================

const cache_size = Ref{Int64}(1024)
global cache = LRU{Any,Any}(maxsize=cache_size[])

function _evidence_domain(domain::SymDomain, expr)
    expr_variables = Symbolics.get_variables(Symbolics.unwrap(expr))
    relevant = DomBlock[
        b for b in domain.blocks if any(v -> _contains_equal(b.variables, v), expr_variables)]
    return EvidenceDomain(domain, relevant, blocks_content_key(domain, relevant), nothing)
end

function _ctx_domain!(ctx::EvidenceDomain)
    ctx.sub === nothing && (ctx.sub = subdomain(ctx.source, ctx.blocks))
    return ctx.sub
end

"""
    domain_evidence(expr, domain::SymDomain) -> ConstraintEvidence

Staged sign, bound, and zero-set inference for `expr` over `domain`.
Runs cheap algebraic/interval stages first (`_prime_domain_bounds!`, `_infer_tree`,
`_affine_factor_evidence`) before falling back to branch-and-prune paving.
"""
function domain_evidence(expr, domain::SymDomain)
    ctx = _evidence_domain(domain, expr)
    key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
    haskey(cache, key) && return cache[key]
    result = _domain_evidence_uncached(expr, ctx)
    cache[key] = result
    return result
end

function _domain_evidence_uncached(expr, ctx::EvidenceDomain)
    # Stage 1: Prime the global cache with exact 1D affine bounds from domain blocks
    _prime_domain_bounds!(ctx)

    # Stage 2: Fast structural and interval arithmetic tree walk
    best_evidence = _infer_tree(expr, ctx)
    if best_evidence.divisibility !== undetermined || isempty(ctx.blocks)
        return best_evidence
    end

    # Stage 3+: Progressive refinement (Affine -> Centered -> Sturm -> Paved)
    for stage in (
        _affine_factor_evidence,
        _centered_factor_evidence,
        _sturm_factor_evidence,
        _paved_factor_evidence,
    )
        result = stage(expr, ctx)
        if result !== nothing
            new_bound = intersect_interval(best_evidence.bound, result.bound)
            new_sign = result.sign !== undetermined ? result.sign : best_evidence.sign
            new_divis = result.divisibility !== undetermined ? result.divisibility : best_evidence.divisibility
            if new_divis === undetermined && (new_sign in (positive, negative) || !(0 in new_bound))
                new_divis = divisible
            end
            best_evidence = ConstraintEvidence(new_bound, new_divis, new_sign)
            best_evidence.divisibility !== undetermined && return best_evidence
        end
    end
    return best_evidence
end

"""
    relation_status(rel::SymRelation, domain::SymDomain) -> Symbol

Classify `rel` (`residual ⋈ 0`) over `domain` using the staged evidence pipeline:
- `:redundant`  if `rel` holds everywhere on `domain`
- `:infeasible` if `rel` holds nowhere on `domain`
- `:active`     if both `rel` and its negation are satisfiable on `domain`
"""
function relation_status(rel::SymRelation, domain::SymDomain)::Symbol
    ctx = _evidence_domain(domain, rel.residual)
    isempty(ctx.blocks) && return :active

    # Fast Path (Stages 1 & 2): Prime 1D affine bounds and run interval/sign tree inference!
    # This resolves 1D intervals (e.g. x > 2 vs x > 0) and sign-definite expressions
    # with ZERO paving overhead.
    _prime_domain_bounds!(ctx) || return :infeasible
    ev = _infer_tree(simplify(rel.residual), ctx)
    lo, hi = inf(ev.bound), sup(ev.bound)
    op = _get_relation(rel)

    if op === (>)
        (lo > 0.0 || ev.sign === positive) && return :redundant
        (hi <= 0.0 || ev.sign in (negative, iszero)) && return :infeasible
    elseif op === (>=)
        (lo >= 0.0 || ev.sign in (positive, iszero)) && return :redundant
        (hi < 0.0 || ev.sign === negative) && return :infeasible
    elseif op === (<)
        (hi < 0.0 || ev.sign === negative) && return :redundant
        (lo >= 0.0 || ev.sign in (positive, iszero)) && return :infeasible
    elseif op === (<=)
        (hi <= 0.0 || ev.sign in (negative, iszero)) && return :redundant
        (lo > 0.0 || ev.sign === positive) && return :infeasible
    elseif op === (==)
        (lo == 0.0 && hi == 0.0 || ev.sign === iszero) && return :redundant
        (lo > 0.0 || hi < 0.0 || ev.divisibility === divisible) && return :infeasible
    elseif op === (!=)
        (lo > 0.0 || hi < 0.0 || ev.divisibility === divisible) && return :redundant
        (lo == 0.0 && hi == 0.0 || ev.sign === iszero) && return :infeasible
    end

    expr_vars = Symbolics.get_variables(Symbolics.unwrap(rel.residual))
    if length(expr_vars) == 1 && _affine_coefficients(Symbolics.unwrap(rel.residual), Symbolics.unwrap(only(expr_vars))) !== nothing
        return :active
    end

    # Fallback (Stages 3 & 4): Future Sturm/Centered stages or HC4Revise Paving
    sub_dom = _ctx_domain!(ctx)
    # 1. Is `rel` itself satisfiable on `sub_dom`?
    rel_sat = _raw_relation_satisfiable(rel, sub_dom, true)
    rel_sat || return :infeasible

    # 2. Is the negation of `rel` satisfiable on `sub_dom`?
    # If the negation cannot be satisfied, `rel` is redundant!
    neg_rel = _negate_relation(rel)
    needs_boundary = (neg_rel.relation === Symbol("=="))
    neg_sat = _raw_relation_satisfiable(neg_rel, sub_dom, needs_boundary)
    return neg_sat ? :active : :redundant
end

# Direct paving check on a single relation without recursing into `add_constraints`
function _raw_relation_satisfiable(rel::SymRelation, sub_dom::SymDomain, include_boundary::Bool)
    all_vars = copy(sub_dom.variables)
    for v in Symbolics.get_variables(Symbolics.unwrap(rel.residual))
        _push_unique!(all_vars, (_as_num(v),))
    end
    sort!(all_vars, by=string)
    c_new = DomConstraint(rel)
    all_cs = vcat(sub_dom.constraints, [c_new])
    block = DomBlock(all_vars, ConstraintId[c.id for c in all_cs])
    temp_dom = SymDomain(all_cs, [block])
    inner, boundary = _pave_block(temp_dom, temp_dom.blocks[1])
    return include_boundary ? (!isempty(inner) || !isempty(boundary)) : !isempty(inner)
end

# beginning of the pipeline - always called first
function _prime_domain_bounds!(ctx::EvidenceDomain)
    for block in ctx.blocks
        ivs = block.variables
        bounds = Dict(iv => IntervalArithmetic.Interval(-Inf, Inf) for iv in ivs)
        strict_lo = Dict(iv => false for iv in ivs)
        strict_hi = Dict(iv => false for iv in ivs)
        for constraint in constraints_of(ctx.source, block)
            op = _get_relation(constraint.relation)
            op === (!=) && continue
            expr = Symbolics.unwrap(constraint.relation.residual)
            expr_vars = Symbolics.get_variables(expr)
            constraint_ivs = [iv for iv in ivs if _contains_equal(expr_vars, iv)]
            length(constraint_ivs) == 1 || continue
            iv = only(constraint_ivs)
            is_feasible = _update_affine_bound!(bounds, strict_lo, strict_hi, expr, iv, op)
            is_feasible || return false
        end
        # Inject the bounds into the global cache to prime _infer_tree
        for (iv, bound) in bounds
            cache_key = (:constraint_evidence, Symbolics.unwrap(iv), (block_content_key(ctx.source, block),))
            lo, hi = inf(bound), sup(bound)
            s_lo, s_hi = strict_lo[iv], strict_hi[iv]
            sign_state = (hi < 0 || (hi == 0 && s_hi)) ? negative :
                         (lo > 0 || (lo == 0 && s_lo)) ? positive :
                         (lo == 0 && hi == 0) ? iszero : undetermined
            divis_state = (sign_state in (positive, negative) || !(0 in bound)) ? divisible :
                          (sign_state === iszero ? haszero : undetermined)
            cache[cache_key] = ConstraintEvidence(bound, divis_state, sign_state)
        end
    end
    return true
end

function _infer_tree(expr, ctx::EvidenceDomain)
    isequal(expr, 0) && return ConstraintEvidence(interval(0, 0), haszero, iszero)

    # 1. Check existing cache
    local key
    if !SU.iscall(expr)
        var_block = block_of(ctx.source, expr)
        if var_block !== nothing
            key = (:constraint_evidence, Symbolics.unwrap(expr), (block_content_key(ctx.source, var_block),))
        else
            key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
        end
    else
        key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
    end

    if haskey(cache, key)
        return cache[key]
    end

    # 2. Check exact literals
    literal = SU.unwrap_const(Symbolics.unwrap(expr))
    if literal isa Real
        return _evidence_from_literal(literal)
    end

    # 3. Recursive subexpression inference
    simplified = simplify(expr)
    SU.iscall(simplified) || return ConstraintEvidence(interval(-Inf, Inf), undetermined, undetermined)

    op = SU.operation(simplified)
    args = SU.arguments(simplified)

    # Recurse down. If a leaf is undetermined and not cached, this will bubble up.
    children = [_infer_tree(arg, ctx) for arg in args]
    result = _combine_child_evidence(op, children)

    # Only cache if we actually deduced something useful to save memory
    if result.sign !== undetermined || result.divisibility !== undetermined
        cache[key] = result
    end

    return result
end

function _combine_child_evidence(op, children)
    # 1. Compute continuous numeric bounds using IntervalArithmetic
    bounds = [child.bound for child in children]
    # Safely apply the operation to the intervals if supported, else default to unbounded
    new_bound = if op in (+, -, *, /)
        op(bounds...)
    else
        IntervalArithmetic.Interval(-Inf, Inf)
    end

    # 2. Structural deduction
    struct_sign = _structural_sign(op, children)

    # 3. Reconcile numeric bounds with structural deduction
    final_sign = _reconcile_sign(new_bound, struct_sign)
    final_divis = _reconcile_divisibility(new_bound, final_sign)

    return ConstraintEvidence(new_bound, final_divis, final_sign)
end

# affine checks
function _update_affine_bound!(bounds, strict_lo, strict_hi, expr, iv, op)
    affine = _affine_coefficients(expr, Symbolics.unwrap(iv))
    affine === nothing && return true
    coeff = SU.unwrap_const(affine[1])
    intercept = SU.unwrap_const(affine[2])
    (coeff isa Real && intercept isa Real) || return true
    val = Float64(-intercept / coeff)
    effective_op = coeff > 0 ? op : _reverse_relation(op)
    old_lo, old_hi = inf(bounds[iv]), sup(bounds[iv])
    if effective_op in ((<), (<=))
        is_strict = effective_op === (<)
        if val < old_hi || (val == old_hi && is_strict)
            strict_hi[iv] = is_strict
        end
        bounds[iv] = intersect_interval(bounds[iv], Interval(-Inf, val))
    elseif effective_op in ((>), (>=))
        is_strict = effective_op === (>)
        if val > old_lo || (val == old_lo && is_strict)
            strict_lo[iv] = is_strict
        end
        bounds[iv] = intersect_interval(bounds[iv], Interval(val, Inf))
    else # effective_op === (==)
        bounds[iv] = intersect_interval(bounds[iv], Interval(val, val))
    end
    isempty(bounds[iv]) && return false
    lo, hi = inf(bounds[iv]), sup(bounds[iv])
    (lo == hi && (strict_lo[iv] || strict_hi[iv])) && return false
    return true
end

function _affine_coefficients(expr, iv)
    res = _affine_walk(Symbolics.unwrap(expr), Symbolics.unwrap(iv))
    (res === nothing || isequal(res[1], 0)) && return nothing
    return res
end

function _affine_walk(expr, iv)
    isequal(expr, iv) && return (1, 0)
    _contains_equal(Symbolics.get_variables(expr), iv) || return (0, expr)
    SU.iscall(expr) || return nothing

    op = SU.operation(expr)
    args = SU.arguments(expr)

    if op === (+)
        parts = [_affine_walk(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        return (sum(p[1] for p in parts), sum(p[2] for p in parts))
    elseif op === (*)
        parts = [_affine_walk(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        var_parts = filter(p -> !isequal(p[1], 0), parts)
        length(var_parts) > 1 && return nothing
        c = prod(p[2] for p in parts if isequal(p[1], 0); init=1)
        isempty(var_parts) && return (0, c)
        vp = only(var_parts)
        return (vp[1] * c, vp[2] * c)
    elseif op === (/) && length(args) == 2
        lhs, rhs = _affine_walk(args[1], iv), _affine_walk(args[2], iv)
        (lhs === nothing || rhs === nothing) && return nothing
        isequal(rhs[1], 0) && !isequal(rhs[2], 0) && return (lhs[1] / rhs[2], lhs[2] / rhs[2])
    end
    return nothing
end

# Feasibility probes. The sign of `expr` over a domain is probed with
# non-strict inequalities; the zero set {expr = 0} is {expr <= 0} ∩ {expr >= 0},
# stated as two inequalities because domain constraints are inequalities.
function _sign_probe(expr, which::Symbol)
    which === :nonpositive && return [SymRelation(expr, Symbol("<="))]
    which === :nonnegative && return [SymRelation(expr, Symbol(">="))]
    which === :zero && return [SymRelation(expr, Symbol("<=")), SymRelation(expr, Symbol(">="))]
    throw(ArgumentError("unknown probe $which"))
end

_can_be(expr, domain::SymDomain, which::Symbol) =
    constraints_satisfiable(_sign_probe(expr, which), domain, true)

# Turn the three probe answers into evidence (shared by the affine and paved stages).
function _probe_evidence(factor, domain::SymDomain)
    _can_be(factor, domain, :nonpositive) ||
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, positive)
    _can_be(factor, domain, :nonnegative) ||
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, negative)
    _can_be(factor, domain, :zero) ||
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, either)
    return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), haszero, undetermined)
end

"""
    _affine_factor_evidence(factor, ctx, sys)

Classify a factor that is affine in one independent variable.
"""
function _affine_factor_evidence(factor, ctx::EvidenceDomain)
    factor_variables = Symbolics.get_variables(Symbolics.unwrap(factor))
    domain_vars = [iv for iv in ctx.source.variables if _contains_equal(factor_variables, iv)]
    length(domain_vars) == 1 || return nothing
    iv = only(domain_vars)

    coefficients = _affine_coefficients(Symbolics.unwrap(factor), Symbolics.unwrap(iv))
    coefficients === nothing && return nothing

    coeff_evidence = _infer_tree(coefficients[1], ctx)
    coeff_evidence.sign in (positive, negative) || return nothing

    block = block_of(ctx.source, iv)
    block === nothing && return nothing
    return _probe_evidence(factor, subdomain(ctx.source, [block]))
end

function _centered_factor_evidence(factor, ctx::EvidenceDomain)
    return nothing # PSEUDOCODE: replace with centered/mean-value forms.
end

function _sturm_factor_evidence(factor, ctx::EvidenceDomain)
    return nothing # PSEUDOCODE: replace with certified Sturm isolation.
end

function _paved_factor_evidence(factor, ctx::EvidenceDomain)
    return _probe_evidence(factor, _ctx_domain!(ctx))
end

# evidence helpers
function _evidence_from_literal(literal::Real)
    if literal > 0
        return ConstraintEvidence(interval(literal, literal), divisible, positive)
    elseif literal < 0
        return ConstraintEvidence(interval(literal, literal), divisible, negative)
    else
        return ConstraintEvidence(interval(literal, literal), haszero, iszero)
    end
end

function _structural_sign(op, children)
    if op === (+)
        all(c -> c.sign === positive, children) && return positive
        all(c -> c.sign === negative, children) && return negative
        all(c -> c.sign === iszero, children) && return iszero
    elseif op === (-) && length(children) == 1
        c = children[1]
        return c.sign === positive ? negative : c.sign === negative ? positive : c.sign === iszero ? iszero : undetermined
    elseif op === (*)
        any(c -> c.sign === iszero, children) && return iszero
        if all(c -> c.sign in (positive, negative), children)
            negatives = count(c -> c.sign === negative, children)
            return isodd(negatives) ? negative : positive
        end
    elseif op === (/) && length(children) == 2
        num, den = children
        num.sign === iszero && den.sign in (positive, negative) && return iszero
        if den.sign in (positive, negative) && num.sign in (positive, negative)
            return num.sign === den.sign ? positive : negative
        end
    end
    return undetermined
end

function _reconcile_sign(bound, struct_sign)
    # Numeric bounds take precedence if they strictly exclude zero
    sup(bound) < 0 && return negative
    inf(bound) > 0 && return positive
    inf(bound) == 0 && sup(bound) == 0 && return iszero

    # Fallback to structural sign if the interval crosses zero (or is NaN/Inf)
    return struct_sign
end

function _reconcile_divisibility(bound, final_sign)
    # Divisible if strictly positive/negative structurally, or if 0 is outside the interval
    if final_sign in (positive, negative) || !(0 ∈ bound)
        return divisible
    elseif final_sign === iszero || (inf(bound) == 0 && sup(bound) == 0)
        return haszero
    end
    return undetermined
end

function _reverse_relation(op)
    op === (<) && return (>)
    op === (<=) && return (>=)
    op === (>) && return (<)
    op === (>=) && return (<=)
end

function _has_depvar_or_diff(expr, sys::DESys)
    any(variable -> _contains_equal(sys.dvs, variable),
        Symbolics.get_variables(Symbolics.unwrap(expr))) && return true
    expression = Symbolics.unwrap(expr)
    SU.iscall(expression) || return false
    Symbolics.operation(expression) isa Differential && return true
    any(argument -> _has_depvar_or_diff(argument, sys),
        SU.arguments(expression))
end

function _can_divide_by(expr::Symbolics.Num, sys::DESys)
    _contains_equal(sys.dvs, expr) && return false
    _has_depvar_or_diff(expr, sys) && return false
    return factor_divisibility(expr, sys) === divisible
end

"""
Return syntactic numerator-factor candidates shared by every addend.
This function deliberately does not decide whether a factor is cancellable. It
only computes a conservative candidate list; `factor_divisibility` remains the
authority for domain-aware cancellation.
"""
function common_divisors(expr, sys::DESys)
    expr === nothing && throw(ArgumentError("input expression cannot be empty"))
    normalized = unwrap(simplify(expand(expand_derivatives(wrap(expr)))))
    addends = _additive_terms(normalized)
    isempty(addends) && return Any[]

    shared = _multiplicative_factors(first(addends))
    for addend in Iterators.drop(addends, 1)
        available = _multiplicative_factors(addend)
        retained = Any[]
        for candidate in shared
            index = findfirst(factor -> isequal(factor, candidate), available)
            index === nothing || (push!(retained, candidate); deleteat!(available, index))
        end
        shared = retained
        isempty(shared) && break
    end

    # Numeric constants do not improve an equation and can introduce
    # avoidable type conversions during division.
    [
        wrap(factor) for factor in _ordered_unique(shared)
                         if !(SU.unwrap_const(Symbolics.unwrap(factor)) isa Number)
    ]
end

common_divisors(expr, sys::DETree) =
    length(sys.active) == 1 ?
    common_divisors(expr, sys.nodes[first(sys.active)].system) :
    throw(ArgumentError("common divisors require one selected branch"))
