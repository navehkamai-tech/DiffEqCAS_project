
const cache_size = Ref{Int64}(1024)

global cache = LRU{Any,Any}(maxsize=cache_size[])

@enum SignState positive negative iszero either undetermined

@enum DivisState divisible haszero undetermined

"""
    ConstraintEvidence

Internal result for the factor zero-set pipeline.  The public decision is
`bound`; `divisibility` and `sign` make numerical decisions inspectable and give
later stages a place to return their proof object.
"""
struct ConstraintEvidence
    bound::IntervalArithmetic.Interval
    divisibility::DivisState
    sign::SignState
end

# NOTE on names: a "factor" in this file is a multiplicative factor of an
# equation.  A `DomBlock` is a factor of the *domain*; the variables below
# named `dfactor` / fields named `factors` of `EvidenceDomain` are those.

"""
    EvidenceDomain

The part of a leaf's domain that bears on one expression: only the domain
factors that share a variable with it.  Every other factor is irrelevant to the
expression and is never looked at.

`key` identifies those factors by content (variables and constraint
expressions; no Ids, no cached pavings).  Cache entries keyed on it stay valid
exactly as long as the relevant constraints are unchanged and need no explicit
invalidation.  The sub-domain itself is built on demand, since most queries are
settled by interval arithmetic before any feasibility check.
"""
mutable struct EvidenceDomain
    source::SymDomain
    factors::Vector{DomBlock}
    key::Any
    sub::Union{Nothing,SymDomain}
end

function _evidence_domain(sys::DESys, expr)
    expr_variables = Symbolics.get_variables(Symbolics.unwrap(expr))
    domain = sys.domain
    relevant = DomBlock[
        f for f in domain.factors if any(v -> _contains_equal(f.variables, v), expr_variables)]
    return EvidenceDomain(domain, relevant, factors_content_key(domain, relevant), nothing)
end

function _ctx_domain!(ctx::EvidenceDomain)
    ctx.sub === nothing && (ctx.sub = subdomain(ctx.source, ctx.factors))
    return ctx.sub
end

function factor_evidence(factor, sys::DESys)
    ctx = _evidence_domain(sys, factor)
    key = (:constraint_evidence, Symbolics.unwrap(factor), ctx.key)

    haskey(cache, key) && return cache[key]

    result = _factor_evidence_uncached(factor, sys, ctx)
    cache[key] = result

    return result
end

factor_sign(factor, sys::DESys) = factor_evidence(factor, sys).sign

factor_sign(factor, sys::DETree) =
    length(sys.branches) == 1 ?
    factor_sign(factor, only(sys.branches)) :
    throw(ArgumentError("factor sign requires one selected branch"))

factor_divisibility(factor, sys::DESys) = factor_evidence(factor, sys).divisibility

factor_divisibility(factor, sys::DETree) =
    length(sys.branches) == 1 ?
    factor_divisibility(factor, only(sys.branches)) :
    throw(ArgumentError("factor divisibility requires one selected branch"))


function _factor_evidence_uncached(factor, sys::DESys, ctx::EvidenceDomain)
    if _contains_equal(sys.ps, factor)
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, undetermined)
    end

    # Stage 1: Prime the global cache with exact bounds for independent variables
    _prime_domain_bounds!(ctx)

    # Stage 2: Fast structural and interval arithmetic
    best_evidence = _infer_tree(factor, ctx)

    if best_evidence.divisibility !== undetermined || isempty(ctx.factors)
        return best_evidence
    end

    for stage in (
        _affine_factor_evidence,
        _centered_factor_evidence,
        _sturm_factor_evidence,
        _paved_factor_evidence,
    )
        result = stage(factor, ctx, sys)

        if result !== nothing
            new_bound = best_evidence.bound ∩ result.bound
            new_sign = result.sign !== undetermined ? result.sign : best_evidence.sign
            new_divis = result.divisibility !== undetermined ? result.divisibility : best_evidence.divisibility

            if new_divis === undetermined && (new_sign in (positive, negative) || 0 ∉ new_bound)
                new_divis = divisible
            end

            best_evidence = ConstraintEvidence(new_bound, new_divis, new_sign)
            best_evidence.divisibility !== undetermined && return best_evidence
        end
    end

    return best_evidence
end

# beginning of the pipeline - always called first

"""
Natural interval evaluation over each relevant domain factor.

obtain the factor boxes without invoking paving,
evaluate `factor` with `_domain_interval_value` (extended for all supported
registered functions), and return:
* `divisible` only when every feasible box excludes zero;
* `haszero` only with a certified feasible zero;
* leave `undetermined` when interval dependency leaves the result unresolved.
"""
function _prime_domain_bounds!(ctx::EvidenceDomain)
    for dfactor in ctx.factors
        ivs = collect(dfactor.variables)
        bounds = Dict(iv => IntervalArithmetic.Interval(-Inf, Inf) for iv in ivs)

        for constraint in constraints_of(ctx.source, dfactor)
            op = _get_relation(constraint.relation)
            op === (!=) && continue

            expr = Symbolics.unwrap(constraint.relation.residual)
            expr_vars = Symbolics.get_variables(expr)
            constraint_ivs = [iv for iv in ivs if _contains_equal(expr_vars, iv)]

            length(constraint_ivs) == 1 || continue
            iv = only(constraint_ivs)

            is_feasible = _update_affine_bound!(bounds, expr, iv, op)
            is_feasible || throw(DomainError(iv, "Infeasible domain constraint detected."))
        end

        # Inject the bounds into the global cache to prime _infer_tree
        for (iv, bound) in bounds
            cache_key = (:constraint_evidence, Symbolics.unwrap(iv), ctx.key)
            sign_state = bound.hi < 0 ? negative : (bound.lo > 0 ? positive : (bound.lo == 0 && bound.hi == 0 ? iszero : undetermined))
            divis_state = (sign_state in (positive, negative) || 0 ∉ bound) ? divisible : (sign_state === iszero ? haszero : undetermined)
            cache[cache_key] = ConstraintEvidence(bound, divis_state, sign_state)
        end
    end
end

function _infer_tree(expr, ctx::EvidenceDomain)
    expr = simplify(expr)
    expr==0 && return ConstraintEvidence(interval(0, 0), haszero, iszero)

    # 1. Check existing cache
    key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
    if haskey(cache, key) && cache[key].sign !== undetermined
        return cache[key]
    end

    # 2. Check exact literals
    literal = SU.unwrap_const(Symbolics.unwrap(expr))
    if literal isa Real
        return _evidence_from_literal(literal)
    end

    # 3. Recursive subexpression inference
    simplified = simplify(expr)
    SU.iscall(simplified) || return ConstraintEvidence(interval(-Inf, Inf), undetermined, undetermined) #[cite: 1]

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

    # 2. Structural deduction (retaining your existing logic as a fallback)
    struct_sign = _structural_sign(op, children)

    # 3. Reconcile numeric bounds with structural deduction
    final_sign = _reconcile_sign(new_bound, struct_sign)
    final_divis = _reconcile_divisibility(new_bound, final_sign)

    return ConstraintEvidence(new_bound, final_divis, final_sign)
end

# affine checks
function _update_affine_bound!(bounds, expr, iv, op)
    affine = _affine_coefficients(expr, Symbolics.unwrap(iv))
    affine === nothing && return true # true indicates the domain remains feasible

    coeff = SU.unwrap_const(affine[1])
    intercept = SU.unwrap_const(affine[2])
    (coeff isa Real && intercept isa Real) || return true

    val = -intercept / coeff
    effective_op = coeff > 0 ? op : _reverse_relation(op)

    new_bound = if effective_op in ((<), (≤))
        Interval(-Inf, val)
    elseif effective_op in ((>), (≥))
        Interval(val, Inf)
    else
        Interval(val, val) # effective_op === (==)
    end

    bounds[iv] = bounds[iv] ∩ new_bound

    # Return false if the updated interval is empty, signaling an infeasible domain
    return !isempty(bounds[iv])
end

function _affine_coefficients(expr, iv)
    isequal(expr, iv) && return (one(expr), zero(expr))
    _contains_equal(Symbolics.get_variables(expr), iv) || return (zero(expr), expr)
    SU.iscall(expr) || return nothing
    op = SU.operation(expr)
    args = SU.arguments(expr)
    if op === (+)
        parts = [_affine_coefficients(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        return (sum(part[1] for part in parts), sum(part[2] for part in parts))
    elseif op === (-)
        if length(args) == 1
            part = _affine_coefficients(args[1], iv)
            isnothing(part) && return nothing
            return (-part[1], -part[2])
        end
        length(args) == 2 || return nothing
        lhs, rhs = _affine_coefficients.(args, Ref(iv))
        (isnothing(lhs) || isnothing(rhs)) && return nothing
        return (lhs[1] - rhs[1], lhs[2] - rhs[2])
    elseif op === (*)
        parts = [_affine_coefficients(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        variable_parts = filter(part -> !isequal(part[1], 0), parts)
        length(variable_parts) > 1 && return nothing
        constant = prod(part[2] for part in parts if isequal(part[1], 0))
        isempty(variable_parts) && return (zero(expr), constant)
        variable = only(variable_parts)
        return (variable[1] * constant, variable[2] * constant)
    elseif op === (/)
        length(args) == 2 || return nothing
        lhs, rhs = _affine_coefficients.(args, Ref(iv))
        (isnothing(lhs) || isnothing(rhs)) && return nothing
        rhs[1] == 0 && return (lhs[1] / rhs[2], lhs[2] / rhs[2])
    end
    return nothing
end

# Feasibility probes.  The sign of `expr` over a domain is probed with
# non-strict inequalities; the zero set {expr = 0} is {expr ≤ 0} ∩ {expr ≥ 0},
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

Classify a factor that is affine in one independent variable.  The domain
solver already handles linear inequalities and equalities, so asking it
whether the affine zero set is feasible gives a conservative, reusable proof
without factoring the expression again.  Only the domain factor containing that
variable is consulted.
"""
function _affine_factor_evidence(factor, ctx::EvidenceDomain, sys::DESys)
    factor_variables = Symbolics.get_variables(Symbolics.unwrap(factor))
    independent_variables = [iv for iv in sys.ivs if _contains_equal(factor_variables, iv)]
    length(independent_variables) == 1 || return nothing
    iv = only(independent_variables)

    coefficients = _affine_coefficients(Symbolics.unwrap(factor), Symbolics.unwrap(iv))
    coefficients === nothing && return nothing

    coeff_evidence = _infer_tree(coefficients[1], ctx)
    coeff_evidence.sign in (positive, negative) || return nothing

    dfactor = factor_of(ctx.source, iv)
    dfactor === nothing && return nothing
    return _probe_evidence(factor, subdomain(ctx.source, [dfactor]))
end
# TODO: Extend affine zero-set reasoning to factors involving multiple
# independent variables. Require all variables to belong to one domain
# component, verify that `_affine_coefficients` generalizes across every
# variable, and query `constraints_satisfiable([factor == 0], component,
# true)`. Return `haszero` for a certified feasible zero, `divisible` for a
# certified exclusion, and `undetermined` whenever the solver is unresolved.


# rest of _factor_evidence_uncached pipeline components
"""
Centered/mean-value interval form.

TODO (implementation): use the midpoint and interval extensions of the
gradient to tighten each component enclosure.  This is applicable to
transcendental expressions as well as polynomials and must remain conservative
when a derivative extension is unavailable.
"""
function _centered_factor_evidence(factor, ctx::EvidenceDomain, sys::DESys)
    return nothing # PSEUDOCODE: replace with centered/mean-value forms.
end

"""
Univariate polynomial specialization.

TODO (implementation): call Sturm root isolation only when `factor` is
provably a polynomial in exactly one independent variable.  Treating
`sin(x)`/`exp(x)` as polynomial atoms is not sufficient for this stage.
"""
function _sturm_factor_evidence(factor, ctx::EvidenceDomain, sys::DESys)
    return nothing # PSEUDOCODE: replace with certified Sturm isolation.
end

"""
Final general fallback.

Formulates `domain ∧ factor relation 0` and evaluates feasibility via branch-and-prune paving. 
An unresolved boundary box produces `undetermined`, never `divisible`.
"""
function _paved_factor_evidence(factor, ctx::EvidenceDomain, sys::DESys)
    # The relevant domain factors form a product and `factor` couples them, so
    # the question is asked once, jointly, over exactly those factors.  Pavings
    # of unrelated factors are never computed.
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
        return c.sign === positive ? negative : c.sign === negative ? positive : undetermined
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
    bound.hi < 0 && return negative
    bound.lo > 0 && return positive
    bound.lo == 0 && bound.hi == 0 && return iszero

    # Fallback to structural sign if the interval crosses zero (or is NaN/Inf)
    return struct_sign
end

function _reconcile_divisibility(bound, final_sign)
    # Divisible if strictly positive/negative structurally, or if 0 is outside the interval
    if final_sign in (positive, negative) || 0 ∉ bound
        return divisible
    elseif final_sign === iszero || (bound.lo == 0 && bound.hi == 0)
        return haszero
    end
    return undetermined
end

function _reverse_relation(op)
    op === (<) && return (>)
    op === (≤) && return (≥)
    op === (>) && return (<)
    op === (≥) && return (≤)
end

function _combined_constraint_sign(found_positive, found_negative)
    found_positive == found_negative && return either
    return found_positive ? positive : negative
end

# Content key of the relevant domain factors (see `factors_content_key`): valid
# exactly as long as those constraints are, so no invalidation step is needed.
_divisibility_cache_key(factor, ctx::EvidenceDomain) =
    (:divisibility, Symbolics.unwrap(factor), ctx.key)

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
