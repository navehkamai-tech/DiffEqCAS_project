
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

function factor_evidence(factor, sys::DiffEqLeaf)
    components = _evidence_components(sys, factor)
    key = (:constraint_evidence, Symbolics.unwrap(factor), components)

    haskey(cache, key) && return cache[key]

    result = _factor_evidence_uncached(factor, sys, components)
    cache[key] = result

    return result
end

factor_sign(factor, sys::DiffEqLeaf) = factor_evidence(factor, sys).sign

factor_sign(factor, sys::DiffEqSystem) =
    length(sys.branches) == 1 ?
    factor_sign(factor, only(sys.branches)) :
    throw(ArgumentError("factor sign requires one selected branch"))

factor_divisibility(factor, sys::DiffEqLeaf) = factor_evidence(factor, sys).divisibility

factor_divisibility(factor, sys::DiffEqSystem) =
    length(sys.branches) == 1 ?
    factor_divisibility(factor, only(sys.branches)) :
    throw(ArgumentError("factor divisibility requires one selected branch"))


function _factor_evidence_uncached(factor, sys::DiffEqLeaf, components)
    if _contains_equal(sys.ps, factor)
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, undetermined)
    end

    # Stage 1: Prime the global cache with exact bounds for independent variables
    _prime_domain_bounds!(components)

    # Stage 2: Fast structural and interval arithmetic
    best_evidence = _infer_tree(factor, components)

    if best_evidence.divisibility !== undetermined || isempty(components)
        return best_evidence
    end

    for stage in (
        _affine_factor_evidence,
        _centered_factor_evidence,
        _sturm_factor_evidence,
        _paved_factor_evidence,
    )
        result = stage(factor, components, sys)

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
Natural interval evaluation over each domain component.

obtain the component boxes without invoking paving,
evaluate `factor` with `_domain_interval_value` (extended for all supported
registered functions), and return:
* `divisible` only when every feasible box excludes zero;
* `haszero` only with a certified feasible zero;
* leave `undetermined` when interval dependency leaves the result unresolved.
"""
function _prime_domain_bounds!(components)
    for component in components
        key, constraints = component
        ivs = collect(_key_variables(key))
        bounds = Dict(iv => IntervalArithmetic.Interval(-Inf, Inf) for iv in ivs)

        for constraint in constraints
            relation = Symbolics.unwrap(constraint)
            op = Symbolics.operation(relation)
            op in ((<), (≤), (>), (≥), (==)) || continue

            lhs, rhs = SymbolicUtils.arguments(relation)
            expr = lhs - rhs
            expr_vars = Symbolics.get_variables(expr)
            constraint_ivs = [iv for iv in ivs if _contains_equal(expr_vars, iv)]

            length(constraint_ivs) == 1 || continue
            iv = only(constraint_ivs)

            is_feasible = _update_affine_bound!(bounds, expr, iv, op)
            is_feasible || throw(DomainError(iv, "Infeasible domain constraint detected."))
        end

        # Inject the bounds into the global cache to prime _infer_tree
        for (iv, bound) in bounds
            cache_key = (:constraint_evidence, Symbolics.unwrap(iv), components)
            sign_state = bound.hi < 0 ? negative : (bound.lo > 0 ? positive : (bound.lo == 0 && bound.hi == 0 ? iszero : undetermined))
            divis_state = (sign_state in (positive, negative) || 0 ∉ bound) ? divisible : (sign_state === iszero ? haszero : undetermined)
            cache[cache_key] = ConstraintEvidence(bound, divis_state, sign_state)
        end
    end
end

function _infer_tree(expr, components)
    expr = simplify(expr)
    expr==0 && return ConstraintEvidence(interval(0, 0), haszero, iszero)

    # 1. Check existing cache
    key = (:constraint_evidence, Symbolics.unwrap(expr), components)
    if haskey(cache, key) && cache[key].sign !== undetermined
        return cache[key]
    end

    # 2. Check exact literals
    literal = SymbolicUtils.unwrap_const(Symbolics.unwrap(expr))
    if literal isa Real
        return _evidence_from_literal(literal)
    end

    # 3. Recursive subexpression inference
    simplified = simplify(expr)
    SymbolicUtils.iscall(simplified) || return ConstraintEvidence(interval(-Inf, Inf), undetermined, undetermined) #[cite: 1]

    op = SymbolicUtils.operation(simplified)
    args = SymbolicUtils.arguments(simplified)

    # Recurse down. If a leaf is undetermined and not cached, this will bubble up.
    children = [_infer_tree(arg, components) for arg in args]
    result = _combine_child_signs(op, children)

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
    affine = _affine_coefficients(expr, iv)
    affine === nothing && return true # true indicates the domain remains feasible

    coeff = SymbolicUtils.unwrap_const(affine[1])
    intercept = SymbolicUtils.unwrap_const(affine[2])
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
    SymbolicUtils.iscall(expr) || return nothing
    op = SymbolicUtils.operation(expr)
    args = SymbolicUtils.arguments(expr)
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

"""
    _affine_factor_evidence(factor, components, sys)

Classify a factor that is affine in one independent variable.  The domain
solver already handles linear inequalities and equalities, so asking it
whether the affine zero set is feasible gives a conservative, reusable proof
without factoring the expression again.
"""
function _affine_factor_evidence(factor, components, sys::DiffEqLeaf)
    factor_variables = Symbolics.get_variables(Symbolics.unwrap(factor))
    independent_variables = [iv for iv in sys.ivs if _contains_equal(factor_variables, iv)]
    length(independent_variables) == 1 || return nothing
    iv = only(independent_variables)

    coefficients = _affine_coefficients(Symbolics.unwrap(factor), Symbolics.unwrap(iv))
    coefficients === nothing && return nothing

    coeff_evidence = _infer_tree(coefficients[1], components)
    coeff_evidence.sign in (positive, negative) || return nothing

    for component in components
        key, _ = component
        _contains_equal(_key_variables(key), iv) || continue

        can_be_nonpositive = constraints_satisfiable([factor ≤ 0], [component], true)
        if !can_be_nonpositive
            return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, positive)
        end

        can_be_nonnegative = constraints_satisfiable([factor ≥ 0], [component], true)
        if !can_be_nonnegative
            return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, negative)
        end

        can_be_zero = constraints_satisfiable([factor == 0], [component], true)
        if !can_be_zero
            return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, either)
        end

        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), haszero, undetermined)
    end
    return nothing
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
function _centered_factor_divisibility(factor, components, sys::DiffEqLeaf)
    return nothing # PSEUDOCODE: replace with centered/mean-value forms.
end

"""
Univariate polynomial specialization.

TODO (implementation): call Sturm root isolation only when `factor` is
provably a polynomial in exactly one independent variable.  Treating
`sin(x)`/`exp(x)` as polynomial atoms is not sufficient for this stage.
"""
function _sturm_factor_divisibility(factor, components, sys::DiffEqLeaf)
    return nothing # PSEUDOCODE: replace with certified Sturm isolation.
end

"""
Final general fallback.

Formulates `domain ∧ factor relation 0` and evaluates feasibility via branch-and-prune paving. 
An unresolved boundary box produces `undetermined`, never `divisible`.
"""
function _paved_factor_evidence(factor, components, sys::DiffEqLeaf)
    can_be_nonpositive = false
    can_be_nonnegative = false
    can_be_zero = false

    # Evaluate across the union of all relevant topological components
    for component in components
        can_be_nonpositive |= constraints_satisfiable([factor ≤ 0], [component], true)
        can_be_nonnegative |= constraints_satisfiable([factor ≥ 0], [component], true)
        can_be_zero |= constraints_satisfiable([factor == 0], [component], true)
    end

    # If a non-positive value is mathematically impossible across all components
    if !can_be_nonpositive
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, positive)
    end

    # If a non-negative value is mathematically impossible across all components
    if !can_be_nonnegative
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, negative)
    end

    # If it can take both signs but rigorously never touches zero
    if !can_be_zero
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, either)
    end

    # The paving algorithm found a feasible zero or hit its tolerance limit on the boundary
    return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), haszero, undetermined)
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

function _evidence_components(sys::DiffEqLeaf, factor)
    factor_variables = Set(Symbolics.get_variables(Symbolics.unwrap(factor)))
    return [
        key => constraints for (key, constraints) in sys.domain
                               if !isempty(intersect(factor_variables, Set(_key_variables(key))))
    ]
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

function _divisibility_cache_key(factor, components)
    # TODO: Replace this structural tuple with the canonical expression/domain
    # key used by the global cache once cache invalidation is finalized.
    (:divisibility, Symbolics.unwrap(factor), components)
end

function _has_depvar_or_diff(expr, sys::DiffEqLeaf)
    any(variable -> _contains_equal(sys.dvs, variable),
        Symbolics.get_variables(Symbolics.unwrap(expr))) && return true

    expression = Symbolics.unwrap(expr)
    SymbolicUtils.iscall(expression) || return false
    Symbolics.operation(expression) isa Differential && return true
    any(argument -> _has_depvar_or_diff(argument, sys),
        SymbolicUtils.arguments(expression))
end

function _can_divide_by(expr::Symbolics.Num, sys::DiffEqLeaf)
    _contains_equal(sys.dvs, expr) && return false
    _has_depvar_or_diff(expr, sys) && return false

    return factor_divisibility(expr, sys) === divisible
end
