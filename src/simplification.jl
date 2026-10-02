
exponential_logarithmic_rules = [
    @rule(~x/exp(~y) => ~x*exp(-~y)),
    @rule(exp(~x)^~n => exp(~x*~n)),
    @rule(exp(log(~x::is_positive)) => ~x),
    @rule(log(exp(~x::is_real)) => ~x),
    @rule(log(~x)+log(~y) => log(~x * ~y)),
    @rule(log(~x)-log(~y) => log(~x/~y)),
    @rule(~n*log(~x) => log(~x^~n)),
]
power_rules = [
    @rule(~z/(~x::is_divisible)^(~y) => ~z*~x^(-~y)),
    @rule(((~x::is_positive)^(~y))^(~z) => (~x)^(~y*~z)),
    @rule(sqrt((~x::is_real)^2) => abs(~x)),
]
absolute_value_rules = [
    @rule(abs(~x*~y) => abs(~x)*abs(~y)),
    @rule(abs((~x::is_real)^2) => (~x)^2),
    @rule(abs((~x::is_real)^(2*~n)) => (~x)^(2*~n)),
    @rule((abs(~x))^2 => (~x)^2),
    @rule((abs(~x)^(2*~n)) => (~x)^(2*~n)),
    @rule(abs(~x::is_positive) => ~x),
    @rule(abs(~x::is_negative) => -~x),
]
trigonometric_rules = [
    @rule(sin(~x+2*π) => sin(~x)),
    @rule(sin(~x+2*π*~n::is_integer) => sin(~x)),
    @rule(cos(~x+2*π) => cos(~x)),
    @rule(cos(~x+2*π*~n::is_integer) => cos(~x)),
    @rule(sin(~x)^2 => 1//2-1//2*cos(2*~x)),
    @rule(cos(~x)^2 => 1//2+1//2*cos(2*~x)),
    @rule(tan(~x) => sin(~x)/cos(~x))

    #what more? i need addition to multiplication or the inverse, but which?
    #in general there are so many trig identities, it's difficult to know which direction is best for them
]
# add hyperbolic trig rules if wanted

#it's vital to normalize the arguments of these kinds of functions - otherwise they can fail to simplify properly
#these being exp, log, trigonometric functions
#copilot recommends applying simplify directly to the argument

#is_positive needs to be upgraded to handle arbitrary expressions and possibly complex number inputs (return false if complex of course)

#need to define constants like π as symbolics so that they do not become floating points
#it might become necessary to move the simplifier rules into the rewriter generating function

#would be good to treat differentials as operators so they can be factored as polynomials. don't know how I would do that

#I also need to handle limits, not just integrals, for my boundary conditions.

#helpers for divide_common
function _bound_sign(expr)
    literal = SymbolicUtils.unwrap_const(Symbolics.unwrap(expr))
    literal isa Real && return (
        sign=literal > 0 ? positive : literal < 0 ? negative : undetermined,
        iszero=isequal(literal, 0),
    )
    known_sign = get_sign(expr)
    known_sign !== undetermined && return (sign=known_sign, iszero=false)
    simplified = simplify(expr)
    literal = SymbolicUtils.unwrap_const(Symbolics.unwrap(simplified))
    literal isa Real && return (
        sign=literal > 0 ? positive : literal < 0 ? negative : undetermined,
        iszero=isequal(literal, 0),
    )

    # Keep this deliberately conservative: proving every term has the same
    # sign is useful for parameter-dependent bounds without guessing unknowns.
    if SymbolicUtils.istree(simplified)
        op = SymbolicUtils.operation(simplified)
        args = SymbolicUtils.arguments(simplified)
        if op === (+)
            signs = _bound_sign.(args)
            if all(value -> value.sign === positive, signs)
                return (sign=positive, iszero=false)
            elseif all(value -> value.sign === negative, signs)
                return (sign=negative, iszero=false)
            elseif all(value -> value.iszero, signs)
                return (sign=undetermined, iszero=true)
            end
        elseif op === (-) && length(args) == 1
            value = _bound_sign(args[1])
            return (sign=value.sign === positive ? negative :
                         value.sign === negative ? positive : undetermined,
                iszero=value.iszero)
        elseif op === (*)
            signs = _bound_sign.(args)
            any(value -> value.iszero, signs) &&
                return (sign=undetermined, iszero=true)
            nonzero = all(value -> value.sign in (positive, negative), signs)
            if nonzero
                negative_factors = count(value -> value.sign === negative, signs)
                return (sign=isodd(negative_factors) ? negative : positive,
                    iszero=false)
            end
        elseif op === (/) && length(args) == 2
            numerator, denominator = _bound_sign.(args)
            if denominator.sign in (positive, negative) && numerator.sign in (positive, negative)
                sign = numerator.sign === denominator.sign ? positive : negative
                return (sign=sign, iszero=false)
            elseif numerator.iszero && denominator.sign in (positive, negative)
                return (sign=undetermined, iszero=true)
            end
        end
    end

    return (sign=get_sign(simplified), iszero=false)
end

function _affine_coefficients(expr, iv)
    isequal(expr, iv) && return (one(expr), zero(expr))
    _contains_equal(Symbolics.get_variables(expr), iv) || return (zero(expr), expr)
    SymbolicUtils.istree(expr) || return nothing
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

function _reverse_relation(op)
    op === (<) && return (>)
    op === (≤) && return (≥)
    op === (>) && return (<)
    op === (≥) && return (≤)
end

function _sign_from_bound(op, bound_sign, bound_iszero)
    lower_bound = op in ((>), (≥))
    upper_bound = op in ((<), (≤))
    lower_bound || upper_bound || return undetermined
    strict_bound = op === (>) || op === (<)
    bound_excludes_zero = strict_bound && bound_iszero
    if lower_bound
        return bound_sign === positive || bound_excludes_zero ? positive : either
    end
    return bound_sign === negative || bound_excludes_zero ? negative : either
end

function _relation_operands(constraint, iv)
    # Canonicalize simple affine relations locally instead of rewriting the
    # domain, so callers retain the constraints they supplied.
    relation = Symbolics.unwrap(constraint)
    op = Symbolics.operation(relation)
    op in ((<), (≤), (>), (≥)) || return nothing
    lhs, rhs = SymbolicUtils.arguments(relation)
    isequal(rhs, iv) || return (lhs, rhs, op)
    return (rhs, lhs, _reverse_relation(op))
end

function _relation_sign(constraint, iv)
    operands = _relation_operands(constraint, iv)
    if operands !== nothing
        lhs, rhs, op = operands
        if isequal(lhs, iv) && !_contains_equal(Symbolics.get_variables(rhs), iv)
            bound = _bound_sign(rhs)
            return _sign_from_bound(op, bound.sign, bound.iszero)
        end
    end

    relation = Symbolics.unwrap(constraint)
    op = Symbolics.operation(relation)
    op in ((<), (≤), (>), (≥)) || return undetermined
    lhs, rhs = SymbolicUtils.arguments(relation)
    affine = _affine_coefficients(lhs - rhs, iv)
    affine === nothing && return undetermined
    coefficient, intercept = affine
    isequal(coefficient, 0) && return undetermined
    coefficient_sign = _bound_sign(coefficient).sign
    coefficient_sign in (positive, negative) || return undetermined

    bound = _bound_sign(-intercept / coefficient)
    relation_op = coefficient_sign === positive ? op : _reverse_relation(op)
    return _sign_from_bound(relation_op, bound.sign, bound.iszero)
end

function _combined_constraint_sign(found_positive, found_negative)
    found_positive == found_negative && return either
    return found_positive ? positive : negative
end

function _zero_excluded_by_relation(constraint, iv)
    u_constraint = Symbolics.unwrap(constraint)
    variables = Symbolics.get_variables(u_constraint)
    _contains_equal(variables, iv) || return false
    op = Symbolics.operation(u_constraint)
    op in ((<), (≤), (>), (≥), (==), (!=)) || return false
    zero_constraint = simplify(substitute(u_constraint, iv => 0))
    isequal(SymbolicUtils.unwrap_const(Symbolics.unwrap(zero_constraint)), false) &&
        return true

    # A positive power of the independent variable is zero at the origin.
    # Handle symbolic positive exponents when substitution cannot evaluate
    # `0^n` directly, while leaving unknown or nonpositive exponents alone.
    op in ((<), (≤), (>), (≥)) || return false
    lhs, rhs = SymbolicUtils.arguments(u_constraint)
    power = nothing
    other = nothing
    for (candidate, remainder) in ((lhs, rhs), (rhs, lhs))
        if SymbolicUtils.istree(candidate) &&
            SymbolicUtils.operation(candidate) === (^)
            base, exponent = SymbolicUtils.arguments(candidate)
            if isequal(base, iv)
                power = (candidate, exponent)
                other = remainder
                break
            end
        end
    end
    power === nothing && return false
    isequal(SymbolicUtils.unwrap_const(Symbolics.unwrap(other)), 0) || return false
    _, exponent = power
    exponent_sign = _bound_sign(exponent).sign
    exponent_sign === positive || return false
    op in ((<), (>)) || return false
    return true
end

function _infer_variable_sign(constraints, iv)
    found_positive = false
    found_negative = false
    for constraint in constraints
        sign = _relation_sign(constraint, iv)
        found_positive |= sign === positive
        found_negative |= sign === negative
    end
    no_sign_evidence = !found_positive && !found_negative
    no_sign_evidence && return nothing
    return _combined_constraint_sign(found_positive, found_negative)
end

function _constraints_exclude_zero(constraints, iv)
    return any(constraints) do constraint
        _relation_sign(constraint, iv) in (positive, negative) ||
            _zero_excluded_by_relation(constraint, iv)
    end
end

"""
    DivisibilityEvidence

Internal result for the factor zero-set pipeline.  The public decision is
`status`; `stage` and `detail` make numerical decisions inspectable and give
later stages a place to return their proof object.
"""
struct DivisibilityEvidence
    status::DivisState
    stage::Symbol
    detail::Any
end

_proven(status::DivisState, stage, detail=nothing) =
    DivisibilityEvidence(status, stage, detail)

# Domain components are kept separate because a factor may be nonzero on one
# connected component and zero on another.
function _divisibility_components(sys::DiffEqSystem, factor)
    factor_variables = Set(Symbolics.get_variables(Symbolics.unwrap(factor)))
    return [
        (key, constraints) for (key, constraints) in sys.domain
                               if !isempty(intersect(factor_variables, Set(_key_variables(key))))
    ]
end

function _divisibility_cache_key(factor, components)
    # TODO: Replace this structural tuple with the canonical expression/domain
    # key used by the global cache once cache invalidation is finalized.
    (:divisibility, Symbolics.unwrap(factor), components)
end

"""
Cheap exact facts that apply to any already-factored expression.

This is intentionally not another factorization pass.  The caller has
factored the differential equation already; this stage only recognizes facts
such as literal zero/nonzero and exact simplification.
"""
function _exact_factor_divisibility(factor, sys::DiffEqSystem)
    value = SymbolicUtils.unwrap_const(Symbolics.unwrap(factor))
    value isa Number &&
        return _proven(value == 0 ? haszero : divisible, :exact, value)

    simplified = simplify(factor)
    simplified_value = SymbolicUtils.unwrap_const(Symbolics.unwrap(simplified))
    simplified_value isa Number &&
        return _proven(simplified_value == 0 ? haszero : divisible,
            :exact_simplification, simplified_value)

    return nothing
end

function _variable_factor_divisibility(factor, components)
    # This is the retained fast specialization for a leaf independent
    # variable. Its sign and relation helpers are no longer a separate
    # divisibility pipeline; they are one stage of factor_divisibility.
    for (key, constraints) in components
        _contains_equal(_key_variables(key), factor) || continue
        inferred_sign = _infer_variable_sign(constraints, factor)
        inferred_sign === nothing ||
            setmetadata(Symbolics.unwrap(factor), VarSign, inferred_sign)
        _constraints_exclude_zero(constraints, factor) &&
            return _proven(divisible, :variable_constraints)

        component = [key => constraints]
        if constraints_satisfiable([factor ≤ 0, factor ≥ 0], component, true)
            return _proven(haszero, :variable_zero_feasibility)
        end

        # TODO: This is the old behavior and is only sound when the
        # satisfiability result is certified. Once constraints_satisfiable
        # exposes an unresolved state, return `undetermined` for that state.
        return _proven(divisible, :variable_domain_exclusion)
    end
    return _proven(divisible, :independent_variable)
end

"""
Cheap domain reasoning for a general factor.

The old affine/sign helpers are deliberately retained behind the variable
specialization below. They should be generalized in two directions:

* affine factors: reuse `_affine_coefficients` after normalizing the factor;
* monotone/factored expressions: combine factor sign facts without factoring
  the already-factored differential equation again.

The arbitrary-expression case needs zero-set reasoning, not merely a renamed
variable substitution.
"""
function _cheap_factor_divisibility(factor, components, sys::DiffEqSystem)
    _contains_equal(sys.ps, factor) &&
        return _proven(divisible, :parameter)

    if _contains_equal(sys.ivs, factor) &&
        !SymbolicUtils.istree(Symbolics.unwrap(factor))
        return _variable_factor_divisibility(factor, components)
    end

    # TODO: Add `_affine_factor_divisibility` here. It should use the existing
    # affine coefficient/sign helpers for factors such as `a*x + b`, then
    # certify whether the affine zero set intersects each domain component.
    #
    # TODO: Add a generic symbolic zero-set stage here:
    # PSEUDOCODE:
    #   for constraint in component constraints
    #       classify constraint under factor == 0
    #       if contradiction is certified, return divisible
    #       if a feasible zero is certified, return haszero
    #   end
    #   return nothing
    return nothing
end

"""
Natural interval evaluation over each domain component.

TODO (implementation): obtain the component boxes without invoking paving,
evaluate `factor` with `_domain_interval_value` (extended for all supported
registered functions), and return:
* `divisible` only when every feasible box excludes zero;
* `haszero` only with a certified feasible zero;
* `nothing` when interval dependency leaves the result unresolved.
"""
function _interval_factor_divisibility(factor, components, sys::DiffEqSystem)
    return nothing # PSEUDOCODE: replace with interval evaluation.
end

"""
Centered/mean-value interval form.

TODO (implementation): use the midpoint and interval extensions of the
gradient to tighten each component enclosure.  This is applicable to
transcendental expressions as well as polynomials and must remain conservative
when a derivative extension is unavailable.
"""
function _centered_factor_divisibility(factor, components, sys::DiffEqSystem)
    return nothing # PSEUDOCODE: replace with centered/mean-value forms.
end

"""
Univariate polynomial specialization.

TODO (implementation): call Sturm root isolation only when `factor` is
provably a polynomial in exactly one independent variable.  Treating
`sin(x)`/`exp(x)` as polynomial atoms is not sufficient for this stage.
"""
function _sturm_factor_divisibility(factor, components, sys::DiffEqSystem)
    return nothing # PSEUDOCODE: replace with certified Sturm isolation.
end

"""
Final general fallback.

TODO (implementation): formulate `domain ∧ factor == 0` and call
`_pave_constraints`/`f_pave_constraints`.  An unresolved boundary box must
produce `undetermined`, never `divisible`.
"""
function _paved_factor_divisibility(factor, components, sys::DiffEqSystem)
    return nothing # PSEUDOCODE: replace with zero-set paving.
end

function _factor_divisibility_uncached(factor, sys::DiffEqSystem)
    exact = _exact_factor_divisibility(factor, sys)
    exact !== nothing && return exact

    _contains_equal(sys.ps, factor) &&
        return _proven(divisible, :parameter)

    components = _divisibility_components(sys, factor)
    isempty(components) &&
        return _proven(undetermined, :parameter_or_domain_independent)

    # Each stage returns nothing when it cannot prove a result.  This ordering
    # keeps cheap heuristics ahead of increasingly expensive numerical work.
    for stage in (
        _cheap_factor_divisibility,
        _interval_factor_divisibility,
        _centered_factor_divisibility,
        _sturm_factor_divisibility,
        _paved_factor_divisibility,
    )
        result = stage(factor, components, sys)
        result !== nothing && return result
    end

    return _proven(undetermined, :unresolved)
end

function factor_divisibility(factor, sys::DiffEqSystem)
    components = _divisibility_components(sys, factor)
    key = _divisibility_cache_key(factor, components)
    haskey(cache, key) && return cache[key]
    result = _factor_divisibility_uncached(factor, sys)
    cache[key] = result
    return result
end

function _has_depvar_or_diff(expr, sys::DiffEqSystem)
    any(variable -> _contains_equal(sys.dvs, variable),
        Symbolics.get_variables(Symbolics.unwrap(expr))) && return true

    expression = Symbolics.unwrap(expr)
    SymbolicUtils.istree(expression) || return false
    Symbolics.operation(expression) isa Differential && return true
    any(argument -> _has_depvar_or_diff(argument, sys),
        SymbolicUtils.arguments(expression))
end

function _can_divide_by(expr::Symbolics.Num, sys::DiffEqSystem)
    _contains_equal(sys.dvs, expr) && return false
    _has_depvar_or_diff(expr, sys) && return false

    return factor_divisibility(expr, sys).status === divisible
end

function common_divisors(expr, sys::DiffEqSystem)
    if expr===nothing
        throw(IOError("input expression cannot be empty"))
    end

    simplified_expr = expand(expand_derivatives(expr))
    #process it more to simplify things like exponentials
    #after that we're left with simplified_expr
    expr_unwrapped = unwrap(simplified_expr)
    # Get a flat list of every term separated by a + or -
    addends = terms(expr_unwrapped)

    if length(addends) == 1
        return divisible_singlets(expr)
    end

    # Break the first addend into its multiplicative components to use as a baseline
    shared_numerator_factors = factors(denominator(addends[1]))
    shared_denominator_factors = factors(numerator(addends[1]))
    # Intersect factors across all other addends
    for i in 2:length(addends)
        num_factors = factors(numerator(addends[i]))
        # Keep only the factors that exist in BOTH the baseline and the current term
        filter!(f -> f in num_factors, shared_numerator_factors)
        # Early exit if we lose all common factors
        if isempty(shared_numerator_factors)
            break
        end
    end
    #same but for denominator
    for i in 2:length(addends)
        denom_factors = factors(denominator(addends[i]))
        filter!(f -> f in denom_factors, shared_denominator_factors)
        if isempty(shared_denominator_factors)
            break
        end
    end

    return _ordered_unique(vcat(shared_numerator_factors, shared_denominator_factors))
end

# helpers for group_coefficients
function _is_target(e, unwrapped_dvs::Set, dv_ops)
    # If it is a leaf node, check if it matches any dvendent variable directly
    if !SymbolicUtils.istree(e)
        return e in unwrapped_dvs
    end

    op = SymbolicUtils.operation(e)

    # Check if the operation matches any of our base dependent operations
    if any(isequal(op, d_op) for d_op in dv_ops)
        return true
    end

    # Support mixed derivatives by recursively checking arguments
    if op isa Differential
        args = SymbolicUtils.arguments(e)
        return _is_target(args[1], unwrapped_dvs, dv_ops)
    end

    return false
end

function _find_targets!(e, unwrapped_dvs::Set, dv_ops, targets::Set)
    # If we found a target, add it and stop recursing
    if _is_target(e, unwrapped_dvs, dv_ops)
        push!(targets, e)
        return
    end

    # Otherwise, keep digging through the expression tree
    if SymbolicUtils.istree(e)
        for arg in SymbolicUtils.arguments(e)
            _find_targets!(arg, unwrapped_dvs, dv_ops, targets)
        end
    end
end

function _diff_depth(e)
    if !SymbolicUtils.istree(e)
        return 0
    end

    # Increment depth for each Differential operation
    if SymbolicUtils.operation(e) isa Differential
        return 1 + _diff_depth(SymbolicUtils.arguments(e)[1])
    end

    return 0
end

function group_coefficients(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))

    unwrapped_dvs = Set([unwrap(d) for d in dvs])
    dv_ops = [SymbolicUtils.operation(unwrap(d)) for d in dvs]
    targets = Set()

    # Pass the required state into the mutator function
    _find_targets!(expr, unwrapped_dvs, dv_ops, targets)

    # Sort targets safely using the external helper
    sorted_targets = sort(collect(targets), by=_diff_depth, rev=true)

    grouped_expr = 0
    remainder = expr

    for target in sorted_targets
        max_deg = Symbolics.degree(remainder)
        for p in max_deg:-1:1
            target_term = p==1 ? target : target^p
            coeff = simplify(Symbolics.coeff(remainder, target_term))

            if !isequal(coeff, 0)
                grouped_expr += coeff * wrap(target)
                remainder = simplify(remainder - coeff * target_term)
            end

        end
    end

    grouped_expr += simplify(remainder)

    return grouped_expr ~ 0
end
