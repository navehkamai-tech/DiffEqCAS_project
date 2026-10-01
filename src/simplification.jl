#rules for stuff simplify doesn't handle well
#need to add domain checks
exponential_logarithmic_rules = [
    @rule(exp(~x)/exp(~y) => exp(~x - ~y)),
    @rule(exp(log(~x)) => ~x),
    @rule(log(exp(~x)) => ~x),
    @rule(log(~x)+log(~y) => log(~x * ~y)),
    @rule(log(~x)-log(~y) => log(~x/~y)),
    @rule(~n*log(~x) => log(~x^~n)),
]
power_rules = [
    @rule((~x)^(~z)/(~x)^(~y) => (~x)^(~z-~y)),
    @rule(((~x)^(~y))^(~z) => (~x)^(~y*~z)),
    @rule(sqrt((~x)^2) => abs(~x)),
]
absolute_value_rules = [
    @rule(abs(~x*~y) => abs(~x)*abs(~y)),
    @rule(abs((~x)^2) => (~x)^2),
    @rule(abs((~x)^(2*~n)) => (~x)^(2*~n)),
    @rule((abs(~x))^2 => (~x)^2),
    @rule((abs(~x)^(2*~n)) => (~x)^(2*~n)),
    @rule(abs(~x::is_pos_param) => ~x),
]


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

function singlet_divisibility(singlet, sys::DiffEqSystem)
    if singlet isa Number
        if singlet != 0
            return true
        end
        return false
    elseif _contains_equal(sys.ps, singlet)
        return true
    elseif _contains_equal(sys.ivs, singlet)
        return ivs_polynomial_divisibility(singlet, sys)
    end
    return false
end

function _can_divide_by(expr::Symbolics.Num, sys::DiffEqSystem)
    expr_u = unwrap(expr)
    if !SymbolicUtils.istree(expr_u)
        return singlet_divisibility(expr_u)
    elseif _has_depvar_or_diff(expr)
        return false
    end



    # handles things like derivatives of dvs, since their operator is Differential
    return false, sys
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
