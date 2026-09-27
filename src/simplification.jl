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
    @rule(~x^~z/(~x^~y) => ~x^(~z-~y))
    @rule((~x^~y)^~z => ~x^(~y*~z))
    @rule(sqrt((~x)^2) => abs(~x))
]

absolute_value_rules = [
    @rule(abs(~x*~y) => abs(~x)*abs(~y))
    @rule(abs((~x)^2) => (~x)^2)
    @rule(abs((~x)^(2*~n)) => (~x)^(2*~n))
    @rule((abs(~x))^2 => (~x)^2)
    @rule((abs(~x))^(2*~n) => (~x)^(2*~n))
    @rule((abs(~x::is_pos_param)))
]


#helpers for divide_common
function _bound_sign(expr)
    simplified = simplify(expr)
    literal = SymbolicUtils.unwrap_const(Symbolics.unwrap(simplified))
    literal isa Real || return (sign=get_sign(simplified), iszero=false)
    sign = literal > 0 ? positive : literal < 0 ? negative : undetermined
    return (sign=sign, iszero=isequal(literal, 0))
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
    relation = Symbolics.unwrap(constraint)
    op = Symbolics.operation(relation)
    op in ((<), (≤), (>), (≥)) || return nothing
    lhs, rhs = SymbolicUtils.arguments(relation)
    isequal(rhs, iv) || return (lhs, rhs, op)
    return (rhs, lhs, _reverse_relation(op))
end

function _relation_sign(constraint, iv)
    operands = _relation_operands(constraint, iv)
    operands === nothing && return undetermined
    lhs, rhs, op = operands
    isequal(lhs, iv) || return undetermined
    _contains_equal(Symbolics.get_variables(rhs), iv) && return undetermined
    bound = _bound_sign(rhs)
    return _sign_from_bound(op, bound.sign, bound.iszero)
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
    return isequal(SymbolicUtils.unwrap_const(Symbolics.unwrap(zero_constraint)), false)
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
    return any(constraint -> _zero_excluded_by_relation(constraint, iv), constraints)
end

function iv_divisibility(iv, sys)
    u_iv = unwrap(iv)
    divisibility = Symbolics.getmetadata(u_iv, VarDivisibility, nothing)
    divisibility !== nothing && return divisibility
    for (key, constraints) in sys.domain_constraints
        _contains_equal(_key_variables(key), iv) || continue
        inferred_sign = _infer_variable_sign(constraints, u_iv)
        inferred_sign === nothing ||
            setmetadata(u_iv, VariableSign, inferred_sign)
        _constraints_exclude_zero(constraints, u_iv) || continue
        setmetadata(u_iv, VarDivisibility, divisible)
        return divisible
    end
    if anywhere_in_domain([iv ≤ 0, iv ≥ 0], sys.domain_constraints, true, sys.ivs)
        iv = setmetadata(u_iv, VarDivisibility, haszero)
        return haszero
    end
    iv = setmetadata(u_iv, VarDivisibility, divisible)
    return divisible
end

function _can_divide_by(singlet, sys::DiffEqSystem)
    if SymbolicUtils.istree(singlet) && !_contains_equal(sys.dvs, singlet)
        return (false, sys)
    end
    if singlet isa Number
        if singlet == 0
            #terms with 0 should be automatically removed with Symbolics.simplify. this is to catch if somehow that didn't happen
            throw(DivideError("tried to divide by zero, system bug"))
        end
        return (true, sys)
    elseif _contains_equal(sys.ivs, singlet)
        divisibility = iv_divisibility(singlet)
        if divisibility == haszero
            return (false, sys)
        end
        return (true, sys)
    elseif _contains_equal(sys.ps, singlet)
        return (true, sys)
    elseif SymbolicUtils.istree(singlet) && _contains_equal(sys.dvs, SymbolicUtils.operation(singlet))
        new_solution = singlet ~ 0
        _push_unique(sys.trivial_sols, new_solution)
        return (true, sys)
    end
    # handles things like derivatives of dvs, since their operator is Differential
    return (false, sys)
end

function common_divisors(expr, sys::DiffEqSystem)
    if expr===nothing
        throw(IOError("input expression cannot be empty"))
    end

    expanded_expr = expand(expand_derivatives(expr))
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

    return shared_factors
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
