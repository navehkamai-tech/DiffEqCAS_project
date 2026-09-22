
#helpers for divide_common
function get_addends(expr)
    expr = Symbolics.unwrap(expr)
    if SymbolicUtils.istree(expr) && SymbolicUtils.operation(expr) === (+)
        return reduce(vcat, get_addends.(SymbolicUtils.arguments(expr)))
    end
    return [expr]
end

function get_factors(expr)
    expr = Symbolics.unwrap(expr)
    if SymbolicUtils.istree(expr) && SymbolicUtils.operation(expr) === (*)
        return reduce(vcat, get_factors.(SymbolicUtils.arguments(expr)))
    end
    return [expr]
end

function is_divisible(expr, sys::PDESystem)
    if !SymbolicUtils.istree(expr)
        if (isequal(expr, p) for p in sys.ps)
            return true
        elseif (p isa Number) && p != 0
            return true
        elseif (isequal(expr, p) for p in sys.ivs)

        end
    end
end

function extract_and_divide_common(expr)
    expr_unwrapped = Symbolics.unwrap(expr)

    # Get a flat list of every term separated by a + or -
    addends = get_addends(expr_unwrapped)

    if length(addends) <= 1
        return expr
    end

    # Break the first addend into its multiplicative components to use as a baseline
    common_factors = get_factors(addends[1])

    # Intersect factors across all other addends
    for i in 2:length(addends)
        current_factors = get_factors(addends[i])

        # Keep only the factors that exist in BOTH the baseline and the current term
        filter!(f -> f in current_factors, common_factors)

        # Early exit if we lose all common factors
        if isempty(common_factors)
            break
        end
    end

    # Reconstruct the common divisor by multiplying the surviving factors
    if !isempty(common_factors)
        common_divisor = prod(common_factors)

        # needs modification for checking if dividing is allowed, depending on the type of common_divisor and on the domain.
        return simplify(expr_unwrapped / common_divisor)
    end

    return expr
end

# helpers for simplify_and_group
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

function simplify_and_group(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
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
