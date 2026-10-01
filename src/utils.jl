
_key_variables(key) = key isa Tuple ? key : (key,)

# Symbolic values may return symbolic expressions from `==`, so use `isequal`.
_contains_equal(values, target) = any(value -> isequal(value, target), values)

function simplify!(expr::Symbolics.Num)
    return Symbolics.simplify(expr)
end

function _find_matches(arr_A, arr_B)
    matches = []
    for (i, j) in zip(1:length(arr_A), 1:length(arr_B))
        if arr_A[i]==arr_B[j]
            push!(matches, (i, j))
        end
    end
    return matches[]
end

function _push_unique!(arr, new_vals)
    for new_val in new_vals
        _contains_equal(arr, new_val) ? nothing : push!(arr, new_val)
    end
    return arr
end

function _ordered_unique(values)
    result = Any[]
    return _push_unique!(result, values)
end

function D(vars...)
    # 1. Sort the provided variables alphabetically right away
    sorted_vars = sort(collect(vars), by=string)

    # 2. Return a custom operator that nests the Differentials from the inside out
    return expr -> foldr((v, ex) -> Differential(v)(ex), sorted_vars, init=expr)
end

function compute_J_inv(var_exprs, new_vars)
    J_T = transpose(jacobian(var_exprs, new_vars))
    J_inv = inv(Matrix(J_T))
    return simplify.(J_inv)
end

function chain_rule(J_inv, old_var_idx, new_vars, arg, order=1)
    term = wrap(arg)
    # Iteratively apply the chain rule for higher-order derivatives
    for _ in 1:order
        next_term = 0
        for j in eachindex(new_vars)
            D_j = Differential(new_vars[j])
            next_term += J_inv[old_var_idx, j] * D_j(term)
        end
        term = next_term
    end
    return unwrap(term)
end

function _has_depvar_or_diff(expr)
    # get_variables extracts [x, f(x), D(f(x))] and ignores standard math wrappers like sin()
    vars = Symbolics.get_variables(expr)

    for v in vars
        v_un = Symbolics.unwrap(v)
        if SymbolicUtils.istree(v_un)
            op = SymbolicUtils.operation(v_un)
            if op isa Differential || op isa SymbolicUtils.Sym
                return true
            end
        end
    end
    return false
end
#parameter helper
function extract_parameters(list::Tuple)
    symbols = Symbolics.Num[]
    for i in list
        if i isa Symbolics.Equation
            vars = collect(Symbolics.get_variables(unwrap(i.lhs - i.rhs)))
            append!(symbols, vars)
        elseif i isa Symbolics.Num
            vars = collect(Symbolics.get_variables(unwrap(i)))
            append!(symbols, vars)
        else
            throw(ArgumentError("cannot extract parameters from $(typeof(i))"))
        end
    end

    # Keep only unique variables found in the expressions
    unique_vars = unique(symbols)

    # Filter using ModelingToolkit's native parameter metadata check
    params = filter(unique_vars) do v
        ModelingToolkit.isparameter(unwrap(v))
    end

    # Return as Vector{Symbolics.Num} to maintain compatibility with your other functions
    return convert(Vector{Symbolics.Num}, wrap.(params))
end

function get_base_op(expr)
    if SymbolicUtils.istree(expr)
        op = SymbolicUtils.operation(expr)
        if op == getindex
            return get_base_op(SymbolicUtils.arguments(expr)[1])
        end
        return op
    end
    return expr
end

function simplify!(expr)
    return Symbolics.simplify(expr)
end
function expand!(expr)
    return Symbolics.expand(expr)
end
function expand_derivatives!(expr)
    return Symbolics.expand_derivatives(expr)
end

#symbolic rule util functions
notavariable(x) = ModelingToolkit.isparameter(x) || ModelingToolkit.isconstant(x) || x isa Number
is_pos_param(var) = notavariable(var) && get_sign(var) == positive
is_neg_param(var) = notavariable(var) && get_sign(var) == negative
is_number(x) = x isa Number
is_real(x) = x isa Real
is_complex(x) = x isa Number && !(x isa Real)
is_positive(x) = get_sign(x)==positive
is_negative(x) = get_sign(x)==negative