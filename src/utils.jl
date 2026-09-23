
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

#=
need a builder function for PDEs. 
one thing it should do is order the domain constraints the same way the variables are ordered in PDEsystem.ivs 
it should also be a major part of the UI and make it easier, more convenient, and less error prone to initialize a system.
=#