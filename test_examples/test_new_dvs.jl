using ModelingToolkit
using Symbolics
using SymbolicUtils
using DomainSets

include("my_functions.jl")

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

@parameters t x y
@variables u(t,x,y)[1:3]

sys_dvs = [u[1], u[2], u[3]]

dv_funcs = unique([get_base_op(Symbolics.unwrap(dv)) for dv in sys_dvs])
println("dv_funcs: ", dv_funcs)

J_inv = zeros(Num, 0, 0)
var_map = Dict()
@variables r theta
new_ivs = [r, theta]
old_u = Symbolics.unwrap.([t, x, y])
new_u = Symbolics.unwrap.(new_ivs)

new_dvs = [Symbolics.wrap(custom_rewrite(Symbolics.unwrap(dv), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)) for dv in sys_dvs]
println("new_dvs: ", new_dvs)
