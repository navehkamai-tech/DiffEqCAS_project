using ModelingToolkit
using Symbolics
using DomainSets

using DiffEqCAS

@parameters t x y
@variables u(t,x,y)[1:3]

u_unwrapped = Symbolics.unwrap(u[1])
println("typeof u[1]: ", typeof(u_unwrapped))
println("is_tree(u[1]): ", SymbolicUtils.istree(u_unwrapped))
println("operation(u[1]): ", SymbolicUtils.operation(u_unwrapped))
println("arguments(u[1]): ", SymbolicUtils.arguments(u_unwrapped))

# Note that u(t,x,y) is represented internally as an array or similar,
# and u[1] has getindex as its operation.

sys_dvs = [u[1], u[2], u[3]]
dv_funcs = [SymbolicUtils.operation(Symbolics.unwrap(dv)) for dv in sys_dvs]
println("dv_funcs: ", dv_funcs)
