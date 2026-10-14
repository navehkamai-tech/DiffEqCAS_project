using ModelingToolkit
using Symbolics
using SymbolicUtils

@parameters t x y
@variables u(t, x, y)[1:3]

ud = Symbolics.unwrap(u[1])
arg1 = SymbolicUtils.arguments(ud)[1]
println("arg1: ", arg1)
println("istree arg1: ", SymbolicUtils.iscall(arg1))
if SymbolicUtils.iscall(arg1)
    println("operation arg1: ", SymbolicUtils.operation(arg1))
    println("arguments arg1: ", SymbolicUtils.arguments(arg1))
end
