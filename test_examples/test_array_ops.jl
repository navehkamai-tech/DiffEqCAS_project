using Symbolics
using SymbolicUtils
@variables t x
@variables u(t,x)[1:2]
for d in [u[1], u[2]]
    println("d = ", d)
    ud = Symbolics.unwrap(d)
    println("istree = ", SymbolicUtils.istree(ud))
    if SymbolicUtils.istree(ud)
        println("operation = ", SymbolicUtils.operation(ud))
        println("arguments = ", SymbolicUtils.arguments(ud))
    end
end
