using Symbolics
using SymbolicUtils
@variables t x
@variables u(t, x)[1:2]
for d in [u[1], u[2]]
    println("d = ", d)
    ud = Symbolics.unwrap(d)
    println("istree = ", SU.iscall(ud))
    if SU.iscall(ud)
        println("operation = ", SU.operation(ud))
        println("arguments = ", SU.arguments(ud))
    end
end
