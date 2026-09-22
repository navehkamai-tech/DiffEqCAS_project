using ModelingToolkit
using Symbolics
using DomainSets

using DiffEqCAS

@parameters t x
@variables u(t,x)[1:2]

Dt = Differential(t)
Dx = Differential(x)

eqs = [Dt(u) ~ Dx(Dx(u))]

@show eqs

# try simplify_and_group
try
    for eq in eqs
        println(simplify_and_group(eq, [u[1], u[2]]))
    end
catch e
    println("Error in simplify_and_group: ", e)
end
