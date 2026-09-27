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

# try group_coefficients
try
    for eq in eqs
        println(group_coefficients(eq, [u[1], u[2]]))
    end
catch e
    println("Error in group_coefficients: ", e)
end
