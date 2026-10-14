using ModelingToolkit
using Symbolics
using DomainSets

using DiffEqCAS

@parameters t x
@variables u(t,x)[1:2]

Dt = Differential(t)
Dx = Differential(x)

eqs = [Dt(u[1]) ~ Dx(Dx(u[1])) + u[2],
       Dt(u[2]) ~ Dx(Dx(u[2])) + u[1]]

dvs = [u[1], u[2]]

println("Testing group_coefficients:")
try
    for eq in eqs
        println(group_coefficients(eq, dvs))
    end
catch e
    println("Error in group_coefficients: ", e)
    Base.display_error(e, catch_backtrace())
end
