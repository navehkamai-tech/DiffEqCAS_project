using ModelingToolkit
using Symbolics
using DomainSets

include("my_functions.jl")

@parameters t x
@variables u(t,x)[1:2]

Dt = Differential(t)
Dx = Differential(x)

eqs = [Dt(u[1]) ~ Dx(Dx(u[1])) + u[2],
       Dt(u[2]) ~ Dx(Dx(u[2])) + u[1]]

dvs = [u[1], u[2]]

println("Testing simplify_and_group:")
try
    for eq in eqs
        println(simplify_and_group(eq, dvs))
    end
catch e
    println("Error in simplify_and_group: ", e)
    Base.display_error(e, catch_backtrace())
end
