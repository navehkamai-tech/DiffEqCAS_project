using ModelingToolkit
using Symbolics
using SymbolicUtils
using DomainSets

using DiffEqCAS

@parameters t x y
@variables u(t,x,y)[1:3]

Dt = Differential(t)
Dx = Differential(x)
Dy = Differential(y)

eqs = [Dt(u[1]) ~ Dx(Dx(u[1])) + Dy(Dy(u[1])) + u[2],
       Dt(u[2]) ~ Dx(Dx(u[2])) + Dy(Dy(u[2])) + u[1],
       Dt(u[3]) ~ u[1]*u[2]]

bcs = [u[1] ~ 0, u[2] ~ 0, u[3] ~ 0]
domain = [t ∈ Interval(0, 1), x ∈ Interval(-1, 1), y ∈ Interval(-1, 1)]
sys = PDESystem(eqs, bcs, domain, [t,x,y], [u[1],u[2],u[3]], name=:test_sys)

@variables v(t,x,y)[1:3]

dv_mapping = Dict(u[1] => v[1] + v[2], u[2] => v[1] - v[2], u[3] => v[3])

println("Testing change_dvs:")
try
    new_sys = change_dvs(sys, [v[1], v[2], v[3]], dv_mapping)
    for eq in new_sys.eqs
        println(eq)
    end
catch e
    println("Error in change_dvs: ", e)
    Base.display_error(e, catch_backtrace())
end
