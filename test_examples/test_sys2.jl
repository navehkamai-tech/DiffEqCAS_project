using ModelingToolkit
using Symbolics
using DomainSets

include("my_functions.jl")

@parameters t x y
@variables u(t,x,y)[1:3]

Dt = Differential(t)
Dx = Differential(x)
Dy = Differential(y)

# Test change_ivs
@parameters r theta
eqs = [Dt(u[1]) ~ Dx(Dx(u[1])) + Dy(Dy(u[1])) + u[2],
       Dt(u[2]) ~ Dx(Dx(u[2])) + Dy(Dy(u[2])) + u[1],
       Dt(u[3]) ~ u[1]*u[2]]

bcs = [u[1] ~ 0, u[2] ~ 0, u[3] ~ 0]
domain = [t ∈ Interval(0, 1), x ∈ Interval(-1, 1), y ∈ Interval(-1, 1)]

# Create PDESystem (using internal constructors, or just fields)
sys = PDESystem(eqs, bcs, domain, [t,x,y], [u[1],u[2],u[3]], name=:test_sys)

# Apply change_ivs
println("Testing change_ivs:")
iv_mapping = Dict(x => r*cos(theta), y => r*sin(theta))
try
    # In my_functions.jl, change_ivs computes Jacobian of iv_exprs w.r.t new_ivs.
    # So if iv_mapping is mapping x and y to r, theta, new_ivs should just be [r, theta].
    # But wait, iv_exprs in change_ivs builds an array from sys.ivs.
    # If sys.ivs is [t, x, y], then iv_exprs is [t, r*cos(theta), r*sin(theta)].
    # Then it computes J_inv = inv(transpose(jacobian(iv_exprs, new_ivs))).
    # So new_ivs MUST be the same length as iv_exprs!
    # That means new_ivs should be [t, r, theta].
    # Let's try that.
    new_sys = change_ivs(sys, [t, r, theta], Dict(t=>t, x => r*cos(theta), y => r*sin(theta)))
    for eq in new_sys.eqs
        println(eq)
    end
catch e
    println("Error in change_ivs: ", e)
    Base.display_error(e, catch_backtrace())
end
