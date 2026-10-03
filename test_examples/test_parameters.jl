using ModelingToolkit
using Symbolics
using SymbolicUtils
using DomainSets

using DiffEqCAS

@parameters t x y a b
@variables u(t, x, y)[1:2]

eqs = [Differential(t)(u[1]) ~ a * Differential(x, 2)(u[1]) + b * u[2],
    Differential(t)(u[2]) ~ a * Differential(x, 2)(u[2]) + b * u[1]]
bcs = [u[1] ~ 0, u[2] ~ 0]
domain = SymbolicDomain([
    t => [0 <= t, t <= 1],
    x => [-1 <= x, x <= 1],
    y => [-1 <= y, y <= 1],
])
sys = DiffEqSystem(eqs, bcs, domain, [t, x, y], [u[1], u[2]], name=:sys)

@parameters c d
param_mapping = Dict(a => c, b => d)

println("Testing change_parameters:")
new_sys = change_parameters(sys, param_mapping)
for eq in new_sys.eqs
    println(eq)
end
