using ModelingToolkit
using Symbolics
using Test

using DiffEqCAS

@parameters t x y r theta
@variables u(t, x, y)

Dt = Differential(t)
eqs = [Dt(u) ~ 0]
bcs = [u ~ 0]
domain = [
    t => [0 < t, t < 1],
    x => [-1 < x, x < 1],
    y => [-1 < y, y < 1],
]
sys = PDESystem(eqs, bcs, domain, [t, x, y], [u]; name=:domain_change)

new_sys = change_ivs(
    sys,
    [t, r, theta],
    Dict(t => t, x => r * cos(theta), y => r * sin(theta)),
)

@test length(new_sys.domain) == 2
@test isequal(new_sys.domain[1].first, t)
@test isequal(new_sys.domain[2].first, (r, theta))

disk_sys = PDESystem(
    [],
    [],
    [(x, y) => [x^2 + y^2 < 1]],
    [x, y],
    [];
    name=:disk_domain_change,
)
new_disk_sys = change_ivs(
    disk_sys,
    [r, theta],
    Dict(x => r * cos(theta), y => r * sin(theta)),
)

@test length(new_disk_sys.domain) == 1
@test isequal(first(new_disk_sys.domain).first, r)
