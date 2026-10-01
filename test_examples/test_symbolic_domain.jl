using Test
using Symbolics
using DiffEqCAS
using IntervalBoxes
using StaticArrays

@variables x y z

domain = SymbolicDomain([
    x => [0 < x, x < 1],
    (y, z) => [y^2 + z^2 < 1],
])

@test all(isequal.(domain_variables(domain), [x, y, z]))
@test length(domain_components(domain)) == 2
@test isequal(domain[1].first, x)
@test isequal(domain[2].first, (y, z))

sys = DiffEqSystem([], [], domain, [x, y, z], [])
@test sys.domain isa SymbolicDomain
@test all(isequal.(collect(sys.domain), collect(domain)))

sys.domain_set = (IntervalBoxes.IntervalBox[], IntervalBoxes.IntervalBox[])
sys.domain = SymbolicDomain([x => [x > 0]])
@test sys.domain_set === nothing

@test DiffEqCAS.constraints_satisfiable([x > 0], [x => [x > 0]], true)
@test !DiffEqCAS.constraints_satisfiable([x <= 0, x >= 0], [x => [x > 2, x < 1]], true)
@test DiffEqCAS.constraints_satisfiable([2x > 0], [x => [2x > 0]], true)
@test DiffEqCAS.constraints_satisfiable([x <= 0, x >= 0],
    [x => [x^2 < 1]], true)

@test DiffEqCAS.is_in_domain(SVector(0.5), [x => [x > 0, x < 1]])
@test !DiffEqCAS.is_in_domain(SVector(1.5), [x => [x > 0, x < 1]])

@variables x2 y2 z2
component_system = DiffEqSystem(
    [], [], [x2 => [], (y2, z2) => [y2 > 2, y2 < 1]], [x2, y2, z2], [])
@test DiffEqCAS.factor_divisibility(x2, component_system).status === DiffEqCAS.haszero
