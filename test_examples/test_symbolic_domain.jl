using Test
using Symbolics
using DiffEqCAS
using IntervalBoxes

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
