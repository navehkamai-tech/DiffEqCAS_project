using ModelingToolkit
using Symbolics
using Test

using DiffEqCAS

@parameters x y r theta

disk_domain = [((x, y) => [x^2 + y^2 < 1])]
polar_disk = DiffEqCAS.transform_domains(
    disk_domain,
    Dict(x => r * cos(theta), y => r * sin(theta)),
    [r, theta],
)

@test length(polar_disk) == 1
@test isequal(first(polar_disk).first, r)
@test length(first(polar_disk).second) == 1
@test isequal(
    Symbolics.simplify(first(polar_disk).second[1]),
    r^2 < 1,
)

coupled_domain = [((x, y) => [x + y < 1])]
polar_coupled = DiffEqCAS.transform_domains(
    coupled_domain,
    Dict(x => r * cos(theta), y => r * sin(theta)),
    [r, theta],
)

@test length(polar_coupled) == 1
@test isequal(first(polar_coupled).first, (r, theta))
