using Test
using DiffEqCAS

@testset "DiffEqCAS.jl" begin
    @testset "Symbolic Domains" begin include("test_symbolic_domain.jl") end
    @testset "Transform Domains" begin include("test_transform_domains.jl") end
    @testset "Simplification" begin include("test_simplification_pipeline.jl") end
    @testset "Change Independent Variables" begin include("test_change_ivs_domains.jl") end
    @testset "Simplification Domain" begin include("test_simplification_domain.jl") end
end