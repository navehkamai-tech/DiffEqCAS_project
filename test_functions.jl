using Pkg
Pkg.activate(".")
include("my_functions.jl")
using Symbolics, DomainSets, SymbolicUtils
using Test

@testset "DiffEq Initialization" begin
    @variables x t
    @variables u(..)
    eqs = [Differential(t)(u(x,t)) ~ Differential(x)(Differential(x)(u(x,t)))]

    # Test valid creation
    sys = DiffEq(eqs, [x, t], [u(x,t)])
    @test length(sys.eqs) == 1

    # Check domains field
    @test sys.domains isa Vector{Pair{Any,DomainSets.Domain}}
    @test_throws ArgumentError addtodiffeq(sys, :domains, [])
end

@testset "special_rewriter - Dirac and Heaviside" begin
    @variables x
    dr = special_rewriter()

    @test isequal(dr(unwrap(Dirac(x))), unwrap(Dirac(x, 0)))
    @test isequal(simplify(wrap(dr(unwrap(x * Dirac(x, 0))))), 0)

    # Algebraic rules check
    @test isequal(dr(unwrap(Dirac(-x, 2))), unwrap((-1)^2 * Dirac(x, 2)))
end

@testset "change_independents (Complex function verification)" begin
    @variables x y r θ
    @variables u(..)

    # Laplacian in 2D Cartesian
    eqs = [Differential(x)(Differential(x)(u(x,y))) + Differential(y)(Differential(y)(u(x,y))) ~ 0]
    sys = DiffEq(eqs, [x, y], [u(x,y)])

    # Change to polar coordinates
    indep_mapping = Dict(x => r * cos(θ), y => r * sin(θ))
    new_indeps = [r, θ]

    new_sys = change_independents(sys, new_indeps, indep_mapping)
    @test length(new_sys.eqs) == 1

    # Verify the structure matches expectations
    laplacian_polar_eq = new_sys.eqs[1]

    D_r = Differential(r)
    D_r2 = Differential(r)^2
    D_theta2 = Differential(θ)^2

    ur2 = D_r2(u(r,θ))
    ur = D_r(u(r,θ))
    ut2 = D_theta2(u(r,θ))

    std_form = ur2 + (1/r)*ur + (1/r^2)*ut2

    diff_expr = laplacian_polar_eq.lhs - std_form
    val_map = Dict(ur2 => 1.5, ur => 0.5, ut2 => 2.0, r => 2.0, θ => 0.5)

    eval_diff = wrap(substitute(diff_expr, val_map))
    val = Symbolics.value(eval_diff)
    @test isequal(simplify(eval_diff), 0) || abs(val isa Number ? val : eval(Meta.parse(string(val)))) < 1e-10
end

@testset "change_dependents (Wave Equation)" begin
    @variables x t
    @variables u(..) v(..)

    # 1D Wave equation: u_tt = c^2 * u_xx
    c = 2.0
    eqs = [Differential(t)(Differential(t)(u(x,t))) - c^2 * Differential(x)(Differential(x)(u(x,t))) ~ 0]
    sys = DiffEq(eqs, [x, t], [u(x,t)])

    # Substitute u(x,t) = v(x,t) * exp(-t)
    dep_mapping = Dict(u(x,t) => v(x,t) * exp(-t))
    new_deps = [v(x,t)]

    new_sys = change_dependents(sys, new_deps, dep_mapping)
    @test length(new_sys.eqs) == 1

    # Check evaluation with some simple values to make sure transformation is equivalent
    v_expr = new_sys.eqs[1].lhs

    # Evaluate at v=1, v_t=0, v_tt=0, v_x=0, v_xx=0 (implies u=exp(-t), u_t=-exp(-t), u_tt=exp(-t), u_x=0, u_xx=0)
    # The original eq should be u_tt - c^2 u_xx = exp(-t) - 0 = exp(-t) ~ 0
    # Let's substitute manually.
    D_t = Differential(t)
    D_t2 = Differential(t)^2
    D_x2 = Differential(x)^2

    vt2 = D_t2(v(x,t))
    vt = D_t(v(x,t))
    vx2 = D_x2(v(x,t))

    val_map = Dict(vt2 => 0.0, vt => 0.0, vx2 => 0.0, v(x,t) => 1.0, t => 0.0)
    eval_diff = wrap(substitute(v_expr, val_map))
    @test isequal(Symbolics.unwrap(simplify(eval_diff)), 1.0) || abs(eval(Meta.parse(string(Symbolics.unwrap(simplify(eval_diff))))) - 1.0) < 1e-10
end
@testset "simplify_and_group" begin
    @variables x t
    @variables u(..)

    # equation: 2*u_x + 3*u_x + u_xx - u_t ~ 0
    # grouped should be: 5*u_x + u_xx - u_t ~ 0

    eq_in = 2*Differential(x)(u(x,t)) + 3*Differential(x)(u(x,t)) + Differential(x)(Differential(x)(u(x,t))) - Differential(t)(u(x,t)) ~ 0

    eq_grouped = simplify_and_group(eq_in, [u(x,t)])

    # check that terms are correctly combined
    lhs = expand_derivatives(eq_grouped.lhs)

    # We substitute simple values to verify equivalence to standard form
    D_t = Differential(t)
    D_x = Differential(x)
    D_x2 = Differential(x)^2

    ut = D_t(u(x,t))
    ux = D_x(u(x,t))
    uxx = D_x2(u(x,t))

    expected = 5*ux + uxx - ut

    diff_expr = lhs - expected

    val_map = Dict(ut => 1.5, ux => 0.5, uxx => 2.0)
    eval_diff = substitute(diff_expr, val_map)
    @test isequal(Symbolics.unwrap(simplify(eval_diff)), 0) || abs(eval(Meta.parse(string(Symbolics.unwrap(simplify(eval_diff)))))) < 1e-10
end
@testset "Error Paths" begin
    @variables x t u

    eqs = [Differential(t)(u) ~ Differential(x)(Differential(x)(u))]

    # Passing 'u' instead of 'u(x,t)' to build_system should fail
    @test_throws ArgumentError build_system(eqs, [u])

    @variables v(..)
    sys = DiffEq(eqs, [x, t], [v(x,t)])

    # Ambiguous domain modifications
    @test_throws ArgumentError addtodiffeq(sys, :domains, [])
end
