# ===========================================================================
# Decoration tests for `_execute_forward!` and the zero certificate.
#
# Paste before the "known issues" item of satisfiability_paving_test.jl (these
# items rely on `SatSetup`), or keep this as its own `*_test.jl` file.
#
# What is being pinned down
#   * SOUNDNESS  : a box on which the expression is undefined or discontinuous
#                  must NOT come back with decoration >= dac.  A failure here is a
#                  real bug and is exactly how a false "zero found" gets through.
#   * COMPLETENESS: a box with no singularity should come back >= dac.  A
#                  failure here only means we lose answers (too conservative).
#
# Decoration order in IntervalArithmetic: ill < trv < def < dac < com.
#   def = defined on the whole box, dac = defined AND continuous on the whole box.
# ===========================================================================

@testitem "paving: decorations through _execute_forward!" tags=[:paving, :forward, :decoration] setup=[SatSetup] begin
    using Symbolics, Random

    # Decoration of the root after a decorated forward pass over the given boxes.
    function dec(e, vars, ivs...)
        tape = CAS._compile_hc4_residual(e, CAS._EQ, vars)
        @assert length(ivs) == tape.num_vars
        dws = Vector{CAS._DI}(undef, tape.tape_len)
        for (i, iv) in enumerate(ivs)
            dws[i] = IA.interval(iv)
        end
        return IA.decoration(CAS._execute_forward!(tape, dws))
    end
    cont(d) = d >= IA.dac        # defined and continuous on the whole box
    defd(d) = d >= IA.def        # defined on the whole box

    hits(p, lo, hi) = lo <= p <= hi
    near(p, lo, hi, m=1e-6) = lo - m <= p <= hi + m
    # :bad = a singularity is inside the box, :good = clearly away from all of them,
    # :skip = within rounding distance of one (no claim either way).
    poles(ps) = (lo, hi) -> any(p -> hits(p, lo, hi), ps) ? :bad :
                            any(p -> near(p, lo, hi), ps) ? :skip : :good
    # a random box inside [a, b] with log-uniform width, so tiny boxes get tested too
    function randbox(rng, a, b)
        w = (b - a) * 10.0^(-5 * rand(rng))
        lo = a + (b - a - w) * rand(rng)
        return lo, lo + w
    end

    @testset "smooth operations on bounded boxes are dac" begin
        box = bi(-2.0, 3.0)
        for e in (x + 2, 3 * x, x^2, x^3, x^4, exp(x), exp2(x), exp10(x), sin(x), cos(x),
            atan(x), sinh(x), cosh(x), tanh(x), asinh(x), abs(x), x^2 + 1, sin(x) * cos(x),
            exp(-x^2), atan(x) - x)
            @test cont(dec(e, [x], box))
        end
    end

    @testset "unbounded boxes stay continuous when nothing is singular" begin
        @test cont(dec(x^2, [x], bi(1.0, Inf)))
        @test cont(dec(exp(x), [x], bi(-Inf, 0.0)))
        @test cont(dec(x^-1, [x], bi(1.0, Inf)))
        @test !cont(dec(x^-1, [x], bi(0.0, Inf)))
    end

    @testset "degenerate (point) boxes at a singularity are never continuous" begin
        # `_zero_point_sign` leans on this when it probes the corners of a box
        @test !cont(dec(x^-1, [x], bi(0.0)))
        @test !defd(dec(log(x), [x], bi(0.0)))
        @test !defd(dec(log(x), [x], bi(-1.0)))
        @test cont(dec(x^-1, [x], bi(2.0)))
    end

    @testset "singularities are detected per operation (randomized)" begin
        tanpoles = [(k + 0.5) * pi for k in -6:5]
        halfline = (lo, hi) -> lo <= 0 ? :bad : lo < 1e-6 ? :skip : :good
        unit = (lo, hi) -> (lo < -1 - 1e-9 || hi > 1 + 1e-9) ? :bad :
                           (lo >= -1 && hi <= 1) ? :good : :skip
        entries = [
            ("x^-1", x^-1, poles([0.0]), (-4.0, 4.0)),
            ("x^-2", x^-2, poles([0.0]), (-4.0, 4.0)),
            ("x^-3", x^-3, poles([0.0]), (-4.0, 4.0)),
            ("(x-1)^-1", (x - 1)^-1, poles([1.0]), (-3.0, 5.0)),
            ("(x^2-1)^-1", (x^2 - 1)^-1, poles([-1.0, 1.0]), (-3.0, 3.0)),
            # bounded results that HIDE a discontinuity: the enclosure alone cannot tell
            ("atan(x^-1)", atan(x^-1), poles([0.0]), (-4.0, 4.0)),
            ("tanh(x^-1)", tanh(x^-1), poles([0.0]), (-4.0, 4.0)),
            ("exp((x-2)^-2)", exp((x - 2)^-2), poles([2.0]), (-2.0, 6.0)),
            ("sign(x)", sign(x), poles([0.0]), (-4.0, 4.0)),
            ("tan(x)", tan(x), poles(tanpoles), (-8.0, 8.0)),
            ("log(x)", log(x), halfline, (-2.0, 6.0)),
            ("log2(x)", log2(x), halfline, (-2.0, 6.0)),
            ("log10(x)", log10(x), halfline, (-2.0, 6.0)),
            ("x^0.5", x^0.5, halfline, (-2.0, 6.0)),
            ("asin(x)", asin(x), unit, (-2.0, 2.0)),
            ("acos(x)", acos(x), unit, (-2.0, 2.0)),
            ("acosh(x)", acosh(x),
                (lo, hi) -> lo < 1 - 1e-9 ? :bad : lo >= 1 ? :good : :skip, (-1.0, 5.0)),
            ("atanh(x)", atanh(x),
                (lo, hi) -> (lo <= -1 || hi >= 1) ? :bad :
                            (lo > -1 + 1e-9 && hi < 1 - 1e-9) ? :good : :skip, (-2.0, 2.0)),
        ]
        for (name, e, classify, (a, b)) in entries
            @testset "$name" begin
                rng = MersenneTwister(2024)
                tape = CAS._compile_hc4_residual(e, CAS._EQ, [x])
                dws = Vector{CAS._DI}(undef, tape.tape_len)
                nbad = ngood = 0
                for _ in 1:400
                    lo, hi = randbox(rng, a, b)
                    c = classify(lo, hi)
                    c === :skip && continue
                    dws[1] = IA.interval(bi(lo, hi))
                    d = IA.decoration(CAS._execute_forward!(tape, dws))
                    if c === :bad
                        nbad += 1
                        ok = !cont(d)                       # SOUNDNESS
                        ok || @info "decoration too optimistic" name lo hi d
                        @test ok
                    else
                        ngood += 1
                        ok = cont(d)                        # COMPLETENESS
                        ok || @info "decoration too pessimistic" name lo hi d
                        @test ok
                    end
                end
                @test nbad >= 5 && ngood >= 5               # the sampling is not vacuous
            end
        end
    end

    @testset "the worst decoration wins through every combinator" begin
        # x carries the singularity on [-1, 1]; y, z are harmless.
        bad = (bi(-1.0, 1.0), bi(1.0, 2.0), bi(1.0, 2.0))
        good = (bi(1.0, 2.0), bi(1.0, 2.0), bi(1.0, 2.0))
        vars = [x, y, z]
        exprs = [
            x^-1 + y,                    # binary add
            y - x^-1,                    # sub
            -(x^-1),                     # neg
            y * x^-1,                    # binary mul
            y + z + x^-1,                # n-ary add
            y * z * x^-1,                # n-ary mul
            (x^-1)^2,                    # integer power
            (x^-1)^3,
            y^(x^-1),                    # real power, singular exponent
            (x^-1)^y,                    # real power, singular base
            abs(x^-1),
            exp(-abs(x^-1)),             # bounded result, hides the pole
            atan(x^-1),
            sin(x^-1),
            cos(x^-1) * y,
            log(y + x^-2),               # bare x^-2 on [-1,1] is [1,inf): log would look fine
            y^0.5 * sin(x^-1),
            x^-1 - sin(x^-1),
        ]
        for e in exprs
            @test !cont(dec(e, vars, bad...))               # SOUNDNESS
            @test cont(dec(e, vars, good...))               # COMPLETENESS
        end
        # a shared subexpression (DAG node) is evaluated once and must still poison both uses
        shared = log(x)^2 + exp(log(x))
        @test !defd(dec(shared, [x], bi(-1.0, 2.0)))
        @test cont(dec(shared, [x], bi(1.0, 2.0)))
        # abs/clipping of a partially undefined argument does not repair it
        @test !defd(dec(abs(log(x)), [x], bi(-1.0, 2.0)))
    end

    @testset "the scratch workspace does not leak decorations between evaluations" begin
        rel = mk(x^-1 - 1, ==)
        tape = CAS.compile_hc4(rel, [x])
        scratch = Vector{CAS._DI}(undef, tape.tape_len)
        pole = CAS._BI[bi(-1.0, 1.0)]
        clear = CAS._BI[bi(1.0, 2.0)]
        for _ in 1:3
            @test !cont(IA.decoration(CAS._zero_eval(tape, pole, scratch)))
            @test cont(IA.decoration(CAS._zero_eval(tape, clear, scratch)))
        end
    end
end

# ---------------------------------------------------------------------------
@testitem "paving: zero certificates reject discontinuous boxes" tags=[:paving, :certificate, :decoration] setup=[SatSetup] begin
    using Symbolics, Random

    hits(p, lo, hi) = lo <= p <= hi
    function randbox(rng, a, b)
        w = (b - a) * 10.0^(-5 * rand(rng))
        lo = a + (b - a - w) * rand(rng)
        return lo, lo + w
    end
    function mkcert(e, vars; inflate)
        rel = mk(e, ==)
        tape = CAS.compile_hc4(rel, vars)
        others = inflate ? CAS.CompiledHC4[] : nothing     # `[]` switches inflation on
        return CAS._ZeroCertificate(rel.residual, vars, tape; others=others), tape
    end
    probe = UInt64(1)
    ws = CAS._BI[]
    dws = CAS._DI[]

    # Residuals with NO zero in the box whose corner values nevertheless have opposite
    # signs, so an IVT that ignores a pole/jump would wrongly certify them.
    negatives = [
        ("x^-1 on [-1,1]", x^-1, [x], [bi(-1.0, 1.0)]),
        ("x^-1 on a hair around 0", x^-1, [x], [bi(-1e-9, 1e-9)]),
        ("(x-1)^-1 on [0,2]", (x - 1)^-1, [x], [bi(0.0, 2.0)]),
        ("sign(x)-0.5 on [-1,1]", sign(x) - 0.5, [x], [bi(-1.0, 1.0)]),
        ("sign(x)-0.5 on [0,1]", sign(x) - 0.5, [x], [bi(0.0, 1.0)]),
        ("atan(1/x) on [-1,1]", atan(x^-1), [x], [bi(-1.0, 1.0)]),
        ("exp(1/x)-1 on [-1,1]", exp(x^-1) - 1, [x], [bi(-1.0, 1.0)]),
        ("tan(x) on [1,2]", tan(x), [x], [bi(1.0, 2.0)]),
        ("y/x on [-1,1]x[1,2]", y * x^-1, [x, y], [bi(-1.0, 1.0), bi(1.0, 2.0)]),
    ]
    # Same machinery on boxes that DO contain a zero and are continuous: proves the
    # negatives above are rejected because of the decoration, not because the certificate
    # is simply broken or always false.
    positives = [
        ("x^-1 - 0.5 on [1,3]", x^-1 - 0.5, [x], [bi(1.0, 3.0)]),
        ("y/x - 1.2 on [1,2]x[1,2]", y * x^-1 - 1.2, [x, y], [bi(1.0, 2.0), bi(1.0, 2.0)]),
        ("tan(x) - 1 on [0,1]", tan(x) - 1, [x], [bi(0.0, 1.0)]),
    ]

    for inflate in (false, true)
        @testset "inflation=$inflate: never certified across a singularity" begin
            for (name, e, vars, ivs) in negatives
                cert, _ = mkcert(e, vars; inflate=inflate)
                ok1 = !CAS._zero_certify_box(cert, CAS._BI[ivs...])
                ok1 || @info "certified a box with no zero" name
                @test ok1
                ok2 = !cert(boxof(ivs...), probe, ws, dws)
                ok2 || @info "callable certified a box with no zero" name
                @test ok2
            end
        end
        @testset "inflation=$inflate: continuous boxes with a zero are still certified" begin
            for (name, e, vars, ivs) in positives
                cert, _ = mkcert(e, vars; inflate=inflate)
                @test CAS._zero_certify_box(cert, CAS._BI[ivs...])
                @test cert(boxof(ivs...), probe, ws, dws)
            end
        end
    end

    @testset "a point on the pole has no certified sign" begin
        cert, _ = mkcert(x^-1, [x]; inflate=false)
        @test CAS._zero_point_sign(cert, CAS._BI[bi(0.0)]) == 0
        @test CAS._zero_point_sign(cert, CAS._BI[bi(2.0)]) == 1
        @test CAS._zero_point_sign(cert, CAS._BI[bi(-2.0)]) == -1
    end

    @testset "randomized: a certified box never contains a singularity" begin
        tanpoles = [(k + 0.5) * pi for k in -6:5]
        # (name, residual, singular points, range, can the residual vanish at all?)
        entries = [
            ("tan(x) - 1", tan(x) - 1, tanpoles, (-8.0, 8.0), true),
            ("x^-1 - 0.5", x^-1 - 0.5, [0.0], (-4.0, 4.0), true),
            ("atan(1/x) - 0.3", atan(x^-1) - 0.3, [0.0], (-2.0, 8.0), true),
            ("sign(x) - 0.5", sign(x) - 0.5, [0.0], (-4.0, 4.0), false),
        ]
        for (name, e, ps, (a, b), can_vanish) in entries
            @testset "$name" begin
                cert, _ = mkcert(e, [x]; inflate=true)
                rng = MersenneTwister(7)
                naccepted = 0
                for _ in 1:2000
                    lo, hi = randbox(rng, a, b)
                    cert(boxof(bi(lo, hi)), probe, ws, dws) || continue
                    naccepted += 1
                    ok = !any(p -> hits(p, lo, hi), ps)
                    ok || @info "certified a box containing a singularity" name lo hi
                    @test ok
                end
                if can_vanish
                    @test naccepted > 0              # not vacuous: the certificate does fire
                else
                    @test naccepted == 0             # the residual never vanishes
                end
            end
        end
    end

    @testset "_inside_and_defined: bounded results cannot hide a pole" begin
        # atan(1/x) - 2 <= 0 holds wherever it is defined (atan <= pi/2 < 2), so the BARE
        # pass says :inside on [-1, 1]. Only the decoration knows 1/x is not continuous there.
        tape = CAS.compile_hc4(mk(atan(x^-1) - 2, <=), [x])
        d = Vector{CAS._DI}(undef, tape.tape_len)
        @test !CAS._inside_and_defined(tape, boxof(bi(-1.0, 1.0)), d)
        @test !CAS._inside_and_defined(tape, boxof(bi(0.0, 1.0)), d)
        @test CAS._inside_and_defined(tape, boxof(bi(0.5, 1.0)), d)
        @test CAS._inside_and_defined(tape, boxof(bi(-1.0, -0.5)), d)
    end
end
