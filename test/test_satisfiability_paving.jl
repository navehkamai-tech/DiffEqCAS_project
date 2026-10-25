# ===========================================================================
# Tests for satisfiability.jl, paving.jl (and the helpers they lean on in
# utils.jl / types.jl).
#
# Run from the package environment:   julia --project -e 'include("test/test_satisfiability_paving.jl")'
# Assumes the package module is `DiffEqCAS` (change the import below if not).
#
# Philosophy
#   * Soundness claims (`No` is a proof, an interval is an enclosure) are tested
#     strictly, often against random sampling.
#   * Completeness claims (the engine *should* decide this) are only asserted
#     where plain interval/HC4 reasoning must succeed; elsewhere we assert
#     `!== No` / `!== Yes`, because `Unknown` is always an acceptable answer.
# ===========================================================================
using Test
using Random
using Symbolics
import DiffEqCAS
using IntervalArithmetic
const CAS = DiffEqCAS

const Yes, No, Unknown = CAS.Yes, CAS.No, CAS.Unknown
const _inf, _sup = IntervalArithmetic.inf, IntervalArithmetic.sup

@variables x y z
myf(v) = v
@register_symbolic myf(v)          # an op the HC4 tape does not know -> constraint is "dropped"

# ---------------------------------------------------------------- helpers ---
bi(a, b) = CAS._bi(a, b)
mk(e, op) = CAS.SymRelation(e, op)
C(e, op) = CAS.Constraint(mk(e, op))          # residual `e` ⋈ 0
evalf(e, kv...) = CAS._const_value(Symbolics.substitute(e, Dict(kv...)))

same(a::CAS.Evidence, b::CAS.Evidence) =
    all(f -> isequal(getfield(a, f), getfield(b, f)), fieldnames(CAS.Evidence))
ans3(e) = (e.neg, e.zero, e.pos)

function with_env(f; tol=CAS.tolerance[])
    t0 = CAS.tolerance[]
    CAS.tolerance[] = tol
    try
        f()
    finally
        CAS.tolerance[] = t0
    end
end

fresh(f) = (CAS.clear_cache!(); f())

const RELS = [CAS._LT, CAS._LE, CAS._GT, CAS._GE, CAS._EQ, CAS._NE]

# at the top of runtests.jl
const SKIP = Set(split(get(ENV, "SKIP_TESTS", ""), ','; keepempty=false))

macro maybe_testset(name, body)
    quote
        if $(esc(name)) in SKIP
            @info "Skipping testset" name=$(esc(name))
        else
            @testset $(esc(name)) $(esc(body))
        end
    end
end

# ===========================================================================
@testset "satisfiability + paving" begin

    # ---------------------------------------------------------------------------
    @maybe_testset "construction / ids" begin
        r = mk(x - 1, >=)
        @test r.relation === CAS._GE
        @test C(x, >).relation.relation === CAS._GT
        ids = [CAS.fresh_id() for _ in 1:50]
        @test allunique(ids) && issorted(ids)
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "relation utilities" begin
        @test length(CAS._RELATIONS) == 6
        @test all(r -> r in CAS._RELATIONS, RELS)

        @test CAS._relation_symbol(>=) === CAS._GE
        @test CAS._relation_symbol(Symbol("<")) === CAS._LT
        @test_throws ArgumentError CAS._relation_symbol(Symbol("<>"))
        @test_throws ArgumentError CAS._relation_symbol(+)
        for r in RELS
            @test CAS._relation_symbol(CAS._symbol_to_relation(r)) === r
        end
        @test_throws ArgumentError CAS._symbol_to_relation(:foo)

        # three independent encodings of "which residual signs satisfy the relation"
        for r in RELS
            mask = CAS._rel_mask(r)
            op = CAS._symbol_to_relation(r)
            for (bit, v) in ((0, -1), (1, 0), (2, 1))
                expected = ((mask >> bit) & 1) == 1
                @test CAS._holds(r, v) == expected
                @test op(v, 0) == expected
            end
            @test CAS._mask_to_rel(CAS._rel_mask(r)) === r
            @test CAS._negate_relation(CAS._negate_relation(r)) === r
            @test CAS._flip_relation(CAS._flip_relation(r)) === r
            for v in (-2.0, 0.0, 3.0)
                @test CAS._holds(CAS._negate_relation(r), v) == !CAS._holds(r, v)
                @test CAS._holds(CAS._flip_relation(r), -v) == CAS._holds(r, v)
            end
        end
        @test_throws ArgumentError CAS._mask_to_rel(0x00)
        @test_throws ArgumentError CAS._mask_to_rel(0b111)
        @test_throws ArgumentError CAS._holds(:foo, 1)

        # _STATUS_RULES: (redundant signs, infeasible signs)
        rep = (neg=-1, zero=0, pos=1)
        for r in RELS
            redundant, infeasible = CAS._STATUS_RULES[r]
            for s in (:neg, :zero, :pos)
                @test (s in redundant) == !CAS._holds(r, rep[s])
                @test (s in infeasible) == CAS._holds(r, rep[s])
            end
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "sign algebra" begin
        sets = [CAS._Signs(n, z, p) for n in (false, true) for z in (false, true) for p in (false, true)]
        function reps(s)
            v = Float64[]
            s.neg && append!(v, (-7.0, -1.0, -0.01))
            s.zero && push!(v, 0.0)
            s.pos && append!(v, (0.01, 1.0, 7.0))
            return v
        end
        signof(v) = v < 0 ? :neg : v == 0 ? :zero : :pos
        inset(s, v) = getfield(s, signof(v))
        present(vals) = CAS._Signs((:neg in vals), (:zero in vals), (:pos in vals))

        @maybe_testset "sound and exact for + and *" begin
            for a in sets, b in sets
                for (f, g) in ((CAS._s_add, +), (CAS._s_mul, *))
                    r = f(a, b)
                    actual = Symbol[signof(g(va, vb)) for va in reps(a) for vb in reps(b)]
                    for s in actual
                        @test getfield(r, s)                       # soundness
                    end
                    @test r == present(actual)                     # no needless precision loss
                end
            end
        end
        @maybe_testset "neg / inv / integer powers are sound" begin
            for a in sets
                for va in reps(a)
                    @test inset(CAS._s_neg(a), -va)
                    va != 0 && @test inset(CAS._s_inv(a), 1 / va)
                    for n in -3:4
                        (n < 0 && va == 0) && continue
                        @test inset(CAS._s_powint(a, n), va^n)
                    end
                end
            end
        end
        @maybe_testset "_sign_rule" begin
            P = CAS.Evidence(neg=No, zero=No, pos=Unknown)      # strictly positive
            N = CAS.Evidence(neg=Unknown, zero=No, pos=No)      # strictly negative
            A = CAS.Evidence()                                  # anything
            @test CAS._sign_rule(*, [x, y], [P, N]) == CAS._Signs(true, false, false)
            @test CAS._sign_rule(+, [x, y], [P, P]) == CAS._Signs(false, false, true)
            @test CAS._sign_rule(^, [x, Num(2)], [A]) == CAS._Signs(false, true, true)
            @test CAS._sign_rule(exp, [x], [A]) == CAS._Signs(false, false, true)
            @test CAS._sign_rule(abs, [x], [A]) == CAS._Signs(false, true, true)
            @test CAS._sign_rule(/, [x, y], [P, N]) == CAS._Signs(true, false, false)
            @test CAS._sign_rule(sin, [x], [A]) == CAS._ANY_SIGN
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "Evidence lattice" begin
        @maybe_testset "_join" begin
            for a in (Yes, No, Unknown)
                @test CAS._join(a, a) === a
                @test CAS._join(a, Unknown) === a
                @test CAS._join(Unknown, a) === a
            end
            @test CAS._join(Yes, No) === No
            @test CAS._join(No, Yes) === No
        end

        @maybe_testset "_seed_evidence" begin
            @test ans3(CAS._seed_evidence(CAS._LT)) == (Yes, No, No)
            @test ans3(CAS._seed_evidence(CAS._LE)) == (Unknown, Unknown, No)
            @test ans3(CAS._seed_evidence(CAS._GT)) == (No, No, Yes)
            @test ans3(CAS._seed_evidence(CAS._GE)) == (No, Unknown, Unknown)
            @test ans3(CAS._seed_evidence(CAS._EQ)) == (No, Yes, No)
            @test ans3(CAS._seed_evidence(CAS._NE)) == (Unknown, No, Unknown)
            e = CAS._seed_evidence(CAS._EQ)
            @test _inf(e.outer) == 0 && _sup(e.outer) == 0
        end

        @maybe_testset "_tighten" begin
            t = CAS._tighten(CAS.Evidence(outer=bi(1.0, 2.0)))
            @test ans3(t) == (No, No, Unknown)
            t = CAS._tighten(CAS.Evidence(outer=bi(-Inf, 0.0), strict_hi=true))
            @test t.neg === Unknown && t.zero === No && t.pos === No
            @test same(CAS._tighten(CAS.Evidence(outer=bi(1.0, 2.0), pos=No)), CAS._EMPTY_EVIDENCE)
            @test same(CAS._tighten(CAS.Evidence(outer=CAS._empty_bi())), CAS._EMPTY_EVIDENCE)
            @test same(CAS._tighten(CAS.Evidence(neg=No, zero=No, pos=No)), CAS._EMPTY_EVIDENCE)
            @test same(CAS._tighten(CAS.Evidence(ident_zero=true)), CAS._IDENT_ZERO)
            # a point that is excluded by its own strictness is empty
            @test same(CAS._tighten(CAS.Evidence(outer=bi(0.0, 0.0), strict_lo=true)), CAS._EMPTY_EVIDENCE)
            # idempotent
            for e in (CAS.Evidence(), CAS._seed_evidence(CAS._LE), CAS.Evidence(outer=bi(-3.0, 4.0)),
                CAS.Evidence(outer=bi(-3.0, 4.0), neg=No))
                t1 = CAS._tighten(e)
                @test same(CAS._tighten(t1), t1)
            end
        end

        @maybe_testset "_merge" begin
            pool = [CAS.Evidence(), CAS._seed_evidence(CAS._LT), CAS._seed_evidence(CAS._GE),
                CAS._seed_evidence(CAS._EQ), CAS._seed_evidence(CAS._NE),
                CAS._tighten(CAS.Evidence(outer=bi(1.0, 2.0))),
                CAS._tighten(CAS.Evidence(outer=bi(-3.0, 4.0)))]
            for a in pool
                @test same(CAS._merge(a, a), CAS._tighten(a))                 # idempotent
                @test same(CAS._merge(a, CAS.Evidence()), CAS._tighten(a))    # top is the identity
                for b in pool
                    @test same(CAS._merge(a, b), CAS._merge(b, a))            # commutative
                    m = CAS._merge(a, b)
                    if !isempty_interval(m.outer)                                      # only ever shrinks
                        @test _inf(m.outer) >= _inf(a.outer) && _sup(m.outer) <= _sup(a.outer)
                        @test _inf(m.outer) >= _inf(b.outer) && _sup(m.outer) <= _sup(b.outer)
                    end
                end
            end
            @test same(CAS._merge(CAS._seed_evidence(CAS._LT), CAS._seed_evidence(CAS._GE)), CAS._EMPTY_EVIDENCE)
            @test same(CAS._merge(CAS._seed_evidence(CAS._LT), CAS._seed_evidence(CAS._GT)), CAS._EMPTY_EVIDENCE)
            m = CAS._merge(CAS._seed_evidence(CAS._LE), CAS._seed_evidence(CAS._GE))
            @test _inf(m.outer) == 0 && _sup(m.outer) == 0 && m.neg === No && m.pos === No
            @test same(CAS._merge(CAS.Evidence(outer=bi(0.0, 1.0)), CAS.Evidence(outer=bi(2.0, 3.0))), CAS._EMPTY_EVIDENCE)
            @test same(CAS._merge(CAS._seed_evidence(CAS._GT), CAS._IDENT_ZERO), CAS._IDENT_ZERO)
        end

        @maybe_testset "_store! merges into the cache" begin
            CAS.clear_cache!()
            u = Symbolics.unwrap(x)
            CAS._store!(u, (1,), CAS.Evidence(outer=bi(0.0, Inf)))
            e = CAS._store!(u, (1,), CAS.Evidence(outer=bi(-Inf, 5.0)))
            @test _inf(e.outer) == 0 && _sup(e.outer) == 5
            @test same(CAS.cache[CAS._ekey(u, (1,))], e)
            # a different context does not see it
            @test !haskey(CAS.cache, CAS._ekey(u, (2,)))
        end

        @maybe_testset "cache keys depend on the paving environment" begin
            k1 = CAS._ekey(Symbolics.unwrap(x), (1,))
            k2 = with_env(() -> CAS._ekey(Symbolics.unwrap(x), (1,)); tol=0.5)
            @test k1 != k2
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "affine extraction and bound tightening" begin
        na(e, v=x) = CAS._numeric_affine(e, v)
        @test na(2x + 3) == (2.0, 3.0)
        @test na(x - 1) == (1.0, -1.0)
        @test na(3 - 2x) == (-2.0, 3.0)
        @test na((x + 1) / 2) == (0.5, 0.5)
        @test na(2 * (x - 1)) == (2.0, -2.0)
        @test na(x * y + 1) === nothing         # coefficient is not a number
        @test na(x^2) === nothing
        @test na(x * x) === nothing
        @test na(sin(x)) === nothing
        @test na(x / y) === nothing
        @test na(y + 1) === nothing             # x does not occur
        @test na(Num(3)) === nothing

        @maybe_testset "_tighten_bound!" begin
            b = CAS._Bnd()
            @test CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)       # x - 1 >= 0
            @test b.lo == 1.0 && !b.slo && b.hi == Inf
            # negative coefficient flips the relation:  -x + 3 > 0  <=>  x < 3
            b = CAS._Bnd()
            @test CAS._tighten_bound!(b, -1.0, 3.0, CAS._GT)
            @test b.hi == 3.0 && b.shi && b.lo == -Inf
            # equality pins both sides
            b = CAS._Bnd()
            @test CAS._tighten_bound!(b, 1.0, -2.0, CAS._EQ)
            @test b.lo == 2.0 && b.hi == 2.0 && !b.slo && !b.shi
            # contradictions
            b = CAS._Bnd()
            CAS._tighten_bound!(b, 1.0, -2.0, CAS._GT)             # x > 2
            @test !CAS._tighten_bound!(b, 1.0, -1.0, CAS._LT)      # x < 1
            # touching bounds: closed is feasible, one open side is not
            b = CAS._Bnd()
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)
            @test CAS._tighten_bound!(b, 1.0, -1.0, CAS._LE)
            b = CAS._Bnd()
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._GT)
            @test !CAS._tighten_bound!(b, 1.0, -1.0, CAS._LE)
            # strictness is never lost when the same bound is re-applied loosely
            b = CAS._Bnd()
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._GT)
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)
            @test b.slo
            b = CAS._Bnd()
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._GT)
            @test b.slo
            # a looser bound never loosens
            b = CAS._Bnd()
            CAS._tighten_bound!(b, 1.0, -1.0, CAS._LE)
            CAS._tighten_bound!(b, 1.0, -5.0, CAS._LE)
            @test b.hi == 1.0
        end

        @maybe_testset "_bound_evidence" begin
            e = CAS._bound_evidence(CAS._Bnd(1.0, Inf, false, false), true)
            @test ans3(e) == (No, No, Yes)
            e = CAS._bound_evidence(CAS._Bnd(1.0, Inf, false, false), false)    # not exact: no existence claims
            @test e.pos === Unknown && e.neg === No
            e = CAS._bound_evidence(CAS._Bnd(-1.0, 1.0, false, false), true)
            @test ans3(e) == (Yes, Yes, Yes)
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "components" begin
        cs = [C(x, >=), C(y, >=), C(x + y - 1, <=), C(z, >)]
        g = CAS._connected_groups(cs)
        @test length(g) == 2
        @test sort(length.(getfield.(g, :constraints))) == [1, 3]
        @test Set(Set(h.variables) for h in g) == Set([Set([x, y]), Set([z])])

        # order independent
        g2 = CAS._connected_groups(reverse(cs))
        @test [h.keys for h in g] == [h.keys for h in g2]
        # content-based: two constraints with the same content but different Ids collapse
        gd = CAS._connected_groups([C(x - 1, >=), C(x - 1, >=)])
        @test length(gd) == 1 && length(gd[1].constraints) == 1
        # different relation, same residual: distinct
        @test length(CAS._connected_groups([C(x, >=), C(x, >)])[1].constraints) == 2

        comps = CAS.constraint_components(cs)
        @test comps isa Vector{CAS.Comp}
        @test length(comps) == 2
        @test issorted([c.key for c in comps])
        @test CAS.constraint_components(comps) === comps
        @test [c.key for c in CAS.constraint_components(Random.shuffle(MersenneTwister(1), cs))] == [c.key for c in comps]
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "satisfiable" begin
        sat(cs) = fresh(() -> CAS.satisfiable(cs))

        @test sat(CAS.Constraint[]) === Yes
        @test sat([C(x - 1, >=), C(2 - x, >=)]) === Yes
        @test sat([C(x - 2, >=), C(1 - x, >=)]) === No
        @test sat([C(x - 1, >=), C(1 - x, >=)]) === Yes           # closed point
        @test sat([C(x - 1, >), C(1 - x, >=)]) === No             # open at the touching end
        @test sat([C(x - 1, >), C(2 - x, >)]) === Yes
        @test sat([C(Num(1), >)]) === Yes                         # constant constraints
        @test sat([C(Num(-1), >)]) === No
        @test sat([C(Num(0), ==)]) === Yes

        # blocks are independent; the answer is their conjunction
        ok = [C(x - 1, >=), C(2 - x, >=)]
        bad = [C(y, >), C(y + 1, <)]
        @test sat(vcat(ok, bad)) === No
        @test sat(vcat(bad, ok)) === No
        @test sat(vcat(ok, [C(y, >)])) === Yes

        # nonlinear
        @test sat([C(x^2 + 1, <=)]) === No                        # HC4 must see x^2 >= 0
        @test sat([C(x^2 + y^2 - 1, <=)]) !== No
        @test sat([C(x^2 + y^2 - 1, <=)]) === Yes
        @test sat([C(x^2 + y^2 - 1, <=), C(x + y - 3, >=)]) !== Yes
        @test sat([C(x^2 - 2, ==)]) !== No                        # x = ±√2 exists
        @test sat([C(x + y - 2, ==), C(x - y, ==)]) !== No        # x = y = 1
        @test sat([C(exp(x) - y, <=), C(y, <=), C(y + 1, >=)]) === No   # exp(x) > 0 >= y
        @test sat([C(sin(x) - 2, >=)]) === No

        # constraints the tape cannot compile are dropped: never a false `Yes`
        @test sat([C(myf(x), >), C(x - 1, <=), C(x + 1, >=), C(x * x - 3, <=)]) !== Yes

        # SymDomain and vector sources agree; extra relations are conjoined
        cs = [C(x - 1, >=), C(2 - x, >=)]
        dom = CAS._unchecked_domain(cs)
        @test CAS.satisfiable(dom) === Yes
        @test CAS.satisfiable(dom, [mk(x - 3, >=)]) === No
        @test CAS.satisfiable(dom, [mk(x - 1.5, >=)]) === Yes
        # context cache does not leak between different constraint sets
        @test CAS.satisfiable([C(x - 5, >=), C(2 - x, >=)]) === No
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "expr_evidence and sign predicates" begin
        q(f, e, cs) = fresh(() -> f(e, cs))

        @maybe_testset "constants" begin
            cs = CAS.Constraint[]
            @test ans3(CAS.expr_evidence(Num(3), cs)) == (No, No, Yes)
            @test ans3(CAS.expr_evidence(Num(-2), cs)) == (Yes, No, No)
            e0 = CAS.expr_evidence(Num(0), cs)
            @test e0.zero === Yes && e0.neg === No && e0.pos === No
        end

        @maybe_testset "single variable, x > 0" begin
            cs = [C(x, >)]
            @test q(CAS.is_positive, x, cs)
            @test q(CAS.is_nonzero, x, cs)
            @test q(CAS.is_nonnegative, x, cs)
            @test !q(CAS.is_negative, x, cs)
            @test q(CAS.can_be_negative, x, cs) === No
            @test q(CAS.can_be_zero, x, cs) === No
            @test q(CAS.can_be_positive, x, cs) === Yes
            @test q(CAS.is_positive, x + 1, cs)
            @test q(CAS.is_positive, x * x, cs)
            @test q(CAS.is_positive, 1 / x, cs)
            @test q(CAS.is_positive, x^3, cs)
            @test q(CAS.is_negative, -x, cs)
            # sign of x - 1 is genuinely open: nothing may be ruled out
            e = fresh(() -> CAS.expr_evidence(x - 1, cs))
            @test e.neg !== No && e.zero !== No && e.pos !== No
            @test !q(CAS.is_positive, x - 1, cs) && !q(CAS.is_negative, x - 1, cs) && !q(CAS.is_nonzero, x - 1, cs)
        end

        @maybe_testset "closed / open boundaries" begin
            @test q(CAS.is_nonnegative, x - 1, [C(x - 1, >=)])
            @test !q(CAS.is_positive, x - 1, [C(x - 1, >=)])           # x = 1 gives 0
            @test !q(CAS.is_nonzero, x - 1, [C(x - 1, >=)])
            @test q(CAS.is_positive, x - 1, [C(x - 1, >)])
            @test q(CAS.is_nonzero, x - 1, [C(x - 2, >=)])
            @test q(CAS.is_nonpositive, x, [C(-x, >=)])
            @test q(CAS.is_negative, x, [C(-x, >)])
            @test !q(CAS.is_positive, x, [C(x, >=)]) && q(CAS.is_nonnegative, x, [C(x, >=)])
        end

        @maybe_testset "no constraints" begin
            cs = CAS.Constraint[]
            @test q(CAS.is_positive, exp(x), cs)
            @test q(CAS.is_positive, cosh(x), cs)
            @test q(CAS.is_nonnegative, x^2, cs)
            @test q(CAS.is_nonnegative, abs(x), cs)
            @test q(CAS.is_positive, x^2 + 1, cs)
            @test q(CAS.is_negative, sin(x) - 2, cs)                   # interval [-1,1] - 2
            @test !q(CAS.is_positive, x^2, cs)                         # x = 0
            @test !q(CAS.is_nonzero, x^2, cs)
            e = fresh(() -> CAS.expr_evidence(x, cs))
            @test ans3(e) != (No, No, No) && e.neg !== No && e.pos !== No
        end

        @maybe_testset "several variables" begin
            cs = [C(x - 1, >=), C(y - 1, >=)]
            @test q(CAS.is_positive, x * y, cs)
            @test q(CAS.is_positive, x + y, cs)
            @test q(CAS.can_be_negative, x - y, cs) !== No             # x=1, y=2
            @test !q(CAS.is_nonnegative, x - y, cs)
            # unconstrained variable next to constrained one
            cs = [C(x, >)]
            @test !q(CAS.is_positive, y, cs)
            @test q(CAS.can_be_negative, x * y, cs) !== No
            # coupled constraint: the residual of a constraint is known to be >= 0
            cs = [C(x - y, >=), C(y - 1, >=)]
            @test q(CAS.is_nonnegative, x - y, cs)
            @test q(CAS.is_positive, x, cs)
        end

        @maybe_testset "paving-backed decisions" begin
            disk = [C(x^2 + y^2 - 1, <=)]
            @test q(CAS.is_negative, x + y - 3, disk)                  # |x+y| <= √2
            @test q(CAS.can_be_negative, x + y - 3, disk) !== No
            @test q(CAS.can_be_positive, x + y - 3, disk) === No
            @test q(CAS.can_be_positive, x * y, disk) !== No           # (0.5, 0.5)
            # soundness: (x-y)^2 is never negative, so no witness may claim otherwise
            @test q(CAS.can_be_negative, x^2 - 2 * x * y + y^2, disk) !== Yes
            # the boundary x^2+y^2 = 1 is attainable, so `No` would be wrong
            @test q(CAS.can_be_zero, x^2 + y^2 - 1, disk) !== No
            # witnesses can certify that every sign occurs
            e = fresh(() -> CAS.expr_evidence(x - 1, [C(x, >), C(3 - x, >)]))
            @test e.neg !== No && e.zero !== No && e.pos !== No
        end

        @maybe_testset "want only pursues what is asked" begin
            cs = [C(x, >)]
            e = fresh(() -> CAS.expr_evidence(x, cs; want=(:neg,)))
            @test e.neg === No
        end

        @maybe_testset "precomputed components give the same answers" begin
            cs = [C(x - 1, >=), C(y - 1, >=), C(x + y - 10, <=)]
            comps = CAS.constraint_components(cs)
            for e in (x, x + y, x * y, x - y, x^2 - y)
                a = fresh(() -> CAS.expr_evidence(e, cs))
                b = fresh(() -> CAS.expr_evidence(e, comps))
                @test same(a, b)
            end
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "relation_status" begin
        st(r, cs) = fresh(() -> CAS.relation_status(r, cs))

        d = [C(x, >)]                         # x > 0
        @test st(mk(x, >), d) === :redundant
        @test st(mk(x, >=), d) === :redundant
        @test st(mk(x, !=), d) === :redundant
        @test st(mk(x, <), d) === :infeasible
        @test st(mk(x, <=), d) === :infeasible
        @test st(mk(x, ==), d) === :infeasible
        @test st(mk(x - 1, >), d) === :active
        @test st(mk(x - 1, ==), d) === :active
        @test st(mk(x - 1, <=), d) === :active

        d = [C(x, >=)]                        # x >= 0
        @test st(mk(x, >=), d) === :redundant
        @test st(mk(x, >), d) === :active     # x = 0 violates it
        @test st(mk(x, ==), d) === :active
        @test st(mk(x, <), d) === :infeasible

        d = [C(x, >=), C(y, >=)]
        @test st(mk(x + y, >=), d) === :redundant
        @test st(mk(x * y + 1, >), d) === :redundant
        @test st(mk(x + y + 1, <), d) === :infeasible
        @test st(mk(x - y, >), d) === :active

        # a relation and its negation swap redundant <-> infeasible
        swap = Dict(:redundant => :infeasible, :infeasible => :redundant, :active => :active)
        for cs in ([C(x, >)], [C(x, >=), C(y, >=)], CAS.Constraint[])
            for e in (x, x - 1, x + y, x * y + 1, x^2)
                for r in RELS
                    a = st(mk(e, r), cs)
                    b = st(mk(e, CAS._negate_relation(r)), cs)
                    @test b === swap[a]
                end
            end
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "cache transparency and invariances" begin
        function battery(cs)
            (sat=CAS.satisfiable(cs),
                ev=[CAS.expr_evidence(e, cs) for e in (x, y, x + y, x * y, x^2 - y, x - y)],
                st=[CAS.relation_status(mk(e, r), cs) for e in (x - 1, y) for r in (CAS._GT, CAS._LE)])
        end
        same_battery(a, b) = a.sat === b.sat && a.st == b.st && all(same.(a.ev, b.ev))
        build() = [C(x - 1, >=), C(3 - x, >=), C(x + y - 2, <=), C(y, >)]

        ref = fresh(() -> battery(build()))
        @test same_battery(ref, battery(build()))                      # warm cache, new Ids
        rng = MersenneTwister(7)
        for _ in 1:5
            @test same_battery(ref, battery(Random.shuffle(rng, build())))   # order and Ids irrelevant
            @test same_battery(ref, fresh(() -> battery(Random.shuffle(rng, build()))))
        end
        # a tiny cache must not change answers
        old = CAS.cache_size[]
        try
            CAS.resize_cache!(8)
            @test same_battery(ref, fresh(() -> battery(build())))
        finally
            CAS.resize_cache!(old)
        end
        # changing the paving settings must not change soundness of the answers
        with_env(tol=0.05) do
            b = fresh(() -> battery(build()))
            @test b.sat === ref.sat
            for (u, v) in zip(ref.ev, b.ev)       # neither run may contradict the other
                @test all(w -> !(CAS._answer(u, w) === Yes && CAS._answer(v, w) === No), (:neg, :zero, :pos))
                @test all(w -> !(CAS._answer(u, w) === No && CAS._answer(v, w) === Yes), (:neg, :zero, :pos))
            end
        end
    end

    # ---------------------------------------------------------------------------
    @maybe_testset "randomized soundness against sampling" begin
        rng = MersenneTwister(20261022)
        exprs = [x + y, x - y, x * y, x^2 - y, x * y - 1, exp(x) - y, abs(x) - 1,
            (x - 1) * (x + 1), x / (y^2 + 1), sin(x) - y, x^3 - x, atan(x) - y, log(y^2 + 1) - x]
        for trial in 1:10
            x0 = 6 * rand(rng) - 3
            x1 = x0 + 0.1 + 3 * rand(rng)
            y0 = 6 * rand(rng) - 3
            y1 = y0 + 0.1 + 3 * rand(rng)
            box = [C(x - x0, >=), C(x1 - x, >=), C(y - y0, >=), C(y1 - y, >=)]
            coupled = vcat(box, [C(x - y, >=)])

            pts = [(a, b) for a in (x0, x1) for b in (y0, y1)]
            for _ in 1:120
                push!(pts, (x0 + (x1 - x0) * rand(rng), y0 + (y1 - y0) * rand(rng)))
            end

            for (cs, feasible) in ((box, p -> true), (coupled, p -> p[1] >= p[2]))
                P = filter(feasible, pts)
                isempty(P) && continue
                CAS.clear_cache!()
                for e in exprs
                    ev = CAS.expr_evidence(e, cs)
                    @test !isempty_interval(ev.outer)                                   # feasible context
                    for (px, py) in P
                        v = evalf(e, x => px, y => py)
                        (v === nothing || !isfinite(v)) && continue
                        tol = 1e-9 * (1 + abs(v))
                        @test _inf(ev.outer) - tol <= v <= _sup(ev.outer) + tol      # enclosure
                        ev.neg === No && @test v >= -tol
                        ev.pos === No && @test v <= tol
                        ev.zero === No && @test v != 0
                    end
                end
            end
        end
    end

    # ===========================================================================
    #                                 PAVING
    # ===========================================================================
    @maybe_testset "paving: opcode and tape compilation" begin
        @test CAS._give_confine(CAS._LT) == bi(-Inf, 0.0)
        @test CAS._give_confine(CAS._LE) == bi(-Inf, 0.0)
        @test CAS._give_confine(CAS._GT) == bi(0.0, Inf)
        @test CAS._give_confine(CAS._GE) == bi(0.0, Inf)
        @test CAS._give_confine(CAS._EQ) == bi(0.0, 0.0)
        @test isequal(CAS._give_confine(CAS._NE), CAS._entire_bi())
        @test_throws ArgumentError CAS._give_confine(:foo)

        @test CAS._map_opcode(-, 1, false) == CAS.OP_NEG
        @test CAS._map_opcode(-, 2, false) == CAS.OP_SUB
        @test CAS._map_opcode(+, 2, false) == CAS.OP_ADD
        @test CAS._map_opcode(exp, 1, false) == CAS.OP_EXP
        @test_throws ArgumentError CAS._map_opcode(floor, 1, false)

        tape = CAS.compile_hc4(mk(x * y + 1, >=), [x, y])
        @test tape.num_vars == 2
        @test tape.tape_len >= 4
        @test 1 <= tape.root_idx <= tape.tape_len
        @test tape.confine == bi(0.0, Inf)
        @test_throws ArgumentError CAS.compile_hc4(mk(x + z, >=), [x])      # z is not a declared variable
        @test_throws ArgumentError CAS.compile_hc4(mk(myf(x), >=), [x])     # unknown operation

        CAS.clear_cache!()
        @test CAS._compilable(mk(x^2 + sin(y), >=))
        @test !CAS._compilable(mk(myf(x), >=))
        @test !CAS._compilable(mk(myf(x), >=))                              # cached answer is stable
    end

    @maybe_testset "paving: forward evaluation encloses the true value" begin
        rng = MersenneTwister(99)
        exprs = [x + y, x * y, x - y, x^2 - y, x^3 - 2x, exp(x) / (y^2 + 1), abs(x - y),
            sin(x) * cos(y), tanh(x) * y, x / (y^2 + 1), log(y^2 + 1), atan(x) - y]
        for e in exprs
            tape = CAS.compile_hc4(mk(e, >=), [x, y])
            ws = Vector{CAS._BI}(undef, tape.tape_len)
            for _ in 1:40
                px, py = 8 * rand(rng) - 4, 8 * rand(rng) - 4
                v = evalf(e, x => px, y => py)
                for r in (1e-3, 0.0, 0.5)               # fat box, point box
                    ws[1] = bi(px - r, px + r)
                    ws[2] = bi(py - r, py + r)
                    rng_iv = CAS._execute_forward!(tape, ws)
                    tol = 1e-9 * (1 + abs(v))
                    @test !isempty_interval(rng_iv)
                    @test _inf(rng_iv) - tol <= v <= _sup(rng_iv) + tol
                end
            end
        end
    end

    @maybe_testset "paving: HC4Revise" begin
        box1(a, b) = CAS.IntervalBox((bi(a, b),))
        rel = mk(x - 1, >=)
        tape = CAS.compile_hc4(rel, [x])
        ws = Vector{CAS._BI}(undef, tape.tape_len)
        @test CAS.HC4Revise(box1(2.0, 3.0), tape, ws)[1] === :inside
        @test CAS.HC4Revise(box1(-3.0, 0.0), tape, ws)[1] === :outside
        st, b = CAS.HC4Revise(box1(0.0, 2.0), tape, ws)
        @test st === :unknown
        @test _inf(CAS._bi(b[1])) >= 1.0 - 1e-12 && _sup(CAS._bi(b[1])) == 2.0

        c = CAS.HC4Revise(box1(-5.0, 5.0), [x], rel)                  # standalone API
        @test _inf(CAS._bi(c[1])) >= 1.0 - 1e-12 && _sup(CAS._bi(c[1])) == 5.0
        @test isempty_interval(CAS._bi(CAS.HC4Revise(box1(-5.0, 5.0), [x], mk(x - 10, >=))[1]))

        # contraction never removes a feasible point
        rng = MersenneTwister(5)
        box2 = CAS.IntervalBox((bi(-2.0, 2.0), bi(-2.0, 2.0)))
        for r in (mk(x^2 + y^2 - 1, <=), mk(x * y - 1, <=), mk(x * y - 1, >=), mk(sin(x) - y, >=),
            mk(exp(x) - y - 2, <=), mk(abs(x) + abs(y) - 1, <=), mk(x - y^2, ==))
            res = CAS.HC4Revise(box2, [x, y], r)
            for _ in 1:400
                px, py = 4 * rand(rng) - 2, 4 * rand(rng) - 2
                v = evalf(r.residual, x => px, y => py)
                CAS._holds(r.relation, v) || continue
                ix, iy = CAS._bi(res[1]), CAS._bi(res[2])
                @test !isempty_interval(ix) && !isempty_interval(iy)
                @test _inf(ix) - 1e-9 <= px <= _sup(ix) + 1e-9
                @test _inf(iy) - 1e-9 <= py <= _sup(iy) + 1e-9
            end
        end
    end

    @maybe_testset "paving: _window and _contract" begin
        with_env() do
            @test CAS._window(bi(1.0, 2.0)) == bi(1.0, 2.0)
            @test isempty_interval(CAS._window(CAS._empty_bi()))
            for iv in (CAS._entire_bi(), bi(0.0, Inf), bi(-Inf, 5.0), bi(-Inf, -50.0), bi(50.0, Inf))
                w = CAS._window(iv)
                @test isfinite(_inf(w)) && isfinite(_sup(w))
                @test _inf(w) <= _sup(w)
                isfinite(_inf(iv)) && @test _inf(w) == _inf(iv)       # finite ends are kept
                isfinite(_sup(iv)) && @test _sup(w) == _sup(iv)
            end
        end

        cons(cs...) = collect(CAS.Constraint, cs)
        ok, b = CAS._contract(cons(C(x - 1, >=)), [x], [bi(-5.0, 5.0)])
        @test ok && _inf(b[1]) >= 1.0 - 1e-12 && _sup(b[1]) == 5.0
        ok, _ = CAS._contract(cons(C(x - 6, >=)), [x], [bi(-5.0, 5.0)])
        @test !ok
        ok, _ = CAS._contract(cons(C(x^2 + 1, <=)), [x], [bi(-5.0, 5.0)])
        @test !ok
        ok, b = CAS._contract(cons(C(x + y - 4, ==)), [x, y], [bi(0.0, 1.0), bi(0.0, 10.0)])
        @test ok && _inf(b[2]) >= 3.0 - 1e-9 && _sup(b[2]) <= 4.0 + 1e-9
        ok, b = CAS._contract(cons(C(x^2 - 4, <=)), [x], [bi(-10.0, 10.0)])
        @test ok && _inf(b[1]) >= -2.0 - 1e-9 && _sup(b[1]) <= 2.0 + 1e-9 && _inf(b[1]) <= -2.0 && _sup(b[1]) >= 2.0
        # nothing compilable: bounds come back untouched
        ok, b = CAS._contract(cons(C(myf(x), >)), [x], [bi(-5.0, 5.0)])
        @test ok && b == [bi(-5.0, 5.0)]
    end

    @maybe_testset "paving: _pave_answer / _pave_boxes" begin
        unit = [bi(-2.0, 2.0), bi(-2.0, 2.0)]
        width(B, i) = _sup(CAS._bi(B[i])) - _inf(CAS._bi(B[i]))
        area(Bs) = isempty(Bs) ? 0.0 : sum(width(B, 1) * width(B, 2) for B in Bs)

        with_env(tol=0.05) do
            disk = [C(x^2 + y^2 - 1, <=)]
            feasible, inner, boundary, dropped = CAS._pave_boxes(disk, [x, y], unit)
            @test feasible && !dropped && !isempty(inner)
            # every inner box lies inside the disk, every boundary box is small
            for B in inner
                far2 = sum(max(abs(_inf(CAS._bi(B[i]))), abs(_sup(CAS._bi(B[i]))))^2 for i in 1:2)
                @test far2 <= 1 + 1e-9          # farthest corner is still in the disk
            end
            @test all(B -> max(width(B, 1), width(B, 2)) < 0.05 + 1e-12, boundary)
            # inner ⊆ disk ⊆ inner ∪ boundary (in area)
            @test area(inner) <= pi + 1e-9
            @test area(inner) + area(boundary) >= pi - 1e-9

            # no constraints: the whole box is inner
            inner0, boundary0 = CAS._pave_answer(CAS.IntervalBox(Tuple(unit)), CAS.Constraint[], [x, y], 0.1)
            @test length(inner0) == 1 && isempty(boundary0)

            # empty / infeasible / dropped
            @test CAS._pave_boxes(disk, [x, y], [CAS._empty_bi(), bi(0.0, 1.0)])[1] === false
            @test CAS._pave_boxes([C(x^2 + 1, <=)], [x], [bi(-3.0, 3.0)])[1] === false
            f, i, bnd, dr = CAS._pave_boxes([C(myf(x), >), C(x - 1, <=)], [x], [bi(0.0, 2.0)])
            @test dr && f
        end

        @maybe_testset "more than 64 constraints still classify inner boxes" begin
            many = [C(x - 1, >=) for _ in 1:65]
            with_env(tol=0.05) do
                inner, boundary = CAS._pave_answer(CAS.IntervalBox((bi(2.0, 3.0),)), many, [x], 0.05)
                @test !isempty(inner)
            end
        end
    end

    @maybe_testset "paving: _pave_answer" begin
        with_env(tol=0.05) do
            pa(cs, vars, ivs) = fresh(() -> CAS._pave_answer(cs, vars, ivs))
            @test pa([C(x - 1, >=)], [x], [bi(0.0, 2.0)]) === Yes
            @test pa([C(x - 3, >=)], [x], [bi(0.0, 2.0)]) === No
            @test pa([C(x - 1, >=)], [x], [CAS._empty_bi()]) === No
            @test pa([C(x^2 + y^2 - 1, <=)], [x, y], [bi(-2.0, 2.0), bi(-2.0, 2.0)]) === Yes
            @test pa([C(x^2 + y^2 - 1, <=), C(x + y - 3, >=)], [x, y], [bi(-2.0, 2.0), bi(-2.0, 2.0)]) === No
            @test pa([C(x^2 - 2, ==)], [x], [bi(0.0, 3.0)]) !== No            # irrational root
            # dropped constraints forbid certifying anything
            @test pa([C(myf(x), >), C(x - 1, <=)], [x], [bi(0.0, 2.0)]) === Unknown
            # dropped constraints may still prove emptiness
            @test pa([C(myf(x), >), C(x - 5, >=)], [x], [bi(0.0, 2.0)]) === No
        end
    end

    @maybe_testset "paving: _sample_points" begin
        p = CAS._sample_points([bi(0.0, 2.0), bi(10.0, 20.0)])
        @test p[1] == [1.0, 15.0]
        @test Set(p[2:end]) == Set([[0.0, 10.0], [2.0, 10.0], [0.0, 20.0], [2.0, 20.0]])
        big = [bi(0.0, 1.0) for _ in 1:7]
        p = CAS._sample_points(big)
        @test length(p) == 3 && p[2] == zeros(7) && p[3] == ones(7)
    end

    @maybe_testset "paving: _find_witnesses" begin
        with_env(tol=0.05) do
            vars, ivs = [x], [bi(-10.0, 10.0)]
            cs = [C(x, >), C(3 - x, >)]                                # x in (0, 3)
            w = CAS._find_witnesses(Symbolics.unwrap(x - 1), cs, vars, ivs)
            @test w.neg && w.zero && w.pos
            w = CAS._find_witnesses(Symbolics.unwrap(x^2 + 1), [C(x + 1, >), C(1 - x, >)], vars, ivs)
            @test !w.neg && !w.zero && w.pos                           # soundness: never invents a sign
            w = CAS._find_witnesses(Symbolics.unwrap(x), [C(x - 5, >=), C(1 - x, >=)], vars, ivs)
            @test w == CAS._NO_WITNESS                                 # infeasible context
            w = CAS._find_witnesses(Symbolics.unwrap(x), [C(myf(x), >), C(x, >), C(1 - x, >)], vars, ivs)
            @test w == CAS._NO_WITNESS                                 # dropped constraint
        end
    end
end # top-level testset
