# ===========================================================================
# Tests for satisfiability.jl and paving.jl (and the helpers they lean on in
# utils.jl / types.jl), written as `@testitem`s for ReTestItems.jl so any
# single item can be rerun in isolation, in the REPL process.
#
#   using Revise, DiffEqCAS, ReTestItems       # NOT `using TestItems`
#   runtests(DiffEqCAS; nworkers=0)                           # everything
#   runtests(DiffEqCAS; name=r"HC4Revise", nworkers=0)        # by name (regex)
#   runtests(DiffEqCAS; tags=[:paving], nworkers=0)           # by tag
#   runtests("test/satisfiability_paving_test.jl"; nworkers=0)  # this file only
#
# ReTestItems rules this file follows:
#   * the file name ends in `_test.jl`
#   * the only top-level code is `@testsetup module` / `@testitem` blocks
#   * a `@testsetup module` is its own module: names reach an item ONLY if the
#     module `export`s them, and its `using` statements do NOT carry over, so
#     each item does its own `using Symbolics, Random`.
#
# Assumes the package module is `DiffEqCAS` (change it in `SatSetup` below).
#
# Philosophy
#   * Soundness claims (`No` is a proof, an interval is an enclosure) are tested
#     strictly, often against random sampling.
#   * Completeness claims (the engine *should* decide this) are only asserted
#     where plain interval/HC4 reasoning must succeed; elsewhere we assert
#     `!== No` / `!== Yes`, because `Undetermined` is always an acceptable answer.
#
# ===========================================================================
# Shared setup. Evaluated inside every test item that lists `setup=[SatSetup]`.
# ---------------------------------------------------------------------------
@testsetup module SatSetup
using Random
using Symbolics
using IntervalArithmetic
import DiffEqCAS
const CAS = DiffEqCAS
const IA = IntervalArithmetic

# Everything below is visible inside items via `setup=[SatSetup]` (ReTestItems
# only brings *exported* names into the item).
export CAS, IA, Yes, No, Undetermined, _inf, _sup, x, y, z, myf,
    bi, boxof, ivof, mk, C, cons, mkcomp, evalf,
    iv_eq, iv_empty, iv_in, iv_sub, ivs_eq, rand_in,
    symin, varnames, same, ans3, with_env, fresh, RELS


const Yes, No, Undetermined = CAS.Yes, CAS.No, CAS.Undetermined
const _inf, _sup = IA.inf, IA.sup

@variables x y z
myf(v) = v
@register_symbolic myf(v)          # an op the HC4 tape does not know -> constraint is "dropped"

# ----- constructors ---------------------------------------------------
bi(a, b) = CAS._bi(a, b)
bi(a) = CAS._bi(a)
boxof(ivs...) = CAS._make_box(CAS._BI[ivs...])
ivof(B, i) = CAS._bi(B[i])
mk(e, op) = CAS.SymRelation(e, op)
C(e, op) = CAS.Constraint(mk(e, op))                 # residual `e` ⋈ 0
cons(cs...) = collect(CAS.Constraint, cs)
mkcomp(cs) = only(CAS.constraint_components(cs))     # a list that forms exactly one block
evalf(e, kv...) = CAS._const_value(Symbolics.substitute(e, Dict(kv...)))

# ----- interval predicates (IntervalArithmetic's own, never ==/in/isempty)
iv_eq(a, b) = IA.isequal_interval(a, b)
iv_empty(a) = IA.isempty_interval(a)
iv_in(v, a) = IA.in_interval(v, a)
iv_sub(a, b) = IA.issubset_interval(a, b)
ivs_eq(A, B) = length(A) == length(B) && all(iv_eq(p, q) for (p, q) in zip(A, B))
rand_in(rng, iv) = _inf(iv) + (_sup(iv) - _inf(iv)) * rand(rng)

# ----- symbolic-safe helpers (never `==`/`in` on symbolic values) ------
symin(v, vs) = any(w -> isequal(v, w), vs)
varnames(vs) = sort(string.(vs))

# ----- Evidence helpers --------------------------------------------------
# `outer` holds intervals, so compare it with `isequal_interval`; the rest
# are Bools / enums.
same(a::CAS.Evidence, b::CAS.Evidence) =
    iv_eq(a.outer, b.outer) &&
        all(f -> isequal(getfield(a, f), getfield(b, f)),
        (:strict_lo, :strict_hi, :neg, :zero, :pos, :ident_zero))
ans3(e) = (e.neg, e.zero, e.pos)

# ----- global-state helpers ----------------------------------------------
function with_env(f; tol=CAS.tolerance[], mvf=CAS.mvf_enabled[])
    t0, m0 = CAS.tolerance[], CAS.mvf_enabled[]
    CAS.tolerance[] = tol
    CAS.mvf_enabled[] = mvf
    try
        return f()
    finally
        CAS.tolerance[] = t0
        CAS.mvf_enabled[] = m0
    end
end
fresh(f) = (CAS.clear_cache!(); f())

const RELS = [CAS._LT, CAS._LE, CAS._GT, CAS._GE, CAS._EQ, CAS._NE]
end

# ===========================================================================
#                         types.jl / utils.jl
# ===========================================================================
@testitem "types: SymRelation and Constraint construction" tags=[:types] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "relation symbol and type" begin
        r = mk(x - 1, >=)
        @test r.relation === CAS._GE
        @test r.type === :i                         # `x` is a bare independent variable
        @test C(x, >).relation.relation === CAS._GT
        @test mk(Num(1), >).type === :t             # trivially true
        @test mk(Num(-1), >).type === :f            # false
        @test mk(Num(0), ==).type === :t
        @test mk(Num(0), >).type === :f
        @test_throws ArgumentError CAS.SymRelation(Num(1), CAS._GT, :bogus, UInt64(0))
    end

    @testset "canonical form (content hash is scale-invariant)" begin
        @test mk(2x - 2, >=).key == mk(x - 1, >=).key           # positive scale: same
        @test mk(1 - x, >=).relation === CAS._LE                # negative scale flips
        @test mk(1 - x, >=).key == mk(x - 1, <=).key
        @test mk(-2x + 2, >).key == mk(x - 1, <).key
        @test mk(x, ==).key == mk(-3x, ==).key                  # == and != flip to themselves
        @test mk(x, !=).key == mk(-x, !=).key
        @test mk(x, >=).key != mk(x, >).key                     # the relation is part of the key
        @test mk(x, >=).key != mk(y, >=).key
    end

    @testset "SymRelation(expr) parses a relation expression" begin
        # (`x > 1` is deliberately a *symbolic* value here: it is only ever passed on, never branched on)
        @test CAS.SymRelation(x > 1).relation === CAS._GT
        @test CAS.SymRelation(x > 1).key == mk(x - 1, >).key
        @test CAS.SymRelation(x <= y).relation === CAS._LE
        @test_throws ArgumentError CAS.SymRelation(x + 1)       # not a relation
        @test_throws ArgumentError CAS.SymRelation(x)           # not even a call
    end

    @testset "Constraint identity is bookkeeping, content is meaning" begin
        a, b = C(x - 1, >=), C(x - 1, >=)
        @test a.id != b.id
        @test CAS._ckey(a) == CAS._ckey(b)
        @test CAS._content_key(a) == CAS._content_key(b)
        @test CAS._constraint_sort_key(a) != CAS._constraint_sort_key(b)    # Id is the tie-break
        @test issorted([a, b]; by=CAS._constraint_sort_key)
        @test CAS._ckey(a) != CAS._ckey(C(x - 1, >))
        @test CAS.Constraint(x > 1).relation.relation === CAS._GT

        ids = [CAS.fresh_id() for _ in 1:50]
        @test allunique(ids) && issorted(ids)
        @test varnames(CAS.constraint_variables(C(x + y, >=))) == ["x", "y"]
    end

    @testset "_constraint_index binary search" begin
        rel = mk(x, >)
        cs = [CAS.Constraint(i, rel) for i in (2, 5, 9)]
        @test CAS._constraint_index(cs, 2) == 1
        @test CAS._constraint_index(cs, 5) == 2
        @test CAS._constraint_index(cs, 9) == 3
        @test CAS._constraint_index(cs, 4) == 0
        @test CAS._constraint_index(CAS.Constraint[], 1) == 0
    end

    @testset "_unchecked_domain" begin
        cs = [C(x - 1, >=), C(y, >)]
        dom = CAS._unchecked_domain(cs)
        @test length(dom.constraints) == 2
        @test isempty(dom.blocks) && isempty(dom.variables)
    end
end

@testitem "utils: symbolic-safe helpers" tags=[:utils] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "_in / _contains_equal never branch on a symbolic value" begin
        @test CAS._in(x, [y, x]) === true
        @test CAS._in(z, [y, x]) === false
        @test CAS._in(x + 1, [x + 1, y]) === true               # compound expression
        @test CAS._in(x, Set([x, y])) === true
        @test CAS._in(z, Set([x, y])) === false
        @test CAS._in(x, Dict(x => 1)) === true                 # keys
        @test CAS._in(z, Dict(x => 1)) === false
        @test CAS._contains_equal([x + 1, y], x + 1) === true
        @test CAS._contains_equal([x + 1, y], x + 2) === false
        @test varnames(filter(CAS._in([x, y]), [x, z, y])) == ["x", "y"]   # curried form
    end

    @testset "_push_unique! / _ordered_unique" begin
        arr = Any[x]
        CAS._push_unique!(arr, [x, y, y, z])
        @test string.(arr) == ["x", "y", "z"]
        @test string.(CAS._ordered_unique([x, y, x, z, y])) == ["x", "y", "z"]
        @test isempty(CAS._ordered_unique(Any[]))
    end

    @testset "_vars_of" begin
        @test varnames(CAS._vars_of(x + y * z)) == ["x", "y", "z"]
        @test isempty(CAS._vars_of(Num(3)))
        @test isempty(CAS._vars_of(3))
        @test CAS._vars_of(x) isa Vector{Symbolics.Num}
    end

    @testset "_const_value" begin
        @test CAS._const_value(Num(3)) == 3
        @test CAS._const_value(2.5) == 2.5
        @test CAS._const_value(1 // 3) == 1 // 3
        @test CAS._const_value(x) === nothing
        @test CAS._const_value(x + 1) === nothing
    end

    @testset "_numeric_factor / _inv" begin
        @test CAS._numeric_factor(3x) == 3
        @test CAS._numeric_factor(-2 * x * y) == -2
        @test CAS._numeric_factor(x) == 1
        @test CAS._numeric_factor(Num(5)) == 5
        @test CAS._numeric_factor(x + y) == 1
        @test CAS._inv(2) === 1 // 2
        @test CAS._inv(-1) === -1 // 1
        @test CAS._inv(0.5) == 2.0
    end

    @testset "_canonicalize" begin
        res, rel = CAS._canonicalize(Num(3), CAS._GT)           # no variable term: untouched
        @test isequal(res, Num(3)) && rel === CAS._GT
        @test CAS._canonicalize(-x + 1, CAS._GE)[2] === CAS._LE
        @test CAS._canonicalize(x + 1, CAS._GE)[2] === CAS._GE
        @test CAS._canonicalize(-x + 1, CAS._EQ)[2] === CAS._EQ
    end
end

@testitem "utils: relation helpers" tags=[:utils] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "tables" begin
        @test length(CAS._RELATIONS) == 6
        @test all(r -> r in CAS._RELATIONS, RELS)               # Symbols: `in` is safe here
        @test CAS._relation_symbol(>=) === CAS._GE
        @test CAS._relation_symbol(!=) === CAS._NE
        @test CAS._relation_symbol(Symbol("<")) === CAS._LT
        @test_throws ArgumentError CAS._relation_symbol(Symbol("<>"))
        @test_throws ArgumentError CAS._relation_symbol(+)
        err = try
            CAS._relation_symbol(+; error_message="custom:")
        catch e
            e
        end
        @test err isa ArgumentError && occursin("custom:", err.msg)
        @test_throws ArgumentError CAS._symbol_to_relation(:foo)
        @test CAS._get_relation(mk(x, >=)) === (>=)
    end

    @testset "three encodings of 'which residual signs satisfy the relation'" begin
        for r in RELS
            mask = CAS._rel_mask(r)
            op = CAS._symbol_to_relation(r)
            @test CAS._relation_symbol(op) === r
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
        @test_throws ArgumentError CAS._negate_relation(:foo)
        @test_throws ArgumentError CAS._rel_mask(:foo)
    end

    @testset "_STATUS_RULES = (redundant signs, infeasible signs)" begin
        rep = (neg=-1, zero=0, pos=1)
        for r in RELS
            redundant, infeasible = CAS._STATUS_RULES[r]
            for s in (:neg, :zero, :pos)
                @test (s in redundant) == !CAS._holds(r, rep[s])    # sign that violates r must be impossible
                @test (s in infeasible) == CAS._holds(r, rep[s])    # sign that satisfies r must be impossible
            end
        end
    end

    @testset "SymRelation <-> Equation, simplify/expand keep the relation" begin
        @test CAS._eq_from_rel(mk(x - 1, >=)) === nothing
        @test CAS._eq_from_rel(mk(x - 1, ==)) isa Symbolics.Equation
        r = mk((x + 1)^2 - 1, >=)
        @test Symbolics.expand(r) isa CAS.SymRelation
        @test Symbolics.expand(r).relation === r.relation
        @test Symbolics.simplify(r) isa CAS.SymRelation
        @test Symbolics.simplify(r).relation === r.relation
    end
end

@testitem "utils: keys and cache plumbing" tags=[:utils, :cache] setup=[SatSetup] begin
    using Symbolics, Random
    CAS.clear_cache!()
    comp = mkcomp([C(x - 1, >=)])
    comps = CAS.constraint_components([C(x - 1, >=), C(y, >)])
    u = Symbolics.unwrap(x)

    @test CAS._pkey(CAS.Constraint[]) == ()
    @test CAS._ctx_key(comp) == (comp.key, ())
    @test CAS._ctx_key(comps) == ((c.key for c in comps)..., ())
    @test CAS._ctx_key(comps, CAS.Constraint[]) == CAS._ctx_key(comps)
    @test CAS._comp_key([UInt64(1), UInt64(2)]) == hash((UInt64(1), UInt64(2)))
    @test CAS._EMPTY_CTX.key == () && isempty(CAS._EMPTY_CTX.comps)

    # keys that contain a symbolic value are compared with isequal, never ==
    @test isequal(CAS._ekey(u, (1,)), (:evidence, u, (1,), CAS._env()))
    @test !isequal(CAS._ekey(u, (1,)), CAS._ekey(u, (2,)))
    @test CAS._fkey(comp) == (:comp, comp.key, CAS._env())
    @test CAS._hkey(comp) == (:hc4, comp.key, CAS._env())
    @test CAS._fkey(comp) != CAS._hkey(comp)

    @testset "the environment is part of every key" begin
        @test CAS._env() == (CAS.tolerance[], CAS.mvf_enabled[])
        k_tol = with_env(() -> CAS._ekey(u, (1,)); tol=CAS.tolerance[] / 2 + 0.3)
        @test !isequal(CAS._ekey(u, (1,)), k_tol)
        k_mvf = with_env(() -> CAS._fkey(comp); mvf=(!CAS.mvf_enabled[]))
        @test CAS._fkey(comp) != k_mvf
    end

    @testset "clear / resize" begin
        CAS.cache[:probe] = 1
        CAS.clear_cache!()
        @test !haskey(CAS.cache, :probe)
        old = CAS.cache_size[]
        try
            CAS.resize_cache!(5)
            @test CAS.cache_size[] == 5
            for i in 1:10
                CAS.cache[i] = i
            end
            @test length(CAS.cache) <= 5
        finally
            CAS.resize_cache!(old)
            CAS.clear_cache!()
        end
        @test CAS.cache_size[] == old
    end
end

# ===========================================================================
#                              satisfiability.jl
# ===========================================================================
@testitem "sat: sign algebra" tags=[:satisfiability, :signs] setup=[SatSetup] begin
    using Symbolics, Random
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
    ev(s) = CAS.Evidence(neg=s.neg ? Undetermined : No, zero=s.zero ? Undetermined : No, pos=s.pos ? Undetermined : No)

    @testset "_signs / _hasvals" begin
        @test CAS._signs(CAS.Evidence()) == CAS._ANY_SIGN
        @test CAS._signs(CAS.Evidence(neg=No, zero=No, pos=Yes)) == CAS._Signs(false, false, true)
        @test CAS._hasvals(CAS._Signs(false, true, false))
        @test !CAS._hasvals(CAS._Signs(false, false, false))
    end

    @testset "+ and * are sound and exact" begin
        for a in sets, b in sets, (f, g) in ((CAS._s_add, +), (CAS._s_mul, *))
            r = f(a, b)
            actual = Symbol[signof(g(va, vb)) for va in reps(a) for vb in reps(b)]
            for s in actual
                @test getfield(r, s)
            end
            @test r == present(actual)
        end
    end

    @testset "neg / inv / integer powers are sound" begin
        for a in sets, va in reps(a)
            @test inset(CAS._s_neg(a), -va)
            va != 0 && @test inset(CAS._s_inv(a), 1 / va)
            for n in -3:4
                (n < 0 && va == 0) && continue
                @test inset(CAS._s_powint(a, n), va^n)
            end
        end
    end

    @testset "constant real exponent" begin
        for a in sets, va in reps(a), p in (-3.0, -2.0, -0.5, 0.0, 0.5, 1.0, 2.5, 3.0)
            (va < 0 && !isinteger(p)) && continue      # undefined
            (va == 0 && p < 0) && continue             # undefined
            @test inset(CAS._s_pow(a, p), va^p)
        end
    end

    @testset "signed exponent" begin
        for a in sets, b in sets, va in reps(a), vb in reps(b)
            (va < 0 && !isinteger(vb)) && continue
            (va == 0 && vb < 0) && continue
            @test inset(CAS._s_pow(a, b), va^vb)
        end
    end

    @testset "_sign_rule" begin
        P = CAS.Evidence(neg=No, zero=No, pos=Undetermined)      # strictly positive
        N = CAS.Evidence(neg=Undetermined, zero=No, pos=No)      # strictly negative
        A = CAS.Evidence()
        @test CAS._sign_rule(*, [x, y], [P, N]) == CAS._Signs(true, false, false)
        @test CAS._sign_rule(+, [x, y], [P, P]) == CAS._Signs(false, false, true)
        @test CAS._sign_rule(+, [x, y, z], [P, P, N]) == CAS._ANY_SIGN
        @test CAS._sign_rule(^, [x, Num(2)], [A]) == CAS._Signs(false, true, true)
        @test CAS._sign_rule(^, [x, y], [P, A]) == CAS._Signs(false, false, true)
        @test CAS._sign_rule(exp, [x], [A]) == CAS._Signs(false, false, true)
        @test CAS._sign_rule(abs, [x], [A]) == CAS._Signs(false, true, true)
        @test CAS._sign_rule(/, [x, y], [P, N]) == CAS._Signs(true, false, false)
        @test CAS._sign_rule(sin, [x], [A]) == CAS._ANY_SIGN
        # sound against sampling for the monotone / sign-preserving unary ops
        for op in (exp, exp2, exp10, cosh, sinh, tanh, atan, asinh, abs, sqrt)
            for a in sets, va in reps(a)
                (op === sqrt && va < 0) && continue
                @test inset(CAS._sign_rule(op, [x], [ev(a)]), op(va))
            end
        end
        for a in sets, b in sets
            @test CAS._sign_rule(+, [x, y], [ev(a), ev(b)]) == CAS._s_add(a, b)
            @test CAS._sign_rule(*, [x, y], [ev(a), ev(b)]) == CAS._s_mul(a, b)
        end
    end
end

@testitem "sat: interval, identity and combine rules" tags=[:satisfiability, :rules] setup=[SatSetup] begin
    using Symbolics, Random
    E(lo, hi; kw...) = CAS.Evidence(; outer=bi(lo, hi), kw...)
    Z = CAS._IDENT_ZERO
    P = CAS.Evidence(neg=No, zero=No, pos=Undetermined)
    A = CAS.Evidence()

    @testset "_interval_rule" begin
        o, slo, shi = CAS._interval_rule(+, [x, y], [E(1.0, 2.0; strict_lo=true), E(3.0, 4.0)])
        @test iv_eq(o, bi(4.0, 6.0)) && slo && !shi
        o, slo, shi = CAS._interval_rule(*, [x, y], [E(-1.0, 2.0), E(3.0, 4.0)])
        @test iv_eq(o, bi(-4.0, 8.0)) && !slo && !shi
        o, slo, shi = CAS._interval_rule(-, [x], [E(1.0, 2.0; strict_lo=true)])
        @test iv_eq(o, bi(-2.0, -1.0)) && !slo && shi            # negation swaps strictness
        o, slo, shi = CAS._interval_rule(-, [x, y], [E(1.0, 2.0; strict_lo=true), E(0.0, 1.0; strict_hi=true)])
        @test iv_eq(o, bi(0.0, 2.0)) && slo && !shi
        o, _, _ = CAS._interval_rule(/, [x, y], [E(1.0, 2.0), E(2.0, 4.0)])
        @test iv_in(0.25, o) && iv_in(1.0, o)
        o, _, _ = CAS._interval_rule(^, [x, Num(2)], [E(-3.0, 2.0)])
        @test _inf(o) >= 0 && _sup(o) >= 9                        # even power: no dependency loss
        o, _, _ = CAS._interval_rule(^, [x, y], [E(2.0, 3.0), E(1.0, 2.0)])
        @test iv_in(2.0, o) && iv_in(9.0, o)
        o, _, _ = CAS._interval_rule(exp, [x], [E(0.0, 1.0)])
        @test iv_in(1.0, o) && iv_in(exp(1.0), o)
        o, _, _ = CAS._interval_rule(sqrt, [x], [E(0.0, 4.0)])
        @test iv_in(0.0, o) && iv_in(2.0, o)
        o, slo, shi = CAS._interval_rule(floor, [x], [E(0.0, 4.0)])   # no rule: top
        @test iv_eq(o, CAS._entire_bi()) && !slo && !shi
    end

    @testset "_ident_rule" begin
        @test CAS._ident_rule(*, [x, y], [Z, P])
        @test !CAS._ident_rule(+, [x, y], [Z, P])
        @test CAS._ident_rule(+, [x, y], [Z, Z])
        @test CAS._ident_rule(/, [x, y], [Z, P])
        @test !CAS._ident_rule(/, [x, y], [P, Z])
        @test !CAS._ident_rule(/, [x, y], [Z, Z])
        @test CAS._ident_rule(^, [x, Num(2)], [Z])
        @test !CAS._ident_rule(^, [x, Num(-1)], [Z])
        @test CAS._ident_rule(sin, [x], [Z])
        @test !CAS._ident_rule(cos, [x], [Z])
        @test !CAS._ident_rule(exp, [x], [Z])
        @test !CAS._ident_rule(+, CAS.Num[], CAS.Evidence[])
    end

    @testset "_lit_interval / _literal_evidence" begin
        @test iv_eq(CAS._lit_interval(3), bi(3.0, 3.0))
        o = CAS._lit_interval(1 // 3)
        @test iv_in(1 / 3, o) && _sup(o) > _inf(o)               # widened by an ulp
        o = CAS._lit_interval(pi)
        @test _inf(o) < Float64(pi) < _sup(o)
        @test same(CAS._literal_evidence(0), CAS._IDENT_ZERO)
        @test ans3(CAS._literal_evidence(2.5)) == (No, No, Yes)
        @test ans3(CAS._literal_evidence(-1.5)) == (Yes, No, No)
        @test same(CAS._literal_evidence(Inf), CAS.Evidence())
        @test same(CAS._literal_evidence(NaN), CAS.Evidence())
    end

    @testset "_combine" begin
        @test same(CAS._combine(+, [x, y], [CAS._EMPTY_EVIDENCE, P]), CAS._EMPTY_EVIDENCE)
        @test same(CAS._combine(*, [x, y], [Z, A]), CAS._IDENT_ZERO)
        e = CAS._combine(+, [Num(1), Num(2)], [CAS._literal_evidence(1), CAS._literal_evidence(2)])
        @test iv_eq(e.outer, bi(3.0, 3.0))
        @test ans3(e) == (No, No, Undetermined)          # sound, but no existence claim without a witness
        e = CAS._combine(exp, [x], [A])
        @test ans3(e) == (No, No, Undetermined) && e.strict_lo
        e = CAS._combine(sin, [x], [A])
        @test _inf(e.outer) >= -1 && _sup(e.outer) <= 1
        @test ans3(e) == (Undetermined, Undetermined, Undetermined)
    end

    @testset "_infer_evidence uses the cache and never paves" begin
        CAS.clear_cache!()
        u = Symbolics.unwrap(x)
        @test same(CAS._infer_evidence(u, CAS._EMPTY_CTX), CAS.Evidence())
        @test ans3(CAS._infer_evidence(Symbolics.unwrap(x + 1), CAS._EMPTY_CTX)) == (Undetermined, Undetermined, Undetermined)
        @test same(CAS._infer_evidence(Symbolics.unwrap(Num(3)), CAS._EMPTY_CTX), CAS._literal_evidence(3))
        CAS.clear_cache!()
        decided = CAS._tighten(CAS.Evidence(outer=bi(1.0, 2.0), pos=Yes))
        CAS._store!(u, CAS._EMPTY_CTX.key, decided)
        @test same(CAS._infer_evidence(u, CAS._EMPTY_CTX), decided)     # fully decided hit is returned as is
    end
end

# everything up to here works!

@testitem "sat: Evidence helpers and lattice" tags=[:satisfiability, :evidence] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "_answer / _decided / _with / _set_answer" begin
        e = CAS.Evidence(neg=No, zero=Yes, pos=Undetermined)
        @test CAS._answer(e, :neg) === No && CAS._answer(e, :zero) === Yes && CAS._answer(e, :pos) === Undetermined
        @test CAS._decided(e, (:neg, :zero))
        @test !CAS._decided(e, CAS._ALL)
        @test CAS._decided(e, ())
        e2 = CAS._with(e; pos=No)
        @test ans3(e2) == (No, Yes, No) && iv_eq(e2.outer, e.outer)
        @test ans3(CAS._set_answer(e, :neg, Yes)) == (Yes, Yes, Undetermined)
        @test ans3(CAS._set_answer(e, :pos, Yes)) == (No, Yes, Yes)
    end

    @testset "conversions" begin
        @test CAS._to_answer(:sat) === Yes
        @test CAS._to_answer(:unsat) === No
        @test CAS._to_answer(:Undetermined) === Undetermined
        @test CAS._to_answer(:whatever) === Undetermined
        @test CAS._rel_from_want(:neg) === CAS._LT
        @test CAS._rel_from_want(:zero) === CAS._EQ
        @test CAS._rel_from_want(:pos) === CAS._GT
        @test_throws ErrorException CAS._rel_from_want(:foo)
    end

    @testset "_join" begin
        for a in (Yes, No, Undetermined)
            @test CAS._join(a, a) === a
            @test CAS._join(a, Undetermined) === a
            @test CAS._join(Undetermined, a) === a
        end
        @test CAS._join(Yes, No) === No
        @test CAS._join(No, Yes) === No
    end

    @testset "_seed_evidence" begin
        @test ans3(CAS._seed_evidence(CAS._LT)) == (Yes, No, No)
        @test ans3(CAS._seed_evidence(CAS._LE)) == (Undetermined, Undetermined, No)
        @test ans3(CAS._seed_evidence(CAS._GT)) == (No, No, Yes)
        @test ans3(CAS._seed_evidence(CAS._GE)) == (No, Undetermined, Undetermined)
        @test ans3(CAS._seed_evidence(CAS._EQ)) == (No, Yes, No)
        @test ans3(CAS._seed_evidence(CAS._NE)) == (Undetermined, No, Undetermined)
        e = CAS._seed_evidence(CAS._EQ)
        @test iv_eq(e.outer, bi(0.0, 0.0))
    end

    @testset "_tighten" begin
        t = CAS._tighten(CAS.Evidence(outer=bi(1.0, 2.0)))
        @test ans3(t) == (No, No, Undetermined)
        t = CAS._tighten(CAS.Evidence(outer=bi(-Inf, 0.0), strict_hi=true))
        @test ans3(t) == (Undetermined, No, No)
        @test same(CAS._tighten(CAS.Evidence(outer=bi(1.0, 2.0), pos=No)), CAS._EMPTY_EVIDENCE)
        @test same(CAS._tighten(CAS.Evidence(outer=CAS._empty_bi())), CAS._EMPTY_EVIDENCE)
        @test same(CAS._tighten(CAS.Evidence(neg=No, zero=No, pos=No)), CAS._EMPTY_EVIDENCE)
        @test same(CAS._tighten(CAS.Evidence(ident_zero=true)), CAS._IDENT_ZERO)
        @test same(CAS._tighten(CAS.Evidence(outer=bi(0.0, 0.0), strict_lo=true)), CAS._EMPTY_EVIDENCE)
        # answers shrink the interval
        t = CAS._tighten(CAS.Evidence(outer=bi(-3.0, 4.0), neg=No))
        @test iv_eq(t.outer, bi(0.0, 4.0))
        t = CAS._tighten(CAS.Evidence(outer=bi(-3.0, 4.0), pos=No))
        @test iv_eq(t.outer, bi(-3.0, 0.0))
        t = CAS._tighten(CAS.Evidence(outer=bi(0.0, 2.0), zero=No))
        @test t.strict_lo && ans3(t) == (No, No, Undetermined)
        # idempotent
        for e in (CAS.Evidence(), CAS._seed_evidence(CAS._LE), CAS._seed_evidence(CAS._NE),
            CAS.Evidence(outer=bi(-3.0, 4.0)), CAS.Evidence(outer=bi(-3.0, 4.0), neg=No))
            t1 = CAS._tighten(e)
            @test same(CAS._tighten(t1), t1)
        end
    end

    @testset "_merge" begin
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
                if !iv_empty(m.outer)                                     # only ever shrinks
                    @test iv_sub(m.outer, a.outer) && iv_sub(m.outer, b.outer)
                end
            end
        end
        @test same(CAS._merge(CAS._seed_evidence(CAS._LT), CAS._seed_evidence(CAS._GE)), CAS._EMPTY_EVIDENCE)
        @test same(CAS._merge(CAS._seed_evidence(CAS._LT), CAS._seed_evidence(CAS._GT)), CAS._EMPTY_EVIDENCE)
        m = CAS._merge(CAS._seed_evidence(CAS._LE), CAS._seed_evidence(CAS._GE))
        @test iv_eq(m.outer, bi(0.0, 0.0)) && m.neg === No && m.pos === No
        @test same(CAS._merge(CAS.Evidence(outer=bi(0.0, 1.0)), CAS.Evidence(outer=bi(2.0, 3.0))), CAS._EMPTY_EVIDENCE)
        @test same(CAS._merge(CAS._seed_evidence(CAS._GT), CAS._IDENT_ZERO), CAS._IDENT_ZERO)
    end

    @testset "_store! merges into the cache" begin
        CAS.clear_cache!()
        u = Symbolics.unwrap(x)
        CAS._store!(u, (1,), CAS.Evidence(outer=bi(0.0, Inf)))
        e = CAS._store!(u, (1,), CAS.Evidence(outer=bi(-Inf, 5.0)))
        @test iv_eq(e.outer, bi(0.0, 5.0))
        @test same(CAS.cache[CAS._ekey(u, (1,))], e)
        @test !haskey(CAS.cache, CAS._ekey(u, (2,)))          # other contexts do not see it
    end
end

@testitem "sat: affine extraction and bound tightening" tags=[:satisfiability, :affine] setup=[SatSetup] begin
    using Symbolics, Random
    na(e, v=x) = CAS._numeric_affine(e, v)

    @testset "_numeric_affine" begin
        @test na(2x + 3) == (2.0, 3.0)
        @test na(x - 1) == (1.0, -1.0)
        @test na(3 - 2x) == (-2.0, 3.0)
        @test na((x + 1) / 2) == (0.5, 0.5)
        @test na(2 * (x - 1)) == (2.0, -2.0)
        @test na(x * y + 1) === nothing          # coefficient is not a number
        @test na(x^2) === nothing
        @test na(sin(x)) === nothing
        @test na(x / y) === nothing
        @test na(y + 1) === nothing              # x does not occur
        @test na(Num(3)) === nothing
        @test na(y - 2, y) == (1.0, -2.0)
        @test CAS._affine_coefficients(y, x) === nothing
        @test isequal(CAS._affine_coefficients(x + y, x)[1], 1)
    end

    @testset "_tighten_bound!" begin
        b = CAS._Bnd()
        @test CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)       # x - 1 >= 0
        @test b.lo == 1.0 && !b.slo && b.hi == Inf
        b = CAS._Bnd()                                          # -x + 3 > 0  <=>  x < 3
        @test CAS._tighten_bound!(b, -1.0, 3.0, CAS._GT)
        @test b.hi == 3.0 && b.shi && b.lo == -Inf
        b = CAS._Bnd()
        @test CAS._tighten_bound!(b, 1.0, -2.0, CAS._EQ)
        @test b.lo == 2.0 && b.hi == 2.0 && !b.slo && !b.shi
        b = CAS._Bnd()
        @test CAS._tighten_bound!(b, -2.0, 4.0, CAS._EQ)       # negative coefficient, equality
        @test b.lo == 2.0 && b.hi == 2.0
        b = CAS._Bnd()
        CAS._tighten_bound!(b, 1.0, -2.0, CAS._GT)             # x > 2
        @test !CAS._tighten_bound!(b, 1.0, -1.0, CAS._LT)      # x < 1
        b = CAS._Bnd()
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)
        @test CAS._tighten_bound!(b, 1.0, -1.0, CAS._LE)       # closed touching point is feasible
        b = CAS._Bnd()
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._GT)
        @test !CAS._tighten_bound!(b, 1.0, -1.0, CAS._LE)      # one open side is not
        b = CAS._Bnd()
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._GT)
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)
        @test b.slo                                            # strictness never lost
        b = CAS._Bnd()
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._GE)
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._GT)
        @test b.slo
        b = CAS._Bnd()
        CAS._tighten_bound!(b, 1.0, -1.0, CAS._LE)
        CAS._tighten_bound!(b, 1.0, -5.0, CAS._LE)
        @test b.hi == 1.0                                      # a looser bound never loosens
        b = CAS._Bnd()
        @test CAS._tighten_bound!(b, 1.0, 0.0, CAS._NE)        # != carries no interval information
        @test b.lo == -Inf && b.hi == Inf
    end

    @testset "_bound_evidence" begin
        e = CAS._bound_evidence(CAS._Bnd(1.0, Inf, false, false), true)
        @test ans3(e) == (No, No, Yes)
        e = CAS._bound_evidence(CAS._Bnd(1.0, Inf, false, false), false)   # not exact: no existence claims
        @test e.pos === Undetermined && e.neg === No
        e = CAS._bound_evidence(CAS._Bnd(-1.0, 1.0, false, false), true)
        @test ans3(e) == (Yes, Yes, Yes)
        e = CAS._bound_evidence(CAS._Bnd(0.0, 1.0, true, false), true)     # (0, 1]: zero is excluded
        @test ans3(e) == (No, No, Yes)
        e = CAS._bound_evidence(CAS._Bnd(0.0, 0.0, false, false), true)    # the point 0
        @test ans3(e) == (No, Yes, No)
        e = CAS._bound_evidence(CAS._Bnd(0.0, Inf, false, false), true)    # [0, ∞)
        @test e.neg === No && e.zero === Yes && e.pos === Yes
    end

    @testset "_bounded" begin
        @test CAS._bounded(boxof(bi(0.0, 1.0), bi(-2.0, 3.0)))
        @test !CAS._bounded(boxof(bi(0.0, Inf)))
        @test !CAS._bounded(boxof(bi(0.0, 1.0), bi(-Inf, 3.0)))
    end
end

@testitem "sat: components and contexts" tags=[:satisfiability, :components] setup=[SatSetup] begin
    using Symbolics, Random
    cs = [C(x, >=), C(y, >=), C(x + y - 1, <=), C(z, >)]

    @testset "_connected_groups" begin
        g = CAS._connected_groups(cs)
        @test length(g) == 2
        @test sort(length.(getfield.(g, :constraints))) == [1, 3]
        @test Set(Tuple(varnames(h.variables)) for h in g) == Set([("x", "y"), ("z",)])
        g2 = CAS._connected_groups(reverse(cs))                  # order independent
        @test [h.keys for h in g] == [h.keys for h in g2]
        gd = CAS._connected_groups([C(x - 1, >=), C(x - 1, >=)]) # same content, different Ids
        @test length(gd) == 1 && length(gd[1].constraints) == 1
        gs = CAS._connected_groups([C(x - 1, >=), C(2x - 2, >=)])  # same after canonicalization
        @test length(gs) == 1 && length(gs[1].constraints) == 1
        @test length(CAS._connected_groups([C(x, >=), C(x, >)])[1].constraints) == 2
        gc = CAS._connected_groups([C(Num(1), >), C(Num(2), >)]) # variable-free: one group each
        @test length(gc) == 2 && all(h -> isempty(h.variables), gc)
        @test isempty(CAS._connected_groups(CAS.Constraint[]))
    end

    @testset "constraint_components" begin
        comps = CAS.constraint_components(cs)
        @test comps isa Vector{CAS.Comp}
        @test length(comps) == 2
        @test issorted([c.key for c in comps])
        @test CAS.constraint_components(comps) === comps
        shuffled = Random.shuffle(MersenneTwister(1), cs)
        @test [c.key for c in CAS.constraint_components(shuffled)] == [c.key for c in comps]
        dom = CAS._unchecked_domain(cs)
        @test [c.key for c in CAS.constraint_components(dom)] == [c.key for c in comps]
        @test CAS.constraint_components([C(x - 1, >=)])[1].key == CAS.constraint_components([C(x - 1, >=)])[1].key
        @test isempty(CAS.constraint_components(CAS.Constraint[]))
    end

    @testset "contexts" begin
        comps = CAS.constraint_components([C(x, >=), C(y, >=)])
        ctx = CAS._ctx_for(comps, [x])
        @test length(ctx.comps) == 1 && symin(x, ctx.comps[1].variables)
        @test ctx.key == CAS._ctx_key(ctx.comps[1])
        @test isempty(CAS._ctx_for(comps, [z]).comps)
        ctx2 = CAS._ctx_for(comps, [x, y])
        @test length(ctx2.comps) == 2 && ctx2.key == CAS._ctx_key(comps)
        @test length(CAS._restrict_ctx(ctx2, x + 1).comps) == 1
        @test CAS._restrict_ctx(ctx2, Num(3)) === CAS._EMPTY_CTX
        @test CAS._restrict_ctx(CAS._EMPTY_CTX, x) === CAS._EMPTY_CTX
        @test length(CAS._ctx_constraints(ctx2)) == 2
    end
end

@testitem "sat: component facts" tags=[:satisfiability, :facts] setup=[SatSetup] begin
    using Symbolics, Random
    CAS.clear_cache!()

    @testset "exact block of univariate affine constraints" begin
        comp = mkcomp([C(x - 1, >=), C(3 - x, >=)])
        f = CAS._compute_facts(comp)
        @test f.exact && f.feasible
        @test CAS._facts(comp) === f
        ev = CAS._leaf_evidence(x, comp)
        @test iv_eq(ev.outer, bi(1.0, 3.0))
        @test ans3(ev) == (No, No, Yes)
    end

    @testset "strict and degenerate bounds" begin
        ev = CAS._leaf_evidence(x, mkcomp([C(x, >), C(1 - x, >)]))
        @test ev.strict_lo && ev.strict_hi && ans3(ev) == (No, No, Yes)
        ev = CAS._leaf_evidence(x, mkcomp([C(x - 1, >=), C(1 - x, >=)]))     # the point 1
        @test iv_eq(ev.outer, bi(1.0, 1.0)) && ans3(ev) == (No, No, Yes)
    end

    @testset "inexact block: bounds are sound but make no existence claims" begin
        comp = mkcomp([C(x^2 + y^2 - 1, <=)])
        f = CAS._compute_facts(comp)
        @test !f.exact && f.feasible
        @test ans3(CAS._leaf_evidence(x, comp)) == (Undetermined, Undetermined, Undetermined)
        comp = mkcomp([C(x - 1, >=), C(x * y - 2, <=)])
        @test !CAS._compute_facts(comp).exact
        ev = CAS._leaf_evidence(x, comp)                         # x >= 1 is still used
        @test ev.neg === No && ev.zero === No && ev.pos === Undetermined
        @test !CAS._compute_facts(mkcomp([C(x, !=)])).exact      # != is never exact
    end

    @testset "infeasible block" begin
        comp = mkcomp([C(x - 2, >=), C(1 - x, >=)])
        @test !CAS._compute_facts(comp).feasible
        @test same(CAS._leaf_evidence(x, comp), CAS._EMPTY_EVIDENCE)
    end

    @testset "constant constraints" begin
        f = CAS._compute_facts(mkcomp([C(Num(1), >)]))
        @test f.exact && f.feasible
        @test !CAS._compute_facts(mkcomp([C(Num(-1), >)])).feasible
    end
end

@testitem "sat: component facts are published under the key lookups use" tags=[:satisfiability, :facts, :cache] setup=[SatSetup] begin
    using Symbolics, Random
    # `_leaf_evidence` / `_infer_evidence` read evidence under `_ctx_key(comp)`;
    # `_compute_facts` must therefore write it there.
    CAS.clear_cache!()
    comp = mkcomp([C(x - 1, >=), C(3 - x, >=)])
    CAS._compute_facts(comp)
    @test haskey(CAS.cache, CAS._ekey(Symbolics.unwrap(x), CAS._ctx_key(comp)))
    for c in comp.constraints            # each constraint's own residual is seeded
        @test haskey(CAS.cache, CAS._ekey(Symbolics.unwrap(c.relation.residual), CAS._ctx_key(comp)))
    end
    @test CAS._ctx_for([comp], [x]).key == CAS._ctx_key(comp)
    # the consequence users care about
    @test fresh(() -> CAS.is_positive(x, [C(x, >)]))
end

@testitem "sat: _hc4_refine! and _joint_system" tags=[:satisfiability, :hc4] setup=[SatSetup] begin
    using Symbolics, Random
    CAS.clear_cache!()

    @testset "exact block short-circuits to :sat on its affine box" begin
        comp = mkcomp([C(x - 1, >=), C(3 - x, >=)])
        r = CAS._hc4_refine!(comp)
        @test r.status === :sat && ivs_eq(r.box, [bi(1.0, 3.0)])
        @test r.prep === CAS._NO_TAPES
    end

    @testset "inexact block contracts and publishes bounds" begin
        comp = mkcomp([C(x^2 + y^2 - 1, <=)])
        r = CAS._hc4_refine!(comp)
        @test r.status === :unknown
        for iv in r.box
            @test _inf(iv) >= -1 - 1e-9 && _sup(iv) <= 1 + 1e-9
        end
        ev = CAS.cache[CAS._ekey(Symbolics.unwrap(x), CAS._ctx_key(comp))]
        @test _inf(ev.outer) >= -1 - 1e-9 && _sup(ev.outer) <= 1 + 1e-9
        @test CAS._hc4_refine!(comp) === r                      # cached
    end

    @testset "HC4-infeasible block is recorded as infeasible" begin
        comp = mkcomp([C(x^2 + 1, <=)])
        r = CAS._hc4_refine!(comp)
        @test r.status === :unsat && all(iv_empty, r.box)
        @test !CAS._facts(comp).feasible
        @test same(CAS.cache[CAS._ekey(Symbolics.unwrap(x), CAS._ctx_key(comp))], CAS._EMPTY_EVIDENCE)
    end

    @testset "affine-infeasible block" begin
        r = CAS._hc4_refine!(mkcomp([C(x - 2, >=), C(1 - x, >=)]))
        @test r.status === :unsat
    end

    @testset "_joint_system" begin
        comps = CAS.constraint_components([C(x - 1, >=), C(3 - x, >=), C(y, >=)])
        sys = CAS._joint_system(comps, CAS.Constraint[], [z])
        @test sys !== nothing
        @test varnames(sys.variables) == ["x", "y", "z"]
        iz = findfirst(v -> isequal(v, z), sys.variables)
        @test iv_eq(sys.ivs[iz], CAS._entire_bi())              # free variable: unbounded
        @test length(sys.constraints) == 3 && length(sys.ivs) == 3
        sys = CAS._joint_system(comps, CAS.Constraint[], [x])   # already owned: not added twice
        @test length(sys.variables) == 2
        bad = CAS.constraint_components([C(x - 2, >=), C(1 - x, >=)])
        @test CAS._joint_system(bad, CAS.Constraint[], CAS.Num[]) === nothing
    end
end

@testitem "sat: satisfiable" tags=[:satisfiability, :sat] setup=[SatSetup] begin
    using Symbolics, Random
    sat(cs) = fresh(() -> CAS.satisfiable(cs))

    @testset "affine" begin
        @test sat(CAS.Constraint[]) === Yes
        @test sat([C(x - 1, >=), C(2 - x, >=)]) === Yes
        @test sat([C(x - 2, >=), C(1 - x, >=)]) === No
        @test sat([C(x - 1, >=), C(1 - x, >=)]) === Yes           # closed point
        @test sat([C(x - 1, >), C(1 - x, >=)]) === No             # open at the touching end
        @test sat([C(x - 1, >), C(2 - x, >)]) === Yes
        @test sat([C(x, >)]) === Yes
    end

    @testset "constants" begin
        @test sat([C(Num(1), >)]) === Yes
        @test sat([C(Num(-1), >)]) === No
        @test sat([C(Num(0), ==)]) === Yes
    end

    @testset "blocks are independent; the answer is their conjunction" begin
        ok = [C(x - 1, >=), C(2 - x, >=)]
        bad = [C(y, >), C(y + 1, <)]
        @test sat(vcat(ok, bad)) === No
        @test sat(vcat(bad, ok)) === No
        @test sat(vcat(ok, [C(y, >)])) === Yes
    end

    @testset "nonlinear" begin
        @test sat([C(x^2 + 1, <=)]) === No                        # HC4 must see x^2 >= 0
        @test sat([C(x^2 + y^2 - 1, <=)]) === Yes
        @test sat([C(x^2 + y^2 - 1, <=), C(x + y - 3, >=)]) === No   # HC4 contracts to [-1,1]^2, then x+y-3 < 0
        @test sat([C(x^2 - 2, ==)]) !== No                        # x = ±√2 exists
        @test sat([C(x + y - 2, ==), C(x - y, ==)]) !== No        # x = y = 1
        @test sat([C(exp(x) - y, <=), C(y, <=), C(y + 1, >=)]) === No   # exp(x) > 0 >= y
        @test sat([C(sin(x) - 2, >=)]) === No
        @test sat([C(x^2 - 1, >=)]) !== No                        # unbounded: may stay Unknown
    end

    @testset "constraints the tape cannot compile are dropped: never a false Yes" begin
        @test sat([C(myf(x), >), C(x - 1, <=), C(x + 1, >=), C(x * x - 3, <=)]) !== Yes
    end

    @testset "sources: vector, blocks, SymDomain (+ extra relations)" begin
        cs = [C(x - 1, >=), C(2 - x, >=)]
        @test CAS.satisfiable(CAS.constraint_components(cs)) === sat(cs)
        dom = CAS._unchecked_domain(cs)
        @test CAS.satisfiable(dom) === Yes
        @test CAS.satisfiable(dom, [mk(x - 3, >=)]) === No
        @test CAS.satisfiable(dom, [mk(x - 1.5, >=)]) === Yes
        @test CAS.satisfiable([C(x - 5, >=), C(2 - x, >=)]) === No   # no leakage from the previous queries
    end

    @testset "per-block answers are cached under the environment" begin
        CAS.clear_cache!()
        comp = mkcomp([C(x - 1, >=), C(2 - x, >=)])
        @test CAS._sat_comp(comp) === Yes
        @test CAS.cache[(:sat, comp.key, CAS._env())] === Yes
        k = with_env(() -> (:sat, comp.key, CAS._env()); tol=0.5)
        @test k != (:sat, comp.key, CAS._env())
    end
end

@testitem "sat: expr_evidence and sign predicates" tags=[:satisfiability, :evidence] setup=[SatSetup] begin
    using Symbolics, Random
    q(f, e, cs) = fresh(() -> f(e, cs))

    @testset "constants" begin
        cs = CAS.Constraint[]
        @test ans3(CAS.expr_evidence(Num(3), cs)) == (No, No, Yes)
        @test ans3(CAS.expr_evidence(Num(-2), cs)) == (Yes, No, No)
        e0 = CAS.expr_evidence(Num(0), cs)
        @test e0.zero === Yes && e0.neg === No && e0.pos === No
    end

    @testset "single variable, x > 0" begin
        cs = [C(x, >)]
        @test q(CAS.is_positive, x, cs) && q(CAS.is_nonzero, x, cs) && q(CAS.is_nonnegative, x, cs)
        @test !q(CAS.is_negative, x, cs)
        @test q(CAS.can_be_negative, x, cs) === No
        @test q(CAS.can_be_zero, x, cs) === No
        @test q(CAS.can_be_positive, x, cs) === Yes
        @test q(CAS.is_positive, x + 1, cs)
        @test q(CAS.is_positive, x * x, cs)
        @test q(CAS.is_positive, 1 / x, cs)
        @test q(CAS.is_positive, x^3, cs)
        @test q(CAS.is_negative, -x, cs)
        e = fresh(() -> CAS.expr_evidence(x - 1, cs))             # genuinely open: nothing may be ruled out
        @test e.neg !== No && e.zero !== No && e.pos !== No
        @test !q(CAS.is_positive, x - 1, cs) && !q(CAS.is_negative, x - 1, cs) && !q(CAS.is_nonzero, x - 1, cs)
    end

    @testset "closed / open boundaries" begin
        @test q(CAS.is_nonnegative, x - 1, [C(x - 1, >=)])
        @test !q(CAS.is_positive, x - 1, [C(x - 1, >=)])          # x = 1 gives 0
        @test !q(CAS.is_nonzero, x - 1, [C(x - 1, >=)])
        @test q(CAS.is_positive, x - 1, [C(x - 1, >)])
        @test q(CAS.is_nonzero, x - 1, [C(x - 2, >=)])
        @test q(CAS.is_nonpositive, x, [C(-x, >=)])
        @test q(CAS.is_negative, x, [C(-x, >)])
        @test !q(CAS.is_positive, x, [C(x, >=)]) && q(CAS.is_nonnegative, x, [C(x, >=)])
    end

    @testset "no constraints" begin
        cs = CAS.Constraint[]
        @test q(CAS.is_positive, exp(x), cs) && q(CAS.is_positive, cosh(x), cs)
        @test q(CAS.is_nonnegative, x^2, cs) && q(CAS.is_nonnegative, abs(x), cs)
        @test q(CAS.is_positive, x^2 + 1, cs)
        @test q(CAS.is_negative, sin(x) - 2, cs)
        @test !q(CAS.is_positive, x^2, cs) && !q(CAS.is_nonzero, x^2, cs)   # x = 0
        e = fresh(() -> CAS.expr_evidence(x, cs))
        @test e.neg !== No && e.pos !== No
    end

    @testset "several variables" begin
        cs = [C(x - 1, >=), C(y - 1, >=)]
        @test q(CAS.is_positive, x * y, cs) && q(CAS.is_positive, x + y, cs)
        @test q(CAS.can_be_negative, x - y, cs) !== No
        @test !q(CAS.is_nonnegative, x - y, cs)
        cs = [C(x, >)]
        @test !q(CAS.is_positive, y, cs)                           # unconstrained next to constrained
        @test q(CAS.can_be_negative, x * y, cs) !== No
        cs = [C(x - y, >=), C(y - 1, >=)]                          # coupled
        @test q(CAS.is_positive, x, cs)
        @test q(CAS.is_nonnegative, x - y, cs) || q(CAS.is_nonpositive, y - x, cs)
    end

    @testset "paving-backed decisions" begin
        disk = [C(x^2 + y^2 - 1, <=)]
        @test q(CAS.is_negative, x + y - 3, disk)                  # |x+y| <= √2
        @test q(CAS.can_be_negative, x + y - 3, disk) !== No
        @test q(CAS.can_be_positive, x + y - 3, disk) === No
        @test q(CAS.can_be_positive, x * y, disk) !== No
        @test q(CAS.can_be_negative, x^2 - 2 * x * y + y^2, disk) !== Yes   # (x-y)^2 is never negative
        @test q(CAS.can_be_zero, x^2 + y^2 - 1, disk) !== No       # the boundary is attainable
        e = fresh(() -> CAS.expr_evidence(x - 1, [C(x, >), C(3 - x, >)]))
        @test e.neg !== No && e.zero !== No && e.pos !== No
    end

    @testset "want only pursues what is asked" begin
        e = fresh(() -> CAS.expr_evidence(x, [C(x, >)]; want=(:neg,)))
        @test e.neg === No
    end

    @testset "sources: precomputed blocks and SymDomain agree with the vector" begin
        cs = [C(x - 1, >=), C(y - 1, >=), C(x + y - 10, <=)]
        comps = CAS.constraint_components(cs)
        dom = CAS._unchecked_domain(cs)
        for e in (x, x + y, x * y, x - y, x^2 - y)
            a = fresh(() -> CAS.expr_evidence(e, cs))
            @test same(a, fresh(() -> CAS.expr_evidence(e, comps)))
            @test same(a, fresh(() -> CAS.expr_evidence(e, dom)))
        end
    end
end

@testitem "sat: relation_status" tags=[:satisfiability, :status] setup=[SatSetup] begin
    using Symbolics, Random
    st(r, cs) = fresh(() -> CAS.relation_status(r, cs))

    @testset "x > 0" begin
        d = [C(x, >)]
        @test st(mk(x, >), d) === :redundant
        @test st(mk(x, >=), d) === :redundant
        @test st(mk(x, !=), d) === :redundant
        @test st(mk(x, <), d) === :infeasible
        @test st(mk(x, <=), d) === :infeasible
        @test st(mk(x, ==), d) === :infeasible
        @test st(mk(x - 1, >), d) === :active
        @test st(mk(x - 1, ==), d) === :active
        @test st(mk(x - 1, <=), d) === :active
    end

    @testset "x >= 0" begin
        d = [C(x, >=)]
        @test st(mk(x, >=), d) === :redundant
        @test st(mk(x, >), d) === :active          # x = 0 violates it
        @test st(mk(x, ==), d) === :active
        @test st(mk(x, <), d) === :infeasible
    end

    @testset "two variables" begin
        d = [C(x, >=), C(y, >=)]
        @test st(mk(x + y, >=), d) === :redundant
        @test st(mk(x * y + 1, >), d) === :redundant
        @test st(mk(x + y + 1, <), d) === :infeasible
        @test st(mk(x - y, >), d) === :active
    end

    @testset "constant relations" begin
        @test st(mk(Num(1), >), CAS.Constraint[]) === :redundant
        @test st(mk(Num(-1), >), CAS.Constraint[]) === :infeasible
        @test st(mk(Num(0), ==), CAS.Constraint[]) === :redundant
    end

    @testset "every constraint of a feasible context is redundant in it" begin
        for cs in ([C(x, >)], [C(x - 1, >=), C(3 - x, >=)], [C(x - y, >=), C(y - 1, >=)],
            [C(x^2 + y^2 - 1, <=)])
            for c in cs
                @test st(c.relation, cs) === :redundant
            end
        end
    end

    @testset "a relation and its negation swap redundant <-> infeasible" begin
        swap = Dict(:redundant => :infeasible, :infeasible => :redundant, :active => :active)
        for cs in ([C(x, >)], [C(x, >=), C(y, >=)], CAS.Constraint[])
            for e in (x, x - 1, x + y, x * y + 1, x^2), r in RELS
                a = st(mk(e, r), cs)
                b = st(mk(e, CAS._negate_relation(r)), cs)
                @test b === swap[a]
            end
        end
    end
end

@testitem "sat: strategy hook" tags=[:satisfiability, :pipeline] setup=[SatSetup] begin
    using Symbolics, Random
    strat(u, ctx, ev) = CAS._with(ev; neg=No)
    push!(CAS._STRATEGIES, strat)
    try
        e = fresh(() -> CAS.expr_evidence(x, CAS.Constraint[]; want=(:neg,)))
        @test e.neg === No                        # the strategy was consulted and its result merged
    finally
        empty!(CAS._STRATEGIES)
    end
    e = fresh(() -> CAS.expr_evidence(x, CAS.Constraint[]; want=(:neg,)))
    @test e.neg !== No
end

@testitem "sat: cache transparency and invariances" tags=[:satisfiability, :cache] setup=[SatSetup] begin
    using Symbolics, Random
    function battery(cs)
        (sat=CAS.satisfiable(cs),
            ev=[CAS.expr_evidence(e, cs) for e in (x, y, x + y, x * y, x^2 - y, x - y)],
            st=[CAS.relation_status(mk(e, r), cs) for e in (x - 1, y) for r in (CAS._GT, CAS._LE)])
    end
    same_battery(a, b) = a.sat === b.sat && a.st == b.st && all(same.(a.ev, b.ev))
    build() = [C(x - 1, >=), C(3 - x, >=), C(x + y - 2, <=), C(y, >)]

    ref = fresh(() -> battery(build()))
    @test ref.sat !== No                                              # the system is genuinely feasible
    @test same_battery(ref, battery(build()))                         # warm cache, new Ids
    rng = MersenneTwister(7)
    for _ in 1:5
        @test same_battery(ref, battery(Random.shuffle(rng, build())))
        @test same_battery(ref, fresh(() -> battery(Random.shuffle(rng, build()))))
    end

    old = CAS.cache_size[]
    try
        CAS.resize_cache!(8)                                          # a tiny cache must not change answers
        @test same_battery(ref, fresh(() -> battery(build())))
    finally
        CAS.resize_cache!(old)
    end

    with_env(tol=0.05) do                                             # other settings: never contradictory
        b = fresh(() -> battery(build()))
        @test b.sat !== No
        for (u, v) in zip(ref.ev, b.ev), w in (:neg, :zero, :pos)
            @test !(CAS._answer(u, w) === Yes && CAS._answer(v, w) === No)
            @test !(CAS._answer(u, w) === No && CAS._answer(v, w) === Yes)
        end
    end
end

@testitem "sat: randomized soundness against sampling" tags=[:satisfiability, :property, :slow] setup=[SatSetup] begin
    using Symbolics, Random
    rng = MersenneTwister(20261029)
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
                @test !iv_empty(ev.outer)                                   # feasible context
                for (px, py) in P
                    v = evalf(e, x => px, y => py)
                    (v === nothing || !isfinite(v)) && continue
                    tol = 1e-9 * (1 + abs(v))
                    @test _inf(ev.outer) - tol <= v <= _sup(ev.outer) + tol  # enclosure
                    ev.neg === No && @test v >= -tol
                    ev.pos === No && @test v <= tol
                    ev.zero === No && @test v != 0
                end
                # existence claims must at least be consistent with the enclosure
                ev.neg === Yes && @test _inf(ev.outer) < 0
                ev.pos === Yes && @test _sup(ev.outer) > 0
                ev.zero === Yes && @test iv_in(0.0, ev.outer)
            end
        end
    end
end

@testitem "sat: DESys helpers" tags=[:satisfiability, :sys] setup=[SatSetup] begin
    using Symbolics, Random
    @variables t a u(t)
    mksys(cs...) = CAS.DESys(Num[t], Num[u], Num[a], [], Symbolics.Equation[],
        CAS._unchecked_domain(collect(CAS.Constraint, cs)), CAS.Constraint[], CAS.Constraint[])
    CAS.clear_cache!()

    sys0 = mksys()
    @test CAS.factor_divisible(a, sys0)               # a parameter no constraint mentions: generically non-zero
    @test !CAS.factor_divisible(a + 1, sys0)
    sys1 = mksys(C(t, >=))
    @test CAS.factor_divisible(a, sys1)
    @test !CAS.factor_divisible(t, sys1)              # t = 0 is allowed
    @test CAS.factor_divisible(t, mksys(C(t - 1, >=)))
    @test CAS.factor_divisible(a, mksys(C(a, >)))     # mentioned, but provably non-zero
    @test !CAS.factor_divisible(a, mksys(C(a, >=)))

    sys2 = mksys(C(t - 1, >=))
    @test !CAS._can_divide_by(u, sys2)                       # a dependent variable
    @test !CAS._can_divide_by(Differential(t)(u), sys2)      # a derivative
    @test CAS._can_divide_by(t, sys2)
    @test CAS._can_divide_by(a, sys0)

    @test same(fresh(() -> CAS.factor_evidence(t, sys2)), fresh(() -> CAS.expr_evidence(t, sys2.domain)))

    cd = CAS.common_divisors(x * y + x * z, sys0)
    @test any(f -> isequal(f, x), cd)
    @test !any(f -> isequal(f, y), cd)
    @test isempty(CAS.common_divisors(x + y, sys0))
    @test all(f -> !(f isa Number), CAS.common_divisors(2 * x * y + 4 * x, sys0))
    @test_throws ArgumentError CAS.common_divisors(nothing, sys0)
end

# ===========================================================================
#                                  paving.jl
# ===========================================================================
@testitem "paving: small helpers" tags=[:paving, :helpers] setup=[SatSetup] begin
    using Symbolics, Random
    @test CAS._MAX_MASKED == 64

    @testset "_full_mask" begin
        @test CAS._full_mask(0) == 0
        @test CAS._full_mask(3) == 0b111
        @test CAS._full_mask(64) == typemax(UInt64)
        @test CAS._full_mask(70) == typemax(UInt64)
    end

    @testset "boxes" begin
        B = boxof(bi(0.0, 2.0), bi(10.0, 20.0))
        @test CAS._box_contains([1.0, 15.0], B)
        @test !CAS._box_contains([3.0, 15.0], B)
        @test !CAS._box_contains([1.0, 25.0], B)
        @test !CAS._is_point(B)
        @test CAS._is_point(boxof(bi(1.0, 1.0), bi(2.0, 2.0)))
        @test !CAS._is_point(boxof(bi(1.0, 1.0), bi(2.0, 3.0)))
        @test !CAS._is_point(boxof(CAS._empty_bi()))
        @test CAS._box_empty(boxof(bi(0.0, 1.0), CAS._empty_bi()))
        @test !CAS._box_empty(B)
    end

    @testset "interval constructors and lifting" begin
        @test iv_eq(CAS._const_interval(3), bi(3.0, 3.0))
        @test iv_eq(CAS._const_interval(2.5), bi(2.5, 2.5))
        o = CAS._const_interval(1 // 3)
        @test iv_in(1 / 3, o) && _sup(o) > _inf(o)
        o = CAS._const_interval(2^53 + 1)                    # not exactly representable
        @test iv_in(2^53 + 1, o)
        v = bi(1.0, 2.0)
        @test CAS._lift(CAS._BI, v) === v
        @test CAS._is_defined(CAS._lift(CAS._DI, v))
        @test CAS._bi(IA.interval(v)) === v || iv_eq(CAS._bi(IA.interval(v)), v)
        @test iv_empty(CAS._empty_bi()) && !iv_empty(CAS._entire_bi())
    end

    @testset "_significant_reduction" begin
        sr = CAS._significant_reduction
        @test sr(bi(0.0, 1.0), CAS._empty_bi(), 0.01)                  # emptying always counts
        @test !sr(CAS._empty_bi(), bi(0.0, 1.0), 0.01)
        @test sr(bi(0.0, 10.0), bi(0.0, 9.0), 0.05)
        @test !sr(bi(0.0, 10.0), bi(0.0, 9.8), 0.05)
        @test !sr(bi(1.0, 1.0), bi(1.0, 1.0), 0.05)                    # degenerate
        @test sr(bi(0.0, Inf), bi(1.0, Inf), 0.05)                     # any tightening of an unbounded end
        @test !sr(bi(0.0, Inf), bi(0.0, Inf), 0.05)
    end
end

@testitem "paving: opcode and confine tables" tags=[:paving, :tape] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "_give_confine" begin
        @test iv_eq(CAS._give_confine(CAS._LT), bi(-Inf, 0.0))
        @test iv_eq(CAS._give_confine(CAS._LE), bi(-Inf, 0.0))
        @test iv_eq(CAS._give_confine(CAS._GT), bi(0.0, Inf))
        @test iv_eq(CAS._give_confine(CAS._GE), bi(0.0, Inf))
        @test iv_eq(CAS._give_confine(CAS._EQ), bi(0.0, 0.0))
        @test iv_eq(CAS._give_confine(CAS._NE), CAS._entire_bi())
        @test_throws ArgumentError CAS._give_confine(:foo)
    end

    @testset "_map_opcode" begin
        @test CAS._map_opcode(-, 1, false) == CAS.OP_NEG
        @test CAS._map_opcode(-, 2, false) == CAS.OP_SUB
        @test CAS._map_opcode(+, 2, false) == CAS.OP_ADD
        @test CAS._map_opcode(*, 2, false) == CAS.OP_MUL
        @test CAS._map_opcode(/, 2, false) == CAS.OP_DIV
        @test CAS._map_opcode(^, 2, true) == CAS.OP_POW_INT
        @test CAS._map_opcode(^, 2, false) == CAS.OP_POW
        for (f, code) in ((abs, CAS.OP_ABS), (sign, CAS.OP_SIGN), (exp, CAS.OP_EXP), (exp2, CAS.OP_EXP2),
            (exp10, CAS.OP_EXP10), (log, CAS.OP_LOG), (log2, CAS.OP_LOG2), (log10, CAS.OP_LOG10),
            (sin, CAS.OP_SIN), (cos, CAS.OP_COS), (tan, CAS.OP_TAN), (asin, CAS.OP_ASIN),
            (acos, CAS.OP_ACOS), (atan, CAS.OP_ATAN), (sinh, CAS.OP_SINH), (cosh, CAS.OP_COSH),
            (tanh, CAS.OP_TANH), (asinh, CAS.OP_ASINH), (acosh, CAS.OP_ACOSH), (atanh, CAS.OP_ATANH))
            @test CAS._map_opcode(f, 1, false) == code
        end
        @test_throws ArgumentError CAS._map_opcode(floor, 1, false)
    end
end

@testitem "paving: tape compilation" tags=[:paving, :tape] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "layout invariants" begin
        tape = CAS.compile_hc4(mk(x * y + 1, >=), [x, y])
        @test tape.num_vars == 2
        @test tape.tape_len == tape.num_vars + length(tape.constants) + length(tape.instructions)
        @test 1 <= tape.root_idx <= tape.tape_len
        @test iv_eq(tape.confine, bi(0.0, Inf)) && tape.rel === CAS._GE
        @test tape.mvf === nothing
        @test any(i -> i.op == CAS.OP_MUL, tape.instructions) && any(i -> i.op == CAS.OP_ADD, tape.instructions)
    end

    @testset "powers" begin
        t = CAS.compile_hc4(mk(x^2 - y, >=), [x, y])
        @test any(i -> i.op == CAS.OP_POW_INT && i.arg2 == 2, t.instructions)
        t = CAS.compile_hc4(mk(x^-2 - y, >=), [x, y])
        @test any(i -> i.op == CAS.OP_POW_INT && i.arg2 == -2, t.instructions)
        t = CAS.compile_hc4(mk(x^0.5 - y, >=), [x, y])
        @test any(i -> i.op == CAS.OP_POW, t.instructions)
        t = CAS.compile_hc4(mk(x^y - 1, >=), [x, y])
        @test any(i -> i.op == CAS.OP_POW, t.instructions)
    end

    @testset "common subexpressions are compiled once" begin
        t = CAS.compile_hc4(mk(sin(x + y) * cos(x + y), >=), [x, y])
        @test count(i -> i.op == CAS.OP_ADD, t.instructions) == 1
    end

    @testset "variable order is respected" begin
        rel = mk(x - 2y, >=)
        for vars in ([x, y], [y, x])
            tape = CAS.compile_hc4(rel, vars)
            ws = Vector{CAS._BI}(undef, tape.tape_len)
            vals = Dict(x => 5.0, y => 1.0)
            for (i, v) in enumerate(vars)
                ws[i] = bi(vals[v], vals[v])
            end
            @test iv_in(evalf(rel.residual, x => 5.0, y => 1.0), CAS._execute_forward!(tape, ws))
        end
    end

    @testset "errors" begin
        @test_throws ArgumentError CAS.compile_hc4(mk(x + z, >=), [x])      # z is not a declared variable
        @test_throws ArgumentError CAS.compile_hc4(mk(myf(x), >=), [x])     # unknown operation
    end

    @testset "_is_zero_tape / _compile_partial" begin
        @test CAS._is_zero_tape(CAS._compile_hc4_residual(Num(0), CAS._EQ, [x]))
        @test !CAS._is_zero_tape(CAS._compile_hc4_residual(Num(2), CAS._EQ, [x]))
        @test !CAS._is_zero_tape(CAS._compile_hc4_residual(x, CAS._EQ, [x]))
        d = CAS._compile_partial(x^2, x, [x])                                # 2x
        ws = Vector{CAS._BI}(undef, d.tape_len)
        ws[1] = bi(3.0, 3.0)
        @test iv_in(6.0, CAS._execute_forward!(d, ws))
        @test CAS._compile_partial(myf(x), x, [x]) === nothing               # no derivative rule: no tape
    end
end

@testitem "paving: _prepare and dropped constraints" tags=[:paving, :tape] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "all compile" begin
        prep = CAS._prepare([C(x - 1, >=), C(y - 2, <=)], [x, y])
        @test length(prep.tapes) == 2 && !prep.dropped
        @test prep.max_len == maximum(t.tape_len for t in prep.tapes)
        @test all(t -> t.num_vars == 2, prep.tapes)
        ws, dws = CAS._workspaces(prep)
        @test length(ws) == prep.max_len && length(dws) == prep.max_len
        @test eltype(ws) == CAS._BI && eltype(dws) == CAS._DI
    end

    @testset "uncompilable constraints are dropped, flagged and skipped" begin
        prep = CAS._prepare([C(myf(x), >), C(x - 1, >=)], [x])
        @test length(prep.tapes) == 1 && prep.dropped
        prep = CAS._prepare([C(x + z - 1, >=)], [x])                    # symbol outside `variables`
        @test isempty(prep.tapes) && prep.dropped && prep.max_len == 1
    end

    @testset "more than _MAX_MASKED constraints" begin
        many = [C(x - k, >=) for k in 1:70]
        prep = CAS._prepare(many, [x])
        @test length(prep.tapes) == CAS._MAX_MASKED && prep.dropped
    end

    @testset "_NO_TAPES" begin
        @test isempty(CAS._NO_TAPES.tapes) && !CAS._NO_TAPES.dropped && CAS._NO_TAPES.max_len == 0
    end
end

@testitem "paving: forward evaluation encloses the true value" tags=[:paving, :forward, :property] setup=[SatSetup] begin
    using Symbolics, Random
    rng = MersenneTwister(99)
    exprs = [x + y, x * y, x - y, x^2 - y, x^3 - 2x, exp(x) / (y^2 + 1), abs(x - y),
        sin(x) * cos(y), tanh(x) * y, x / (y^2 + 1), log(y^2 + 1), atan(x) - y]
    for e in exprs
        rel = mk(e, >=)                       # canonicalisation may scale/negate, so compare to rel.residual
        tape = CAS.compile_hc4(rel, [x, y])
        ws = Vector{CAS._BI}(undef, tape.tape_len)
        dws = Vector{CAS._DI}(undef, tape.tape_len)
        for _ in 1:30
            px, py = 8 * rand(rng) - 4, 8 * rand(rng) - 4
            v = evalf(rel.residual, x => px, y => py)
            (v === nothing || !isfinite(v)) && continue
            tol = 1e-9 * (1 + abs(v))
            for r in (1e-3, 0.0, 0.5)         # fat box, point box
                ws[1] = bi(px - r, px + r)
                ws[2] = bi(py - r, py + r)
                F = CAS._execute_forward!(tape, ws)
                @test !iv_empty(F)
                @test _inf(F) - tol <= v <= _sup(F) + tol
                dws[1] = IA.interval(ws[1])   # the decorated pass agrees
                dws[2] = IA.interval(ws[2])
                D = IA.bareinterval(CAS._execute_forward!(tape, dws))
                @test _inf(D) - tol <= v <= _sup(D) + tol
            end
        end
    end
end

@testitem "paving: decorated evaluation reports definedness" tags=[:paving, :forward] setup=[SatSetup] begin
    using Symbolics, Random
    tape = CAS.compile_hc4(mk(log(x), >=), [x])
    dws = Vector{CAS._DI}(undef, tape.tape_len)
    dws[1] = IA.interval(bi(1.0, 2.0))
    @test CAS._is_defined(CAS._execute_forward!(tape, dws))
    dws[1] = IA.interval(bi(-1.0, 2.0))                       # leaves the domain of log
    @test !CAS._is_defined(CAS._execute_forward!(tape, dws))

    tape = CAS.compile_hc4(mk(x^-1 - 1, >=), [x])             # pole inside the box: not continuous
    dws = Vector{CAS._DI}(undef, tape.tape_len)
    dws[1] = IA.interval(bi(-1.0, 1.0))
    v = CAS._execute_forward!(tape, dws)
    @test !(IA.decoration(v) >= IA.dac)

    @testset "_inside_and_defined" begin
        tape = CAS.compile_hc4(mk(log(x) - 5, <=), [x])
        dws = Vector{CAS._DI}(undef, tape.tape_len)
        # the bare enclosure of log([-1, 2]) is clipped to log's domain, so it says "inside" ...
        @test CAS._inside_and_defined(tape, boxof(bi(0.5, 2.0)), dws)
        # ... but the decorated pass knows log is not defined on the whole box
        @test !CAS._inside_and_defined(tape, boxof(bi(-1.0, 2.0)), dws)
        @test !CAS._inside_and_defined(tape, boxof(bi(1.0, 1000.0)), dws)   # defined, but not inside
    end
end

@testitem "paving: _eval_relation_status" tags=[:paving, :status] setup=[SatSetup] begin
    using Symbolics, Random
    table = [
        (CAS._LT, -2.0, -1.0, :inside), (CAS._LT, 0.0, 1.0, :outside), (CAS._LT, -1.0, 1.0, :unknown), (CAS._LT, -1.0, 0.0, :unknown),
        (CAS._LE, -1.0, 0.0, :inside), (CAS._LE, 0.5, 1.0, :outside), (CAS._LE, 0.0, 1.0, :unknown), (CAS._LE, -1.0, 1.0, :unknown),
        (CAS._GT, 1.0, 2.0, :inside), (CAS._GT, -1.0, 0.0, :outside), (CAS._GT, 0.0, 1.0, :unknown), (CAS._GT, -1.0, 1.0, :unknown),
        (CAS._GE, 0.0, 1.0, :inside), (CAS._GE, -2.0, -1.0, :outside), (CAS._GE, -1.0, 0.0, :unknown), (CAS._GE, -1.0, 1.0, :unknown),
        (CAS._EQ, 0.0, 0.0, :inside), (CAS._EQ, 1.0, 2.0, :outside), (CAS._EQ, -2.0, -1.0, :outside), (CAS._EQ, -1.0, 1.0, :unknown), (CAS._EQ, 0.0, 1.0, :unknown),
        (CAS._NE, 1.0, 2.0, :inside), (CAS._NE, -2.0, -1.0, :inside), (CAS._NE, 0.0, 0.0, :outside), (CAS._NE, -1.0, 1.0, :unknown), (CAS._NE, 0.0, 1.0, :unknown),
    ]
    for (rel, lo, hi, expected) in table
        @test CAS._eval_relation_status(rel, bi(lo, hi)) === expected
    end
    for rel in RELS
        @test CAS._eval_relation_status(rel, CAS._empty_bi()) === :outside
    end

    @testset "sound against sampling" begin
        rng = MersenneTwister(3)
        for _ in 1:300
            a, b = sort([6 * rand(rng) - 3, 6 * rand(rng) - 3])
            a = rand(rng) < 0.3 ? round(a) : a            # hit the exact-zero boundary sometimes
            b = max(a, rand(rng) < 0.3 ? round(b) : b)
            iv = bi(a, b)
            for rel in RELS
                st = CAS._eval_relation_status(rel, iv)
                pts = [a, b, (a + b) / 2, rand_in(rng, iv)]
                st === :inside && @test all(p -> CAS._holds(rel, p), pts)
                st === :outside && @test !any(p -> CAS._holds(rel, p), pts)
            end
        end
    end
end

@testitem "paving: reverse helpers" tags=[:paving, :reverse] setup=[SatSetup] begin
    using Symbolics, Random
    E = CAS._empty_bi()

    @testset "_rev_mul solves a*b ∈ c for a" begin
        @test iv_eq(CAS._rev_mul(bi(1.0, 2.0), bi(1.0, 1.0), bi(-10.0, 10.0)), bi(1.0, 2.0))
        @test iv_eq(CAS._rev_mul(bi(-1.0, 1.0), bi(-1.0, 1.0), bi(-10.0, 10.0)), bi(-10.0, 10.0))   # 0 ∈ b, 0 ∈ c
        @test iv_eq(CAS._rev_mul(bi(1.0, 2.0), bi(0.0, 1.0), bi(-10.0, 10.0)), bi(1.0, 10.0))       # 0 ∈ b only
        @test iv_empty(CAS._rev_mul(E, bi(1.0, 2.0), bi(0.0, 1.0)))
        @test iv_empty(CAS._rev_mul(bi(1.0, 2.0), E, bi(0.0, 1.0)))
        rng = MersenneTwister(11)
        for _ in 1:300
            a0, b0 = 4 * rand(rng) - 2, 4 * rand(rng) - 2
            c = bi(a0 * b0 - 0.1, a0 * b0 + 0.1)
            b = bi(b0 - 0.3 * rand(rng), b0 + 0.3 * rand(rng))
            r = CAS._rev_mul(c, b, bi(-3.0, 3.0))
            @test iv_in(a0, r)
        end
    end

    @testset "_rev_pow_int solves x^n ∈ c for x" begin
        X = bi(-10.0, 10.0)
        r = CAS._rev_pow_int(bi(4.0, 9.0), 2, X)
        @test _inf(r) <= -3 && _sup(r) >= 3 && _inf(r) >= -3 - 1e-9 && _sup(r) <= 3 + 1e-9
        @test iv_empty(CAS._rev_pow_int(bi(-5.0, -1.0), 2, X))
        r = CAS._rev_pow_int(bi(8.0, 27.0), 3, X)
        @test _inf(r) <= 2 && _sup(r) >= 3 && _inf(r) >= 2 - 1e-9 && _sup(r) <= 3 + 1e-9
        r = CAS._rev_pow_int(bi(-27.0, -8.0), 3, X)
        @test _inf(r) <= -3 && _sup(r) >= -2 && _sup(r) <= -2 + 1e-9
        @test iv_eq(CAS._rev_pow_int(bi(0.5, 2.0), 0, X), X)               # x^0 = 1
        @test iv_empty(CAS._rev_pow_int(bi(2.0, 3.0), 0, X))
        r = CAS._rev_pow_int(bi(2.0, 4.0), -1, X)                           # 1/x ∈ [2,4]
        @test _inf(r) <= 0.25 && _sup(r) >= 0.5 && _inf(r) >= 0.25 - 1e-9 && _sup(r) <= 0.5 + 1e-9
        @test iv_empty(CAS._rev_pow_int(E, 2, X))
        rng = MersenneTwister(12)
        for n in (-3, -2, -1, 1, 2, 3, 4, 5), _ in 1:100
            x0 = 4 * rand(rng) - 2
            abs(x0) < 0.2 && continue
            v = x0^n
            c = bi(v - 1e-6 * abs(v), v + 1e-6 * abs(v))
            @test iv_in(x0, CAS._rev_pow_int(c, n, bi(-2.0, 2.0)))
        end
    end

    @testset "_widen_periodic" begin
        twopi = 2.0 * Float64(pi)
        @test iv_eq(CAS._widen_periodic(CAS._entire_bi(), twopi, bi(0.0, 1.0)), CAS._entire_bi())  # unbounded: no loop
        @test iv_empty(CAS._widen_periodic(E, twopi, bi(0.0, 1.0)))
        @test iv_empty(CAS._widen_periodic(bi(0.0, 10.0), twopi, E))
        # every x in X with sin(x) in C survives
        rng = MersenneTwister(13)
        X = bi(-8.0, 8.0)
        for _ in 1:200
            x0 = rand_in(rng, X)
            s = sin(x0)
            C0 = bi(max(-1.0, s - 1e-6), min(1.0, s + 1e-6))
            a = asin(C0)
            @test iv_in(x0, CAS._widen_periodic(X, twopi, a, bi(Float64(pi)) - a))
        end
    end
end

@testitem "paving: HC4Revise" tags=[:paving, :hc4] setup=[SatSetup] begin
    using Symbolics, Random
    rel = mk(x - 1, >=)
    tape = CAS.compile_hc4(rel, [x])
    ws = Vector{CAS._BI}(undef, tape.tape_len)
    dws = Vector{CAS._DI}(undef, tape.tape_len)

    @testset "tape API" begin
        @test CAS.HC4Revise(boxof(bi(2.0, 3.0)), tape, ws, dws)[1] === :inside
        @test CAS.HC4Revise(boxof(bi(-3.0, 0.0)), tape, ws, dws)[1] === :outside
        st, b = CAS.HC4Revise(boxof(bi(0.0, 2.0)), tape, ws, dws)
        @test st === :unknown
        @test _inf(CAS._bi(b[1])) >= 1.0 - 1e-12 && _sup(CAS._bi(b[1])) == 2.0
    end

    @testset "`:inside` needs definedness on the whole box" begin
        t = CAS.compile_hc4(mk(log(x) - 5, <=), [x])
        w = Vector{CAS._BI}(undef, t.tape_len)
        d = Vector{CAS._DI}(undef, t.tape_len)
        @test CAS.HC4Revise(boxof(bi(0.5, 2.0)), t, w, d)[1] === :inside
        st, b = CAS.HC4Revise(boxof(bi(-1.0, 2.0)), t, w, d)
        @test st === :unknown                                    # bare says inside, decorated disagrees
        @test _inf(CAS._bi(b[1])) <= 0.5 && _sup(CAS._bi(b[1])) >= 2.0
    end

    @testset "standalone API" begin
        c = CAS.HC4Revise(boxof(bi(-5.0, 5.0)), [x], rel)
        @test _inf(CAS._bi(c[1])) >= 1.0 - 1e-12 && _sup(CAS._bi(c[1])) == 5.0
        @test CAS._box_empty(CAS.HC4Revise(boxof(bi(-5.0, 5.0)), [x], mk(x - 10, >=)))
    end

    @testset "equality and inequality contract to the right set" begin
        c = CAS.HC4Revise(boxof(bi(-10.0, 10.0)), [x], mk(x^2 - 4, <=))
        @test _inf(CAS._bi(c[1])) <= -2 && _inf(CAS._bi(c[1])) >= -2 - 1e-9
        @test _sup(CAS._bi(c[1])) >= 2 && _sup(CAS._bi(c[1])) <= 2 + 1e-9
        c = CAS.HC4Revise(boxof(bi(0.0, 1.0), bi(0.0, 10.0)), [x, y], mk(x + y - 4, ==))
        @test _inf(CAS._bi(c[2])) >= 3 - 1e-9 && _sup(CAS._bi(c[2])) <= 4 + 1e-9
    end
end

@testitem "paving: HC4Revise never removes a feasible point" tags=[:paving, :hc4, :property, :slow] setup=[SatSetup] begin
    using Symbolics, Random
    rng = MersenneTwister(5)
    box2 = boxof(bi(-2.0, 2.0), bi(-2.0, 2.0))
    for r in (mk(x^2 + y^2 - 1, <=), mk(x * y - 1, <=), mk(x * y - 1, >=), mk(sin(x) - y, >=),
        mk(exp(x) - y - 2, <=), mk(abs(x) + abs(y) - 1, <=), mk(x^2 - y, <), mk(x - y, !=))
        res = CAS.HC4Revise(box2, [x, y], r)
        for _ in 1:400
            px, py = 4 * rand(rng) - 2, 4 * rand(rng) - 2
            v = evalf(r.residual, x => px, y => py)
            (v === nothing || !CAS._holds(r.relation, v)) && continue
            @test !CAS._box_empty(res)
            ix, iy = CAS._bi(res[1]), CAS._bi(res[2])
            @test _inf(ix) - 1e-9 <= px <= _sup(ix) + 1e-9
            @test _inf(iy) - 1e-9 <= py <= _sup(iy) + 1e-9
        end
    end
    # points exactly on a curve (random sampling never hits an equality)
    r = mk(x - y^2, ==)
    res = CAS.HC4Revise(box2, [x, y], r)
    for _ in 1:200
        py = 2.8 * rand(rng) - 1.4
        px = py^2
        @test _inf(CAS._bi(res[1])) - 1e-9 <= px <= _sup(CAS._bi(res[1])) + 1e-9
        @test _inf(CAS._bi(res[2])) - 1e-9 <= py <= _sup(CAS._bi(res[2])) + 1e-9
    end
end

@testitem "paving: mean-value forms" tags=[:paving, :mvf] setup=[SatSetup] begin
    using Symbolics, Random
    freshws(t) = (Vector{CAS._BI}(undef, t.tape_len), Vector{CAS._DI}(undef, t.tape_len))

    @testset "gates" begin
        @test CAS.compile_hc4(mk(x^2 - 2x + 1.05, >=), [x]; mvf=true).mvf isa CAS.MVFPlan
        @test CAS.compile_hc4(mk(x^2 - 2x + 1.05, >=), [x]).mvf === nothing           # off by default
        @test CAS.compile_hc4(mk(x * y - 1, >=), [x, y]; mvf=true).mvf === nothing    # no repeated variable
        @test CAS.compile_hc4(mk(abs(x) + x^2, >=), [x]; mvf=true).mvf === nothing    # not differentiable
        t = CAS.compile_hc4(mk(x^2 - x, >=), [x, y])
        @test CAS._mvf_multi_occurrence(t) == [1]
        @test CAS._mvf_differentiable(t)
        @test !CAS._mvf_differentiable(CAS.compile_hc4(mk(abs(x) - y, >=), [x, y]))
        t3 = CAS.compile_hc4(mk(x + y + z, >=), [x, y, z])
        ops = Int[]
        for inst in t3.instructions
            CAS._foreach_operand(a -> push!(ops, a), t3, inst)
        end
        @test sort(ops) == [1, 2, 3]
        ops = Int[]
        t2 = CAS.compile_hc4(mk(x^2 - y, >=), [x, y])
        for inst in t2.instructions
            inst.op == CAS.OP_POW_INT && CAS._foreach_operand(a -> push!(ops, a), t2, inst)
        end
        @test ops == [1]                                                              # the exponent is not an operand
        @test CAS._mvf_active(bi(0.0, 1.0)) && !CAS._mvf_active(bi(1.0, 1.0))
        @test !CAS._mvf_active(bi(0.0, Inf)) && !CAS._mvf_active(CAS._empty_bi())
    end

    @testset "mean-value form decides what the natural enclosure cannot" begin
        rel = mk(x^2 - 2x + 1.05, >=)             # always true; dependency problem hides it
        plain = CAS.compile_hc4(rel, [x])
        mvf = CAS.compile_hc4(rel, [x]; mvf=true)
        box = boxof(bi(0.9, 1.1))
        @test CAS.HC4Revise(box, plain, freshws(plain)...)[1] === :unknown
        @test CAS.HC4Revise(box, mvf, freshws(mvf)...)[1] === :inside
        plan = mvf.mvf::CAS.MVFPlan
        @test plan.state[] == 1 && plan.vars == [1] && length(plan.dtapes) == 1
        @test plan.tries == 1 && plan.hits == 1
        rep = CAS._mvf_report(CAS._Prepared([mvf, plain], false, mvf.tape_len))
        @test rep[1].plan && rep[1].hits == 1 && rep[1].vars == [1]
        @test !rep[2].plan
    end

    @testset "back-off" begin
        plan = CAS.MVFPlan(mk(x^2 - x, >=).residual, [x], [1])
        skips = Int[]
        for _ in 1:8
            @test CAS._mvf_fail!(plan) === nothing
            push!(skips, plan.skip)
        end
        @test skips == [1, 3, 7, 15, 31, 63, 63, 63]
        @test plan.fails == 8
    end

    @testset "refine returns nothing when it should not run" begin
        rel = mk(x^2 - 2x + 1.05, >=)
        t = CAS.compile_hc4(rel, [x]; mvf=true)
        ws, dws = freshws(t)
        ws[1] = bi(0.9, 1.1)
        F = CAS._execute_forward!(t, ws)
        plan = t.mvf::CAS.MVFPlan
        plan.state[] = -1                                                  # unusable
        @test CAS._mvf_refine!(t, plan, ws, dws, F) === nothing
        plan.state[] = 0
        plan.skip = 2                                                      # backing off
        @test CAS._mvf_refine!(t, plan, ws, dws, F) === nothing && plan.skip == 1
        plan.skip = 0
        ws[1] = bi(1.0, 1.0)                                               # point box: nothing to refine
        F0 = CAS._execute_forward!(t, ws)
        @test CAS._mvf_refine!(t, plan, ws, dws, F0) === nothing
    end
end

@testitem "paving: mean-value forms are sound" tags=[:paving, :mvf, :property, :slow] setup=[SatSetup] begin
    using Symbolics, Random
    rng = MersenneTwister(21)
    exprs = [x^2 - x, x * y - x, sin(x) * x - x, (x - 1) * (x + 1) - x, exp(x) - x^2 - 1, x^2 + y^2 - x * y]
    for e in exprs, s in (-0.3, 0.0, 0.3), r in (CAS._GE, CAS._LE)
        rel = mk(e + s, r)
        tp = CAS.compile_hc4(rel, [x, y])
        tm = CAS.compile_hc4(rel, [x, y]; mvf=true)
        wp, dp = Vector{CAS._BI}(undef, tp.tape_len), Vector{CAS._DI}(undef, tp.tape_len)
        wm, dm = Vector{CAS._BI}(undef, tm.tape_len), Vector{CAS._DI}(undef, tm.tape_len)
        for _ in 1:6
            cx, cy, w = 3 * rand(rng) - 1.5, 3 * rand(rng) - 1.5, 0.05 + 0.5 * rand(rng)
            box = boxof(bi(cx - w, cx + w), bi(cy - w, cy + w))
            sp, _ = CAS.HC4Revise(box, tp, wp, dp)
            sm, _ = CAS.HC4Revise(box, tm, wm, dm)
            (sp !== :unknown) && @test sm === sp                           # mvf only ever adds decisions
            for _ in 1:15
                v = evalf(rel.residual, x => cx + w * (2rand(rng) - 1), y => cy + w * (2rand(rng) - 1))
                v === nothing && continue
                holds = CAS._holds(rel.relation, v)
                sm === :inside && @test holds
                sm === :outside && @test !holds
            end
        end
    end
end

@testitem "paving: _hc4_propagate" tags=[:paving, :hc4] setup=[SatSetup] begin
    using Symbolics, Random
    @testset "all inside clears the mask" begin
        prep = CAS._prepare([C(x - 1, >=)], [x])
        ws, dws = CAS._workspaces(prep)
        st, b, mask = CAS._hc4_propagate(boxof(bi(2.0, 3.0)), prep.tapes, CAS._full_mask(1), ws, dws)
        @test st === :unknown && mask == 0
    end

    @testset "outside / empty box is :unsat" begin
        prep = CAS._prepare([C(x - 1, >=)], [x])
        ws, dws = CAS._workspaces(prep)
        @test CAS._hc4_propagate(boxof(bi(-3.0, 0.0)), prep.tapes, CAS._full_mask(1), ws, dws)[1] === :unsat
        @test CAS._hc4_propagate(boxof(CAS._empty_bi()), prep.tapes, CAS._full_mask(1), ws, dws)[1] === :unsat
    end

    @testset "iterates to a fixpoint (and max_pass limits it)" begin
        # listed in the unhelpful order: y >= x only helps after x >= 1 has been applied
        prep = CAS._prepare([C(y - x, >=), C(x - 1, >=)], [x, y])
        ws, dws = CAS._workspaces(prep)
        box = boxof(bi(0.0, 10.0), bi(0.0, 10.0))
        st, b, _ = CAS._hc4_propagate(box, prep.tapes, CAS._full_mask(2), ws, dws)
        @test st === :unknown
        @test _inf(CAS._bi(b[1])) >= 1 - 1e-12 && _inf(CAS._bi(b[2])) >= 1 - 1e-12
        st, b, _ = CAS._hc4_propagate(box, prep.tapes, CAS._full_mask(2), ws, dws; max_pass=1)
        @test _inf(CAS._bi(b[2])) == 0.0
    end

    @testset "a contracted point re-checks the remaining constraints" begin
        prep = CAS._prepare([C(x^2, ==)], [x])
        ws, dws = CAS._workspaces(prep)
        st, b, mask = CAS._hc4_propagate(boxof(bi(-1.0, 1.0)), prep.tapes, CAS._full_mask(1), ws, dws)
        @test st === :unknown && CAS._is_point(b) && mask == 0
    end
end

@testitem "paving: _contract" tags=[:paving, :hc4] setup=[SatSetup] begin
    using Symbolics, Random
    contract(cs, vars, ivs...) = CAS._contract(boxof(ivs...), cs, vars)

    c = contract(cons(C(x - 1, >=)), [x], bi(-5.0, 5.0))
    @test c.status === :sat && c.mask == 0
    @test _inf(c.box[1]) >= 1.0 - 1e-12 && _sup(c.box[1]) == 5.0

    c = contract(cons(C(x - 6, >=)), [x], bi(-5.0, 5.0))
    @test c.status === :unsat && CAS._box_empty(CAS._make_box(c.box))
    @test contract(cons(C(x^2 + 1, <=)), [x], bi(-5.0, 5.0)).status === :unsat

    c = contract(cons(C(x + y - 4, ==)), [x, y], bi(0.0, 1.0), bi(0.0, 10.0))
    @test c.status === :unknown && c.mask != 0
    @test _inf(c.box[2]) >= 3.0 - 1e-9 && _sup(c.box[2]) <= 4.0 + 1e-9

    c = contract(cons(C(x^2 - 4, <=)), [x], bi(-10.0, 10.0))
    @test _inf(c.box[1]) >= -2 - 1e-9 && _inf(c.box[1]) <= -2 && _sup(c.box[1]) >= 2 && _sup(c.box[1]) <= 2 + 1e-9

    @testset "nothing compilable: bounds untouched, :sat is off the table" begin
        c = contract(cons(C(myf(x), >)), [x], bi(-5.0, 5.0))
        @test c.status === :unknown && c.prep.dropped && ivs_eq(c.box, [bi(-5.0, 5.0)])
    end

    @testset "_infeasible" begin
        c = CAS._infeasible(3)
        @test c.status === :unsat && length(c.box) == 3 && all(iv_empty, c.box)
        @test c.prep === CAS._NO_TAPES
    end
end

@testitem "paving: _pave_core and _pave_contracted" tags=[:paving, :pave] setup=[SatSetup] begin
    using Symbolics, Random
    ratio = CAS.HC4_DEFAULT_RATIO

    @testset "hand-built outcomes" begin
        NT = CAS._NO_TAPES
        @test CAS._pave_contracted(CAS._Contracted(:unsat, CAS._BI[bi(0.0, 1.0)], UInt64(0), NT)) === :unsat
        @test CAS._pave_contracted(CAS._Contracted(:sat, CAS._BI[bi(0.0, 1.0)], UInt64(0), NT)) === :sat
        @test CAS._pave_contracted(CAS._Contracted(:unknown, CAS._BI[bi(0.0, 1.0)], UInt64(0), NT)) === :unknown  # dropped
        @test CAS._pave_contracted(CAS._Contracted(:unknown, CAS._BI[bi(0.0, Inf)], UInt64(1), NT)) === :unknown  # unbounded
        @test CAS._pave_contracted(CAS._Contracted(:unknown, CAS._BI[bi(1.0, 1.0)], UInt64(1), NT)) === :unknown  # a point
    end

    @testset "_pave_core" begin
        prep = CAS._prepare([C(x - 1, >=)], [x])
        ws, dws = CAS._workspaces(prep)
        root = boxof(bi(0.0, 2.0))
        @test CAS._pave_core(root, prep, ws, dws, CAS._full_mask(1), 0.05, ratio) === :sat
        # a certifier that never accepts: every surviving box shrinks below epsilon -> unresolved
        @test CAS._pave_core(root, prep, ws, dws, CAS._full_mask(1), 0.05, ratio; certify=(a...) -> false) === :unknown
        # a certifier that accepts the root decides immediately, unless something was dropped
        @test CAS._pave_core(root, prep, ws, dws, CAS._full_mask(1), 0.05, ratio; certify=(a...) -> true) === :sat
        dropped = CAS._Prepared(prep.tapes, true, prep.max_len)
        @test CAS._pave_core(root, dropped, ws, dws, CAS._full_mask(1), 0.05, ratio; certify=(a...) -> true) === :unknown
        @test_throws ArgumentError CAS._pave_core(root, prep, ws, dws, CAS._full_mask(1), 0.05, ratio; max_boxes=0)
        prep2 = CAS._prepare([C(x - 5, >=)], [x])
        ws2, dws2 = CAS._workspaces(prep2)
        @test CAS._pave_core(boxof(bi(0.0, 2.0)), prep2, ws2, dws2, CAS._full_mask(1), 0.05, ratio) === :unsat
        @test CAS._DEFAULT_PAVE_CERTIFY(root, UInt64(0), ws, dws) && !CAS._DEFAULT_PAVE_CERTIFY(root, UInt64(1), ws, dws)
    end

    @testset "end to end on the unit disk" begin
        with_env(tol=0.05) do
            box = boxof(bi(-2.0, 2.0), bi(-2.0, 2.0))
            disk = cons(C(x^2 + y^2 - 1, <=))
            c = CAS._contract(box, disk, [x, y])
            @test c.status === :unknown
            @test CAS._pave_contracted(c) === :sat
            @test CAS._pave_contracted(c; max_boxes=1) === :unknown          # budget exhausted: never a guess

            # needs paving to refute: x*y >= 1 inside the unit disk is empty, but HC4 alone cannot see it
            c = CAS._contract(box, cons(C(x^2 + y^2 - 1, <=), C(x * y - 1, >=)), [x, y])
            @test CAS._pave_contracted(c) === :unsat

            # an equality curve can never be certified by the default hook
            c = CAS._contract(box, cons(C(x^2 + y^2 - 1, ==)), [x, y])
            @test CAS._pave_contracted(c) === :unknown
        end
    end
end

@testitem "paving: zero certificates" tags=[:paving, :certificate] setup=[SatSetup] begin
    using Symbolics, Random
    function mkcert(residual_num, vars, tape_rel)
        tape = CAS.compile_hc4(tape_rel, vars)
        return CAS._ZeroCertificate(tape_rel.residual, vars, tape), tape
    end
    rel = mk(x - 1, ==)
    cert, tape = mkcert(rel.residual, [x], rel)
    ws = Vector{CAS._BI}(undef, tape.tape_len)
    dws = Vector{CAS._DI}(undef, tape.tape_len)
    probe = UInt64(1)                                        # bit zero is the probe

    @testset "construction" begin
        @test length(cert.dtapes) == 1 && cert.dtapes[1] !== nothing
        @test length(cert.scratch) >= tape.tape_len
        @test CAS._zero_eval(tape, CAS._BI[bi(0.0, 1.0), bi(0.0, 1.0)], cert.scratch) === nothing   # arity mismatch
    end

    @testset "point signs are rigorous" begin
        @test CAS._zero_point_sign(cert, CAS._BI[bi(3.0)]) == 1
        @test CAS._zero_point_sign(cert, CAS._BI[bi(0.0)]) == -1
        @test CAS._zero_point_sign(cert, CAS._BI[bi(1.0)]) == 0         # exactly zero: not a sign
    end

    @testset "IVT and the callable hook" begin
        @test CAS._zero_ivt(cert, CAS._BI[bi(0.0, 2.0)])
        @test !CAS._zero_ivt(cert, CAS._BI[bi(2.0, 3.0)])
        @test cert(boxof(bi(0.0, 2.0)), probe, ws, dws)
        @test !cert(boxof(bi(2.0, 3.0)), probe, ws, dws)                # no root: never certified
        @test cert(boxof(bi(2.0, 3.0)), UInt64(0), ws, dws)             # nothing left to prove
        @test !cert(boxof(bi(0.0, 2.0)), UInt64(0b11), ws, dws)         # another constraint is still undecided
    end

    @testset "interval Newton" begin
        r2 = mk(x^2 - 2, ==)
        c2, _ = mkcert(r2.residual, [x], r2)
        @test CAS._zero_newton(c2, CAS._BI[bi(1.0, 2.0)])               # unique simple root √2
        @test !CAS._zero_newton(c2, CAS._BI[bi(1.5, 2.0)])              # no root there
        @test !CAS._zero_newton(c2, CAS._BI[bi(-2.0, 2.0)])             # derivative contains 0
        @test !CAS._zero_newton(c2, CAS._BI[])
    end

    @testset "undefined on part of the box: never certified" begin
        rl = mk(log(x), ==)
        cl, tl = mkcert(rl.residual, [x], rl)
        w = Vector{CAS._BI}(undef, tl.tape_len)
        d = Vector{CAS._DI}(undef, tl.tape_len)
        @test !cl(boxof(bi(-1.0, 2.0)), probe, w, d)
        @test cl(boxof(bi(0.5, 2.0)), probe, w, d)
    end
end

@testitem "paving: zero probes and dropped constraints end to end" tags=[:paving, :certificate, :sat] setup=[SatSetup] begin
    using Symbolics, Random
    cs = [C(x - 1, >=), C(2 - x, >=)]
    @test fresh(() -> CAS.can_be_zero(x - 1, cs)) === Yes
    @test fresh(() -> CAS.can_be_zero(x^2 - 5, cs)) === No              # x^2 ∈ [1, 4]
    # the certificate is what lets an irrational root be reported as attained
    @test fresh(() -> CAS.can_be_zero(x^2 - 2, cs)) === Yes

    @testset "a dropped constraint forbids any existence claim" begin
        cs_dropped = [C(myf(x), >), C(x - 1, >=), C(2 - x, >=)]
        e = fresh(() -> CAS.expr_evidence(x - 1.5, cs_dropped; want=(:zero,)))
        @test e.zero === Undetermined
        @test fresh(() -> CAS.satisfiable(cs_dropped)) !== Yes
    end
end

# ===========================================================================
#                    known issues (read the comment on each)
# ===========================================================================
@testitem "known issues" tags=[:known_issues] setup=[SatSetup] begin
    using Symbolics, Random
    # `_pkey` reads `c.key`, but `Constraint` has no `key` field (it lives on `c.relation.key`).
    # Harmless while `params` is always empty; breaks the moment a parameter constraint is used.
    @test_broken CAS._pkey([C(x, >)]) isa Tuple

    # `_s_pow(a, p)` sends integer-valued exponents with |p| >= 1_000_000 down the "non-integer"
    # branch, where a negative base is declared impossible. (-3)^2_000_000 is positive (or +Inf),
    # so a negative-only base ends up with *no* possible sign, which reads as "empty" downstream.
    @test_broken CAS._s_pow(CAS._Signs(true, false, false), 2_000_000).pos
end
