#------------------------------------------------
# sat specific utils
#------------------------------------------------

_answer(i::Evidence, w::Symbol) = w === :neg ? i.neg : w === :zero ? i.zero : i.pos
_decided(i::Evidence, want) = all(w -> _answer(i, w) !== Unknown, want)
_ekey(u, ckey::Tuple) = (:evidence, u, ckey, _env())
_fkey(comp::Comp) = (:comp, comp.key, _env())
_hkey(comp::Comp) = (:hc4, comp.key, _env())

_to_answer(s::Symbol)::Answer = s === :sat ? Yes : s === :unsat ? No : Unknown

_make_box(ivs::Vector{_BI}) = IntervalBox(ivs)

function _with(i::Evidence; outer=i.outer, strict_lo=i.strict_lo, strict_hi=i.strict_hi,
    neg=i.neg, zero=i.zero, pos=i.pos, ident_zero=i.ident_zero)
    return Evidence(outer, strict_lo, strict_hi, neg, zero, pos, ident_zero)
end

_set_answer(i::Evidence, w::Symbol, a::Answer) =
    w === :neg ? _with(i; neg=a) : w === :zero ? _with(i; zero=a) : _with(i; pos=a)

_join(x::Answer, y::Answer) = x === y ? x : x === Unknown ? y : y === Unknown ? x : No

function _rel_from_want(want::Symbol)
    want === :neg && return _LT
    want === :zero && return _EQ
    want === :pos && return _GT
    error("invalid want: $want")
end

"""
Make an Evidence self-consistent: answers follow from the interval and the interval
follows from the answers. Contradictions collapse to the empty Evidence.
"""
function _tighten(i::Evidence)::Evidence
    i.ident_zero && return _IDENT_ZERO
    o = i.outer
    isempty_interval(o) && return _EMPTY_EVIDENCE
    lo, hi = inf(o), sup(o)
    slo = i.strict_lo || lo == -Inf
    shi = i.strict_hi || hi == Inf
    neg, zer, pos = i.neg, i.zero, i.pos
    lo >= 0 && (neg = No)
    hi <= 0 && (pos = No)
    (lo > 0 || hi < 0 || (lo == 0 && slo) || (hi == 0 && shi)) && (zer = No)
    if neg === No && lo < 0
        lo = 0.0
        slo = false
    end
    if pos === No && hi > 0
        hi = 0.0
        shi = false
    end
    if zer === No
        lo == 0 && (slo = true)
        hi == 0 && (shi = true)
    end
    (lo > hi || (lo == hi && (slo || shi || isinf(lo)))) && return _EMPTY_EVIDENCE
    (neg === No && zer === No && pos === No) && return _EMPTY_EVIDENCE
    outer = (lo == inf(o) && hi == sup(o)) ? o : _bi(lo, hi)
    return Evidence(outer, slo, shi, neg, zer, pos, false)
end

"Combine two sound facts about the same expression in the same context."
function _merge(a::Evidence, b::Evidence)::Evidence
    (a.ident_zero || b.ident_zero) && return _IDENT_ZERO
    (isempty_interval(a.outer) || isempty_interval(b.outer)) && return _EMPTY_EVIDENCE
    la, lb, ha, hb = inf(a.outer), inf(b.outer), sup(a.outer), sup(b.outer)
    lo, slo = la > lb ? (la, a.strict_lo) : lb > la ? (lb, b.strict_lo) : (la, a.strict_lo || b.strict_lo)
    hi, shi = ha < hb ? (ha, a.strict_hi) : hb < ha ? (hb, b.strict_hi) : (ha, a.strict_hi || b.strict_hi)
    lo > hi && return _EMPTY_EVIDENCE
    return _tighten(Evidence(_bi(lo, hi), slo, shi,
        _join(a.neg, b.neg), _join(a.zero, b.zero), _join(a.pos, b.pos), false))
end

# Store a sound fact about `u` in the context `ckey`, merging with what is there.
function _store!(u, ckey::Tuple, evidence::Evidence)::Evidence
    k = _ekey(u, ckey)
    old = get(cache, k, nothing)
    new = old === nothing ? evidence : _merge(old, evidence)
    cache[k] = new
    return new
end

function _seed_evidence(rel::Symbol)::Evidence
    rel === _LT && return _tighten(Evidence(outer=_bi(-Inf, 0.0), strict_hi=true, neg=Yes))
    rel === _LE && return _tighten(Evidence(outer=_bi(-Inf, 0.0)))
    rel === _GT && return _tighten(Evidence(outer=_bi(0.0, Inf), strict_lo=true, pos=Yes))
    rel === _GE && return _tighten(Evidence(outer=_bi(0.0, Inf)))
    rel === _EQ && return _tighten(Evidence(outer=_bi(0.0, 0.0), zero=Yes))
    return Evidence(zero=No)
end

const _STATUS_RULES = Dict{Symbol,Tuple{Tuple,Tuple}}(
    _GT => ((:neg, :zero), (:pos,)),
    _GE => ((:neg,), (:pos, :zero)),
    _LT => ((:pos, :zero), (:neg,)),
    _LE => ((:pos,), (:neg, :zero)),
    _EQ => ((:neg, :pos), (:zero,)),
    _NE => ((:zero,), (:neg, :pos)),
)

#----------------------------------------------------------
# Components & Context
# ----------------------------------------------------------
"Split constraints into connected blocks for the engine."
function _components(constraints)::Vector{Comp}
    comps = Comp[
        Comp(g.constraints, g.variables, hash(Tuple(g.keys)))
        for g in _connected_groups(constraints)
    ]
    sort!(comps, by=c -> c.key)
    return comps
end

_as_comps(comps::Vector{Comp}) = comps
_as_comps(domain::SymDomain) = _components(domain.constraints)
_as_comps(cs::AbstractVector{<:Constraint}) = _components(cs)

"Precompute the blocks of a domain / constraint list when asking many queries."
constraint_components(src) = _as_comps(src)

function _ctx_for(comps::Vector{Comp}, vars, params=Constraint[])::Ctx
    keep = Comp[c for c in comps if any(_in(c.variables), vars)]
    return Ctx(keep, params, _ctx_key(keep))
end

# The part of `ctx` that bears on a sub-expression.
function _restrict_ctx(ctx::Ctx, expr)::Ctx
    isempty(ctx.comps) && return ctx
    vs = _vars_of(expr)
    isempty(vs) && return _EMPTY_CTX
    return _ctx_for(ctx.comps, vs)
end

_ctx_constraints(ctx::Ctx) = vcat(Constraint[c for comp in ctx.comps for c in comp.constraints], Constraint[c for c in ctx.params])

# ---------------------------------------------------------------------------
# Component facts: bounds from univariate affine constraints
# ---------------------------------------------------------------------------
mutable struct _Bnd
    lo::Float64
    hi::Float64
    slo::Bool
    shi::Bool
end
_Bnd() = _Bnd(-Inf, Inf, false, false)

struct CompFacts
    exact::Bool
    feasible::Bool
    algebraic::Bool
end

# Result of contracting a block once with HC4 (cached under `_hkey(comp)`).
#   :unsat   block infeasible
#   :sat     every constraint inside-and-defined on `box` (box is non-empty)
#   :unknown contracted, undecided
struct _Hc4Result
    status::Symbol
    box::Vector{_BI}
end

# update to handle parameters by querying the context and the cache
function _affine_coefficients(expr, iv)
    res = _affine_walk(Symbolics.unwrap(expr), Symbolics.unwrap(iv))
    (res === nothing || isequal(res[1], 0)) && return nothing
    return res
end

function _affine_walk(expr, iv)
    isequal(expr, iv) && return (1, 0)
    any(w -> isequal(Symbolics.unwrap(w), iv), _vars_of(expr)) || return (0, expr)
    SU.iscall(expr) || return nothing

    op = SU.operation(expr)
    args = SU.arguments(expr)

    if op === (+)
        parts = [_affine_walk(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        return (sum(p[1] for p in parts), sum(p[2] for p in parts))
    elseif op === (-)
        parts = [_affine_walk(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        length(parts) == 1 && return (-parts[1][1], -parts[1][2])
        length(parts) == 2 && return (parts[1][1] - parts[2][1], parts[1][2] - parts[2][2])
    elseif op === (*)
        parts = [_affine_walk(arg, iv) for arg in args]
        any(isnothing, parts) && return nothing
        var_parts = filter(p -> !isequal(p[1], 0), parts)
        length(var_parts) > 1 && return nothing
        c = prod(p[2] for p in parts if isequal(p[1], 0); init=1)
        isempty(var_parts) && return (0, c)
        vp = only(var_parts)
        return (vp[1] * c, vp[2] * c)
    elseif op === (/) && length(args) == 2
        lhs, rhs = _affine_walk(args[1], iv), _affine_walk(args[2], iv)
        (lhs === nothing || rhs === nothing) && return nothing
        isequal(rhs[1], 0) && !isequal(rhs[2], 0) &&
            return (lhs[1] / rhs[2], lhs[2] / rhs[2])
    end
    return nothing
end

# (a, c) with residual == a*v + c, both plain numbers, a != 0; else `nothing`.
function _numeric_affine(expr, v::Symbolics.Num)
    aff = _affine_coefficients(expr, v)
    aff === nothing && return nothing
    a, c = _const_value(aff[1]), _const_value(aff[2])
    (a === nothing || c === nothing || a == 0) && return nothing
    return Float64(a), Float64(c)
end

# Intersect with `a*x + c ⋈ 0`; false if the interval became empty.
function _tighten_bound!(b::_Bnd, a::Float64, c::Float64, rel::Symbol)::Bool
    val = -c / a
    op = a > 0 ? rel : _flip_relation(rel)
    if op === _LT || op === _LE
        strict = op === _LT
        if val < b.hi
            b.hi = val
            b.shi = strict
        elseif val == b.hi
            b.shi |= strict
        end
    elseif op === _GT || op === _GE
        strict = op === _GT
        if val > b.lo
            b.lo = val
            b.slo = strict
        elseif val == b.lo
            b.slo |= strict
        end
    elseif op === _EQ
        _tighten_bound!(b, a, c, _LE)
        _tighten_bound!(b, a, c, _GE)
    end
    return b.lo < b.hi || (b.lo == b.hi && !b.slo && !b.shi)
end

function _bounded(box::IntervalBox)
    for i in 1:length(box)
        if isinf(sup(box[i])) || isinf(inf(box[i]))
            return false
        end
    end
    return true
end

function _bound_evidence(b::_Bnd, exact::Bool)::Evidence
    neg = exact && b.lo < 0 ? Yes : Unknown
    pos = exact && b.hi > 0 ? Yes : Unknown
    zer = exact && (b.lo < 0 || (b.lo == 0 && !b.slo)) &&
        (b.hi > 0 || (b.hi == 0 && !b.shi)) ? Yes : Unknown
    return _tighten(Evidence(_bi(b.lo, b.hi), b.slo, b.shi, neg, zer, pos, false))
end

# FIX: CompFacts is (exact, feasible, algebraic); the old call had the first two swapped.
function _compute_facts(comp::Comp)::CompFacts
    ckey = (comp.key,)
    bnds = Dict{Symbolics.Num,_Bnd}(v => _Bnd() for v in comp.variables)
    feasible = true
    exact = true
    for c in comp.constraints
        rel = c.relation.relation
        r = Symbolics.unwrap(c.relation.residual)
        vs = _vars_of(r)
        if isempty(vs)                                  # constant constraint
            val = _const_value(r)
            val === nothing || _holds(rel, val) || (feasible = false)
            continue
        end
        _store!(r, ckey, _seed_evidence(rel))               # the constraint's own residual
        if length(vs) == 1 && rel !== _NE
            aff = _numeric_affine(r, vs[1])
            if aff !== nothing
                _tighten_bound!(bnds[vs[1]], aff[1], aff[2], rel) || (feasible = false)
                continue
            end
        end
        exact = false
    end
    vars = Dict{Symbolics.Num,Evidence}()
    for v in comp.variables
        evidence = feasible ? _bound_evidence(bnds[v], exact) : _EMPTY_EVIDENCE
        vars[v] = evidence
        _store!(Symbolics.unwrap(v), ckey, evidence)
    end
    algebraic = all(c -> _is_algebraic(c.relation.residual), comp.constraints)
    facts = CompFacts(exact, feasible, algebraic)
    cache[_fkey(comp)] = facts
    return facts
end

function _facts(comp::Comp)::CompFacts
    hit = get(cache, _fkey(comp), nothing)
    return hit === nothing ? _compute_facts(comp) : hit
end

# Current knowledge about a variable (HC4-refined entries live in the cache).
function _leaf_evidence(v::Symbolics.Num, comp::Comp)::Evidence
    facts = _facts(comp)
    facts.feasible || return _EMPTY_EVIDENCE
    key = _ekey(Symbolics.unwrap(v), _ctx_key(comp))
    hit = get(cache, key, nothing)
    hit === nothing || return hit
    _compute_facts(comp)                  # evicted, or new environment: republish bounds and seeds
    return get(cache, key, Evidence())    # unreachable in practice; top is a sound last resort
end

#------------------------------------------------------------
# Sign algebra: which signs can the value still take? 
#------------------------------------------------------------
struct _Signs
    neg::Bool
    zero::Bool
    pos::Bool
end

const _ANY_SIGN = _Signs(true, true, true)

_signs(i::Evidence) = _Signs(i.neg !== No, i.zero !== No, i.pos !== No)
_hasvals(s::_Signs) = s.neg || s.zero || s.pos
_s_neg(s::_Signs) = _Signs(s.pos, s.zero, s.neg)
_s_inv(s::_Signs) = _Signs(s.neg, false, s.pos)        # 1/0 is undefined
_s_mul(a::_Signs, b::_Signs) = _Signs(
    (a.neg && b.pos) || (a.pos && b.neg),
    (a.zero && _hasvals(b)) || (b.zero && _hasvals(a)),
    (a.pos && b.pos) || (a.neg && b.neg))
_s_add(a::_Signs, b::_Signs) = _Signs(
    (a.neg && _hasvals(b)) || (b.neg && _hasvals(a)),
    (a.zero && b.zero) || (a.pos && b.neg) || (a.neg && b.pos),
    (a.pos && _hasvals(b)) || (b.pos && _hasvals(a)))

function _s_powint(a::_Signs, n::Int)
    n == 0 && return _Signs(false, false, _hasvals(a))
    n < 0 && return _s_powint(_s_inv(a), -n)
    return iseven(n) ? _Signs(false, a.zero, a.neg || a.pos) : a
end

# constant exponent: only the base's signs are needed
function _s_pow(a::_Signs, p::Real)
    if isinteger(p) && abs(p) < 1_000_000
        return _s_powint(a, Int(p))
    end
    # non-integer: negative base undefined, 0^p only defined for p > 0
    return _Signs(false, p > 0 && a.zero, a.pos)
end

# non-constant exponent: both operands are evidence
function _s_pow(a::_Signs, b::_Signs)
    hasb = _hasvals(b)
    return _Signs(
        a.neg && hasb,                          # neg^(odd integer) can be negative
        a.zero && b.pos,                        # 0^positive = 0 (0^negative is undefined)
        hasb && (a.pos || a.neg || (a.zero && b.zero)))  # pos^anything, neg^even, 0^0 = 1
end

function _sign_rule(op, args, kids)::_Signs
    S = _signs.(kids)
    n = length(S)
    if op === (+)
        return reduce(_s_add, S)
    elseif op === (*)
        return reduce(_s_mul, S)
    elseif op === (/) && n == 2
        return _s_mul(S[1], _s_inv(S[2]))
    elseif op === (^)
        p = length(args) >= 2 ? _const_value(args[2]) : nothing
        if p !== nothing && n >= 1
            return _s_pow(S[1], p)
        elseif n == 2
            return _s_pow(S[1], S[2])
        end
        return _ANY_SIGN
    elseif n == 1
        s = S[1]
        (op === exp || op === exp2 || op === exp10 || op === cosh) &&
            return _Signs(false, false, _hasvals(s))
        (op === sinh || op === tanh || op === atan || op === asinh) && return s
        op === abs && return _Signs(false, s.zero, s.neg || s.pos)
        op === sqrt && return _Signs(false, s.zero, s.pos)
    end
    return _ANY_SIGN
end

const _UNARY_INTERVAL_OPS = (exp, exp2, exp10, log, log2, log10, sin, cos, tan,
    asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh, abs, sqrt)

# -> (outer, strict_lo, strict_hi)
function _interval_rule(op, args, kids)
    X = _BI[k.outer for k in kids]
    n = length(kids)
    if op === (+)
        return reduce(+, X), any(k -> k.strict_lo, kids), any(k -> k.strict_hi, kids)
    elseif op === (*)
        return reduce(*, X), false, false
    elseif op === (-)
        n == 1 && return -X[1], kids[1].strict_hi, kids[1].strict_lo
        n == 2 && return X[1] - X[2], kids[1].strict_lo || kids[2].strict_hi,
        kids[1].strict_hi || kids[2].strict_lo
    elseif op === (/) && n == 2
        return X[1] / X[2], false, false
    elseif op === (^) && n == 2
        p = _const_value(args[2])
        if p !== nothing && isinteger(p) && abs(p) < 1_000_000
            return pow(X[1], Int(p)), false, false
        end
        return pow(X[1], X[2]), false, false
    elseif n == 1 && op in _UNARY_INTERVAL_OPS
        return op(X[1]), false, false
    end
    return _entire_bi(), false, false
end

const _ZERO_PRESERVING = (sin, tan, asin, atan, sinh, tanh, asinh, atanh, abs, sqrt)

# Is the node identically zero because of how its children are?
function _ident_rule(op, args, kids)::Bool
    z = Bool[k.ident_zero for k in kids]
    isempty(z) && return false
    if op === (*)
        return any(z)
    elseif op === (+) || op === (-)
        return all(z)
    elseif op === (/)
        return length(z) == 2 && z[1] && !z[2]
    elseif op === (^)
        p = length(args) == 2 ? _const_value(args[2]) : nothing
        return z[1] && p !== nothing && p > 0
    elseif length(z) == 1 && op in _ZERO_PRESERVING
        return z[1]
    end
    return false
end

# Evidence for a call node from its children's Evidence (stages 2–4).
function _combine(op, args, kids::Vector{Evidence})::Evidence
    any(k -> isempty_interval(k.outer), kids) && return _EMPTY_EVIDENCE
    _ident_rule(op, args, kids) && return _IDENT_ZERO
    outer, slo, shi = _interval_rule(op, args, kids)
    s = _sign_rule(op, args, kids)
    return _tighten(Evidence(outer, slo, shi,
        s.neg ? Unknown : No, s.zero ? Unknown : No, s.pos ? Unknown : No, false))
end

function _derive(u, ctx::Ctx)::Evidence
    for comp in ctx.comps
        v = _as_num(u)
        _in(v, comp.variables) && return _leaf_evidence(v, comp)
    end
    SU.iscall(u) || return Evidence()                       # unconstrained symbol / parameter
    op = SU.operation(u)
    args = SU.arguments(u)
    kids = Evidence[_infer_evidence(a, _restrict_ctx(ctx, a)) for a in args]
    return _combine(op, args, kids)
end

_lit_interval(v::Union{Integer,AbstractFloat}) = _bi(v)
function _lit_interval(v::Real)             # Rational / Irrational: widen by an ulp
    x = Float64(v)
    return _bi(prevfloat(x), nextfloat(x))
end

function _literal_evidence(v::Real)::Evidence
    isfinite(v) || return Evidence()
    v == 0 && return _IDENT_ZERO
    iv = _lit_interval(v)
    return v > 0 ? Evidence(outer=iv, neg=No, zero=No, pos=Yes) :
           Evidence(outer=iv, neg=Yes, zero=No, pos=No)
end

# Stages 1–4. Never pavings, so children never trigger expensive work.
function _infer_evidence(u, ctx::Ctx)::Evidence
    c = _const_value(u)
    c !== nothing && return _literal_evidence(c)
    hit = get(cache, _ekey(u, ctx.key), nothing)
    hit !== nothing && _decided(hit, _ALL) && return hit
    return _store!(u, ctx.key, _derive(u, ctx))
end

"""
    _hc4_refine!(comp) -> _Contracted
 
Contract one block once (via `_contract`), cache the result under `_hkey(comp)`,
and publish the refined variable bounds as evidence so every later query on the
block benefits. A proven-infeasible block is also recorded in its `CompFacts`.
The cached `_Contracted` is exactly what `_pave_contracted` needs.
"""
function _hc4_refine!(comp::Comp)::_Contracted
    facts = _facts(comp)
    facts.feasible || return _infeasible(length(comp.variables))

    key = _hkey(comp)
    res = get(cache, key, nothing)
    if res === nothing
        ivs = _BI[_leaf_evidence(v, comp).outer for v in comp.variables]
        res = if any(isempty_interval, ivs)
            _infeasible(length(ivs))
        elseif facts.exact
            # Every constraint is a univariate affine bound, already folded into
            # `ivs` with its strictness. HC4 cannot see strictness through a closed
            # box, so this shortcut is needed, not just an optimisation.
            _Contracted(:sat, ivs, UInt64(0), _NO_TAPES)
        else
            _contract(_make_box(ivs), comp.constraints, comp.variables)
        end
        cache[key] = res
    end

    res.status === :unsat &&
        (cache[_fkey(comp)] = CompFacts(facts.exact, false, facts.algebraic))

    ckey = _ctx_key(comp)
    for (i, v) in enumerate(comp.variables)
        ev = res.status === :unsat ? _EMPTY_EVIDENCE : _tighten(Evidence(outer=res.box[i]))
        _store!(Symbolics.unwrap(v), ckey, ev)
    end
    return res
end

"""
    _joint_system(comps, params, extra_vars)
 
Refine every block (cached; publishes tightened bounds) and assemble the joint
system: variables, refined boxes (`ivs`, same order) and all constraints.
`extra_vars` that no block owns (e.g. a free variable of the probed expression) are
added with an unbounded interval. Returns `nothing` if some block is infeasible.
"""
function _joint_system(comps::Vector{Comp}, params::Vector{Constraint}, extra_vars)
    refined = _Contracted[_hc4_refine!(c) for c in comps]
    any(r -> r.status === :unsat, refined) && return nothing

    variables = Symbolics.Num[v for c in comps for v in c.variables]
    ivs = _BI[iv for r in refined for iv in r.box]
    for v in extra_vars
        any(c -> _in(v, c.variables), comps) && continue
        push!(variables, v)
        push!(ivs, _entire_bi())
    end
    constraints = Constraint[c for comp in comps for c in comp.constraints]
    append!(constraints, params)
    return (variables=variables, ivs=ivs, constraints=constraints)
end

# ---------------------------------------------------------------------------
# Expression-specific strategies
# ---------------------------------------------------------------------------
# Each strategy is `(u, ctx, evidence) -> Evidence` and must return only sound facts
# (it may refine `evidence`; the pipeline merges the result). 
# Planned: single variable polynomials (Sturm), centered/mean-value forms. 
# Affine expressions need none: their variable bounds are exact and handled by stages 3 and 7.

const _STRATEGIES = Function[]

function _expr_evidence(expr, ctx::Ctx, want::Tuple)::Evidence
    u = Symbolics.unwrap(expr)
    evidence = _infer_evidence(u, ctx)
    _decided(evidence, want) && return evidence
    for strategy in _STRATEGIES
        evidence = _store!(u, ctx.key, strategy(u, ctx, evidence))
        _decided(evidence, want) && return evidence
    end

    # Refining the blocks publishes tighter variable bounds, so interval
    # inference on `u` may now decide without any probe.
    sys = _joint_system(ctx.comps, ctx.params, _vars_of(u))
    sys === nothing && return _store!(u, ctx.key, _EMPTY_EVIDENCE)
    evidence = _infer_evidence(u, ctx)
    _decided(evidence, want) && return evidence

    box = _make_box(sys.ivs)
    miss = Symbol[]
    for w in want
        _answer(evidence, w) !== Unknown && continue
        probe = Constraint(0, SymRelation(u, _rel_from_want(w)))
        # probe first: it is the one constraint that must never be dropped
        contracted = _contract(box, vcat(Constraint[probe], sys.constraints), sys.variables)
        if w === :zero && contracted.status === :unknown &&
            !contracted.prep.dropped && !isempty(contracted.prep.tapes)
            # The probe is first, so tape 1 and its residual are the equality
            # being queried. Do not build a certificate if anything was dropped.
            cert = _ZeroCertificate(probe.relation.residual, sys.variables, contracted.prep.tapes[1])
            ans = _to_answer(_pave_contracted(contracted; certify=cert))
        else
            ans = _to_answer(_pave_contracted(contracted))
        end
        if ans === Unknown
            push!(miss, w)
        else
            evidence = _store!(u, ctx.key, _set_answer(evidence, w, ans))
        end
    end
    isempty(miss) && return evidence

    # further stages for `miss` ...
    return _store!(u, ctx.key, _tighten(evidence))
end

# ---------------------------------------------------------------------------
# 10. Public API
# ---------------------------------------------------------------------------
"""
    expr_evidence(expr, src; want=(:neg,:zero,:pos)) -> Evidence
 
`src` is a `SymDomain`, a vector of `Constraint`, or the result of
`constraint_components`. Only the answers listed in `want` are pursued; the
others are filled in if they came free. The context itself is assumed
satisfiable; `No` means context ∧ probe is unsatisfiable.
"""
expr_evidence(expr, src; want::Tuple=_ALL) =
    _expr_evidence(expr, _ctx_for(_as_comps(src), _vars_of(expr)), want)

can_be_negative(expr, src) = expr_evidence(expr, src; want=(:neg,)).neg
# needs updating
can_be_zero(expr, src) = expr_evidence(expr, src; want=(:zero,)).zero
can_be_positive(expr, src) = expr_evidence(expr, src; want=(:pos,)).pos

function is_positive(expr, src)::Bool
    i = expr_evidence(expr, src; want=(:neg, :zero))
    return i.neg === No && i.zero === No
end

function is_negative(expr, src)::Bool
    i = expr_evidence(expr, src; want=(:pos, :zero))
    return i.pos === No && i.zero === No
end

is_nonnegative(expr, src)::Bool = can_be_negative(expr, src) === No
is_nonpositive(expr, src)::Bool = can_be_positive(expr, src) === No

"Divisibility: `expr` provably never vanishes."
is_nonzero(expr, src)::Bool = can_be_zero(expr, src) === No

function _sat_comp(comp::Comp)::Answer
    key = (:sat, comp.key, _env())
    hit = get(cache, key, nothing)
    hit === nothing || return hit
    ans = _to_answer(_pave_contracted(_hc4_refine!(comp)))
    cache[key] = ans
    return ans
end

"""
    satisfiable(src) -> Answer
 
Is there a point satisfying all constraints? Blocks are independent, so the
result is the conjunction of per-block answers (each cached on its own).
"""
function satisfiable(src)::Answer
    result = Yes
    for comp in _as_comps(src)
        a = _sat_comp(comp)
        a === No && return No
        a === Unknown && (result = Unknown)
    end
    return result
end

satisfiable(domain::SymDomain, extra::AbstractVector{SymRelation}=SymRelation[]) =
    satisfiable(vcat(domain.constraints, Constraint[Constraint(0, r) for r in extra]))

_all_no(expr, ctx::Ctx, fields) =
    all(f -> _answer(_expr_evidence(expr, ctx, (f,)), f) === No, fields)

"""
    relation_status(rel::SymRelation, src) -> Symbol
 
- `:redundant`  `rel` holds everywhere on the domain
- `:infeasible` `rel` holds nowhere on the domain
- `:active`     both it and its negation are (possibly) satisfiable
"""
function relation_status(rel::SymRelation, src)::Symbol
    ctx = _ctx_for(_as_comps(src), _vars_of(rel.residual))
    redundant, infeasible = _STATUS_RULES[rel.relation]
    _all_no(rel.residual, ctx, redundant) && return :redundant
    _all_no(rel.residual, ctx, infeasible) && return :infeasible
    return :active
end

# ---------------------------------------------------------------------------
# 11. DESys / DETree conveniences
# ---------------------------------------------------------------------------

factor_evidence(factor, sys::DESys; want::Tuple=_ALL) = expr_evidence(factor, sys.domain; want=want)

"""
Can `factor` be divided out? A parameter that no constraint mentions is treated
as generically non-zero; anything else must be provably non-zero on the domain.
"""
function factor_divisible(factor, sys::DESys)::Bool
    ctx = _ctx_for(_components(sys.domain.constraints), _vars_of(factor))
    _contains_equal(sys.ps, factor) && isempty(ctx.comps) && return true
    return _answer(_expr_evidence(factor, ctx, (:zero,)), :zero) === No
end

function _can_divide_by(expr::Symbolics.Num, sys::DESys)
    _contains_equal(sys.dvs, expr) && return false
    _has_depvar_or_diff(expr, sys) && return false
    return factor_divisible(expr, sys)
end

#=
I doubt the usefulness of some of these helpers since predicate functions 
require a single argument, so would have to be defined inside the context of another function
these could still make it a bit simpler I suppose
=#

"""
Return syntactic numerator-factor candidates shared by every addend.
This function deliberately does not decide whether a factor is cancellable. It
only computes a conservative candidate list; `factor_divisible` remains the
authority for domain-aware cancellation.
"""
function common_divisors(expr, sys::DESys)
    expr === nothing && throw(ArgumentError("input expression cannot be empty"))
    normalized = unwrap(simplify(expand(expand_derivatives(wrap(expr)))))
    addends = _additive_terms(normalized)
    isempty(addends) && return Any[]

    shared = _multiplicative_factors(first(addends))
    for addend in Iterators.drop(addends, 1)
        available = _multiplicative_factors(addend)
        retained = Any[]
        for candidate in shared
            index = findfirst(factor -> isequal(factor, candidate), available)
            index === nothing || (push!(retained, candidate); deleteat!(available, index))
        end
        shared = retained
        isempty(shared) && break
    end

    # Numeric constants do not improve an equation and can introduce
    # avoidable type conversions during division.
    [
        wrap(factor) for factor in _ordered_unique(shared)
                         if !(SU.unwrap_const(Symbolics.unwrap(factor)) isa Number)
    ]
end

