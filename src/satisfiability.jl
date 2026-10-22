#------------------------------------------------
# sat specific utils
#------------------------------------------------

_answer(i::Evidence, w::Symbol) = w === :neg ? i.neg : w === :zero ? i.zero : i.pos
_decided(i::Evidence, want) = all(w -> _answer(i, w) !== Unknown, want)
_ekey(u, ckey::Tuple) = (:evidence, u, ckey, _env())

function _with(i::Evidence; outer=i.outer, strict_lo=i.strict_lo, strict_hi=i.strict_hi,
    neg=i.neg, zero=i.zero, pos=i.pos, ident_zero=i.ident_zero)
    return Evidence(outer, strict_lo, strict_hi, neg, zero, pos, ident_zero)
end

_set_answer(i::Evidence, w::Symbol, a::Answer) =
    w === :neg ? _with(i; neg=a) : w === :zero ? _with(i; zero=a) : _with(i; pos=a)

_join(x::Answer, y::Answer) = x === y ? x : x === Unknown ? y : y === Unknown ? x : No

"""
Make an Evidence self-consistent: answers follow from the interval and the interval
follows from the answers. Contradictions collapse to the empty Evidence.
"""
function _tighten(i::Evidence)::Evidence
    i.ident_zero && return _IDENT_ZERO
    o = i.outer
    isempty(o) && return _EMPTY_EVIDENCE
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
    (isempty(a.outer) || isempty(b.outer)) && return _EMPTY_EVIDENCE
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
        Comp(g.constraints, g.variables, Set(g.variables), hash(Tuple(g.keys)))
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

function _ctx_for(comps::Vector{Comp}, vars)::Ctx
    keep = Comp[c for c in comps if any(v -> v in c.variables, vars)]
    length(keep) == length(ctx.comps) && return ctx
    return Ctx(keep, _ctx_key(keep))
end

# The part of `ctx` that bears on a sub-expression.
function _restrict_ctx(ctx::Ctx, expr)::Ctx
    isempty(ctx.comps) && return ctx
    vs = _vars_of(expr)
    isempty(vs) && return _EMPTY_CTX
    return _ctx_for(ctx, vs)
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

function _bound_evidence(b::_Bnd, exact::Bool)::Evidence
    neg = exact && b.lo < 0 ? Yes : Unknown
    pos = exact && b.hi > 0 ? Yes : Unknown
    zer = exact && (b.lo < 0 || (b.lo == 0 && !b.slo)) &&
        (b.hi > 0 || (b.hi == 0 && !b.shi)) ? Yes : Unknown
    return _tighten(Evidence(_bi(b.lo, b.hi), b.slo, b.shi, neg, zer, pos, false))
end

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
    facts = CompFacts(feasible, exact)
    cache[(:comp, comp.key)] = facts
    return facts
end

function _facts(comp::Comp)::CompFacts
    hit = get(cache, (:comp, comp.key), nothing)
    return hit === nothing ? _compute_facts(comp) : hit
end

# Current knowledge about a variable (HC4-refined entries live in the cache).
function _leaf_evidence(v::Symbolics.Num, comp::Comp)::Evidence
    facts = _facts(comp)
    facts.feasible || return _EMPTY_EVIDENCE
    return get(cache, _ekey(Symbolics.unwrap(v), _ctx_key(comp)), facts.vars[v])
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

function _sign_rule(op, args, kids)::_Signs
    S = _signs.(kids)
    n = length(S)
    if op === (+)
        return reduce(_s_add, S)
    elseif op === (*)
        return reduce(_s_mul, S)
    elseif op === (/) && n == 2
        return _s_mul(S[1], _s_inv(S[2]))
    elseif op === (^) && n == 2
        p = _const_value(args[2])
        if p !== nothing && isinteger(p) && abs(p) < 1_000_000
            return _s_powint(S[1], Int(p))
        elseif p !== nothing
            return _Signs(false, p > 0 && S[1].zero, S[1].pos)
        end
        return (!S[1].neg && !S[1].zero) ? _Signs(false, false, S[1].pos) : _ANY_SIGN
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
            return X[1]^Int(p), false, false
        end
        return X[1]^X[2], false, false
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
    any(k -> isempty(k.outer), kids) && return _EMPTY_EVIDENCE
    _ident_rule(op, args, kids) && return _IDENT_ZERO
    outer, slo, shi = _interval_rule(op, args, kids)
    s = _sign_rule(op, args, kids)
    return _tighten(Evidence(outer, slo, shi,
        s.neg ? Unknown : No, s.zero ? Unknown : No, s.pos ? Unknown : No, false))
end

function _derive(u, ctx::Ctx)::Evidence
    for comp in ctx.comps
        v = _as_num(u)
        v in comp.varset && return _leaf_evidence(v, comp)
    end
    SU.iscall(u) || return Evidence()                       # unconstrained symbol / parameter
    op = SU.operation(u)
    args = SU.arguments(u)
    kids = Evidence[_cheap_evidence(a, _restrict_ctx(ctx, a)) for a in args]
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
function _cheap_evidence(u, ctx::Ctx)::Evidence
    c = _const_value(u)
    c !== nothing && return _literal_evidence(c)
    hit = get(cache, _ekey(u, ctx.key), nothing)
    hit !== nothing && _decided(hit, _ALL) && return hit
    return _store!(u, ctx.key, _derive(u, ctx))
end

# -----------------------------------------------------------
# Paving connectors
# -----------------------------------------------------------

# Contract a block's variable bounds once; refined bounds go into the cache so
# every later query in the block benefits. false = block proven infeasible.
function _hc4_refine!(comp::Comp)::Bool
    key = (:hc4, comp.key)
    hit = get(cache, key, nothing)
    hit === nothing || return hit
    facts = _facts(comp)
    ok = facts.feasible
    if ok && !facts.exact
        ckey = _ctx_key(comp)
        ivs = _BI[_leaf_evidence(v, comp).outer for v in comp.variables]
        ok, ivs = _contract(comp.constraints, comp.variables, ivs)
        for (i, v) in enumerate(comp.variables)
            _store!(Symbolics.unwrap(v), ckey, ok ? _tighten(Evidence(outer=ivs[i])) : _EMPTY_EVIDENCE)
        end
        ok || (cache[(:comp, comp.key)] = CompFacts(false, facts.exact))
    end
    cache[key] = ok
    return ok
end

"""
Is there a point satisfying `cons` inside the box `ivs`?
Yes = an inner box exists; No = nothing survives; Unknown = only boundary boxes.
"""
function _pave_answer(cons, vars, ivs::Vector{_BI})::Answer
    feasible, inner, boundary, dropped = _pave_boxes(cons, vars, ivs)
    feasible || return No
    isempty(inner) || return dropped ? Unknown : Yes
    return isempty(boundary) ? No : Unknown
end

function _sample_points(ivs::Vector{_BI})
    n = length(ivs)
    lo = [inf(i) for i in ivs]
    hi = [sup(i) for i in ivs]
    pts = Vector{Vector{Float64}}([(lo .+ hi) ./ 2])
    if n <= 6
        for m in 0:(2^n-1)
            push!(pts, [((m >> (i - 1)) & 1) == 1 ? hi[i] : lo[i] for i in 1:n])
        end
    else
        push!(pts, lo)
        push!(pts, hi)
    end
    return pts
end

const _NO_WITNESS = (neg=false, zero=false, pos=false)

# Existence certificates. Points of an inner box of the context satisfy every
# constraint; evaluating `u` there with interval arithmetic gives a rigorous sign.
# Zero is certified by the intermediate value theorem when both signs occur in
# one box on which `u` stays bounded (no pole).
function _find_witnesses(u, cons, vars, ivs::Vector{_BI})
    feasible, inner, _, dropped = _pave_boxes(cons, vars, ivs)
    feasible || return _NO_WITNESS
    f = SymRelation(Symbolics.wrap(u), _EQ)
    (dropped || isempty(inner) || !_compilable(f)) && return _NO_WITNESS
    tape = compile_hc4(f, vars)
    ws = Vector{_BI}(undef, tape.tape_len)
    n = length(vars)
    boxes = length(inner) > 64 ? partialsort(inner, 1:64; by=b -> -diam(b)) : inner
    neg = pos = zer = false
    for B in boxes
        bi = _BI[_bi(B[i]) for i in 1:n]
        for i in 1:n
            ws[i] = bi[i]
        end
        range = _execute_forward!(tape, ws)
        bounded = !isempty(range) && isfinite(inf(range)) && isfinite(sup(range))
        bn = bp = false
        for p in _sample_points(bi)
            for i in 1:n
                ws[i] = _bi(p[i])
            end
            r = _execute_forward!(tape, ws)
            isempty(r) && continue
            sup(r) < 0 && (bn = true)
            inf(r) > 0 && (bp = true)
            inf(r) == 0 && sup(r) == 0 && (zer = true)
        end
        neg |= bn
        pos |= bp
        bounded && bn && bp && (zer = true)
        neg && pos && zer && break
    end
    return (neg=neg, zero=zer, pos=pos)
end

# Variables of the paving problem and their (windowed) starting intervals.
function _probe_space(u, ctx::Ctx)
    vars = Symbolics.Num[]
    seen = Set{Symbolics.Num}()
    for comp in ctx.comps, v in comp.variables
        v in seen || (push!(seen, v); push!(vars, v))
    end
    for v in _vars_of(u)
        v in seen || (push!(seen, v); push!(vars, v))
    end
    ivs = _BI[_window(_var_outer(v, ctx)) for v in vars]
    return vars, ivs
end

function _var_outer(v::Symbolics.Num, ctx::Ctx)::_BI
    for comp in ctx.comps
        v in comp.variables && return _leaf_evidence(v, comp).outer
    end
    return _entire_bi()
end

const _PROBE_REL = (neg=_LT, zero=_EQ, pos=_GT)

# Is `expr ⋈ 0` (⋈ chosen by `w`) satisfiable together with the context?
function _probe(u, ctx::Ctx, cons, vars, ivs, w::Symbol)::Answer
    key = (:probe, u, ctx.key, w, _env())
    hit = get(cache, key, nothing)
    hit === nothing || return hit
    extra = Constraint(0, SymRelation(Symbolics.wrap(u), _PROBE_REL[w]))
    ans = _pave_answer(vcat(cons, [extra]), vars, ivs)
    cache[key] = ans
    return ans
end

# Stage 7. Witnesses first (they can settle several answers with one paving of
# the context), then one probe paving per answer still open.
function _stage_paving(u, ctx::Ctx, evidence::Evidence, want)::Evidence
    pending = [w for w in want if _answer(evidence, w) === Unknown]
    isempty(pending) && return evidence
    cons = _ctx_constraints(ctx)
    vars, ivs = _probe_space(u, ctx)
    wkey = (:wit, u, ctx.key, _env())
    wit = get(cache, wkey, nothing)
    if wit === nothing
        wit = _find_witnesses(u, cons, vars, ivs)
        cache[wkey] = wit
    end
    for w in pending
        wit[w] && (evidence = _set_answer(evidence, w, Yes))
    end
    for w in pending
        _answer(evidence, w) === Unknown || continue
        evidence = _set_answer(evidence, w, _probe(u, ctx, cons, vars, ivs, w))
    end
    return _store!(u, ctx.key, _tighten(evidence))
end

# ---------------------------------------------------------------------------
# Expression-specific strategies
# ---------------------------------------------------------------------------
# Each strategy is `(u, ctx, evidence) -> Evidence` and must return only sound facts
# (it may refine `evidence`; the pipeline merges the result). 
# Planned: single variable polynomials (Sturm), centered/mean-value forms. 
# Affine expressions need none: their variable bounds are exact and handled by stages 3 and 7.

const _STRATEGIES = Function[]


# ---------------------------------------------------------------------------
# 10. Public API
# ---------------------------------------------------------------------------
function _expr_evidence(expr, ctx::Ctx, want::Tuple)::Evidence
    u = Symbolics.unwrap(expr)
    evidence = _cheap_evidence(u, ctx)
    _decided(evidence, want) && return evidence
    for strategy in _STRATEGIES
        evidence = _store!(u, ctx.key, strategy(u, ctx, evidence))
        _decided(evidence, want) && return evidence
    end
    all(_hc4_refine!, ctx.comps) || return _store!(u, ctx.key, _EMPTY_EVIDENCE)
    evidence = _cheap_evidence(u, ctx)
    _decided(evidence, want) && return evidence
    return _stage_paving(u, ctx, evidence, want)
end


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
    facts = _facts(comp)
    ans = if !facts.feasible
        No
    elseif facts.exact
        Yes
    elseif !_hc4_refine!(comp)
        No
    else
        ivs = _BI[_window(_leaf_evidence(v, comp).outer) for v in comp.variables]
        _pave_answer(comp.constraints, comp.variables, ivs)
    end
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

