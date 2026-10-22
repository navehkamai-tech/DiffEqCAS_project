#------------------------------------------------
# sat specific utils
#------------------------------------------------

_answer(i::Evidence, w::Symbol) = w === :neg ? i.neg : w === :zero ? i.zero : i.pos
_decided(i::Evidence, want) = all(w -> _answer(i, w) !== Unknown, want)

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
    return EVIDENCE(outer, slo, shi, neg, zer, pos, false)
end

"Combine two sound facts about the same expression in the same context."
function _merge(a::Evidence, b::Evidence)::Evidence
    (a.ident_zero || b.ident_zero) && return _IDENT_ZERO
    (isempty(a.outer) || isempty(b.outer)) && return _EMPTY_EVIDENCE
    la, lb, ha, hb = inf(a.outer), inf(b.outer), sup(a.outer), sup(b.outer)
    lo, slo = la > lb ? (la, a.strict_lo) : lb > la ? (lb, b.strict_lo) : (la, a.strict_lo || b.strict_lo)
    hi, shi = ha < hb ? (ha, a.strict_hi) : hb < ha ? (hb, b.strict_hi) : (ha, a.strict_hi || b.strict_hi)
    lo > hi && return _EMPTY_EVIDENCE
    return _tighten(EVIDENCE(_bi(lo, hi), slo, shi,
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
    op = a > 0 ? rel : _flip(rel)
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
    facts = CompFacts(feasible, exact, vars)
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
    hit = get(cache, _ikey(u, ctx.key), nothing)
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
        ok || (cache[(:comp, comp.key)] = CompFacts(false, facts.exact, facts.vars))
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
    extra = DomConstraint(0, SymRelation(Symbolics.wrap(u), _PROBE_REL[w]))
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
 
`src` is a `SymDomain`, a vector of `DomConstraint`, or the result of
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
    satisfiable(vcat(domain.constraints, DomConstraint[DomConstraint(0, r) for r in extra]))

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

# Does `expr` mention a dependent variable or a derivative?
function _has_depvar_or_diff(expr, sys::DESys)
    dvs = [Symbolics.unwrap(d) for d in sys.dvs]
    walk(e) = any(d -> isequal(d, e), dvs) ||
        (SU.iscall(e) && (SU.operation(e) isa Differential || any(walk, SU.arguments(e))))
    return walk(Symbolics.unwrap(expr))
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


# everything from here on should be deleted once I verify
function factor_evidence(factor, sys::DESys)
    if _contains_equal(sys.ps, factor) && isempty(_evidence_domain(sys.domain, factor).blocks)
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, undetermined)
    end
    return domain_evidence(factor, sys.domain)
end

factor_sign(factor, sys::DESys) = factor_evidence(factor, sys).sign
factor_sign(factor, sys::DETree) =
    length(sys.active) == 1 ?
    factor_sign(factor, sys.nodes[first(sys.active)].system) :
    throw(ArgumentError("factor sign requires one selected branch"))

factor_divisibility(factor, sys::DESys) = factor_evidence(factor, sys).divisibility
factor_divisibility(factor, sys::DETree) =
    length(sys.active) == 1 ?
    factor_divisibility(factor, sys.nodes[first(sys.active)].system) :
    throw(ArgumentError("factor divisibility requires one selected branch"))

# ===========================================================================
# 1. Domain-Level Evidence & Feasibility Engine (Pure SymDomain, no DESys)
# ===========================================================================


function _evidence_domain(domain::SymDomain, expr)
    expr_variables = Symbolics.get_variables(Symbolics.unwrap(expr))
    relevant = DomBlock[
        b for b in domain.blocks if any(v -> _contains_equal(b.variables, v), expr_variables)]
    return EvidenceDomain(domain, relevant, blocks_content_key(domain, relevant), nothing)
end

function _ctx_domain!(ctx::EvidenceDomain)
    ctx.sub === nothing && (ctx.sub = subdomain(ctx.source, ctx.blocks))
    return ctx.sub
end

"""
    domain_evidence(expr, domain::SymDomain) -> ConstraintEvidence

Staged sign, bound, and zero-set inference for `expr` over `domain`.
Runs cheap algebraic/interval stages first (`_prime_domain_bounds!`, `_infer_tree`,
`_affine_factor_evidence`) before falling back to branch-and-prune paving.
"""
function domain_evidence(expr, domain::SymDomain)
    ctx = _evidence_domain(domain, expr)
    key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
    haskey(cache, key) && return cache[key]
    result = _domain_evidence_uncached(expr, ctx)
    cache[key] = result
    return result
end

function _domain_evidence_uncached(expr, ctx::EvidenceDomain)
    # Stage 1: Prime the global cache with exact 1D affine bounds from domain blocks
    _prime_domain_bounds!(ctx)

    # Stage 2: Fast structural and interval arithmetic tree walk
    best_evidence = _infer_tree(expr, ctx)
    if best_evidence.divisibility !== undetermined || isempty(ctx.blocks)
        return best_evidence
    end

    # Stage 3+: Progressive refinement (Affine -> Centered -> Sturm -> Paved)
    for stage in (
        _affine_factor_evidence,
        _centered_factor_evidence,
        _sturm_factor_evidence,
        _paved_factor_evidence,
    )
        result = stage(expr, ctx)
        if result !== nothing
            new_bound = intersect_interval(best_evidence.bound, result.bound)
            new_sign = result.sign !== undetermined ? result.sign : best_evidence.sign
            new_divis = result.divisibility !== undetermined ? result.divisibility : best_evidence.divisibility
            if new_divis === undetermined && (new_sign in (positive, negative) || !(0 in new_bound))
                new_divis = divisible
            end
            best_evidence = ConstraintEvidence(new_bound, new_divis, new_sign)
            best_evidence.divisibility !== undetermined && return best_evidence
        end
    end
    return best_evidence
end

"""
    relation_status(rel::SymRelation, domain::SymDomain) -> Symbol

Classify `rel` (`residual ⋈ 0`) over `domain` using the staged evidence pipeline:
- `:redundant`  if `rel` holds everywhere on `domain`
- `:infeasible` if `rel` holds nowhere on `domain`
- `:active`     if both `rel` and its negation are satisfiable on `domain`
"""
function relation_status(rel::SymRelation, domain::SymDomain)::Symbol
    ctx = _evidence_domain(domain, rel.residual)
    isempty(ctx.blocks) && return :active

    # Fast Path (Stages 1 & 2): Prime 1D affine bounds and run interval/sign tree inference!
    # This resolves 1D intervals (e.g. x > 2 vs x > 0) and sign-definite expressions
    # with ZERO paving overhead.
    _prime_domain_bounds!(ctx) || return :infeasible
    ev = _infer_tree(simplify(rel.residual), ctx)
    lo, hi = inf(ev.bound), sup(ev.bound)
    op = _get_relation(rel)

    if op === (>)
        (lo > 0.0 || ev.sign === positive) && return :redundant
        (hi <= 0.0 || ev.sign in (negative, iszero)) && return :infeasible
    elseif op === (>=)
        (lo >= 0.0 || ev.sign in (positive, iszero)) && return :redundant
        (hi < 0.0 || ev.sign === negative) && return :infeasible
    elseif op === (<)
        (hi < 0.0 || ev.sign === negative) && return :redundant
        (lo >= 0.0 || ev.sign in (positive, iszero)) && return :infeasible
    elseif op === (<=)
        (hi <= 0.0 || ev.sign in (negative, iszero)) && return :redundant
        (lo > 0.0 || ev.sign === positive) && return :infeasible
    elseif op === (==)
        (lo == 0.0 && hi == 0.0 || ev.sign === iszero) && return :redundant
        (lo > 0.0 || hi < 0.0 || ev.divisibility === divisible) && return :infeasible
    elseif op === (!=)
        (lo > 0.0 || hi < 0.0 || ev.divisibility === divisible) && return :redundant
        (lo == 0.0 && hi == 0.0 || ev.sign === iszero) && return :infeasible
    end

    expr_vars = Symbolics.get_variables(Symbolics.unwrap(rel.residual))
    if length(expr_vars) == 1 && _affine_coefficients(Symbolics.unwrap(rel.residual), Symbolics.unwrap(only(expr_vars))) !== nothing
        return :active
    end

    # Fallback (Stages 3 & 4): Future Sturm/Centered stages or HC4Revise Paving
    sub_dom = _ctx_domain!(ctx)
    # 1. Is `rel` itself satisfiable on `sub_dom`?
    rel_sat = _raw_relation_satisfiable(rel, sub_dom, true)
    rel_sat || return :infeasible

    # 2. Is the negation of `rel` satisfiable on `sub_dom`?
    # If the negation cannot be satisfied, `rel` is redundant!
    neg_rel = _negate_relation(rel)
    needs_boundary = (neg_rel.relation === Symbol("=="))
    neg_sat = _raw_relation_satisfiable(neg_rel, sub_dom, needs_boundary)
    return neg_sat ? :active : :redundant
end

# Direct paving check on a single relation without recursing into `add_constraints`
function _raw_relation_satisfiable(rel::SymRelation, sub_dom::SymDomain, include_boundary::Bool)
    all_vars = copy(sub_dom.variables)
    for v in Symbolics.get_variables(Symbolics.unwrap(rel.residual))
        _push_unique!(all_vars, (_as_num(v),))
    end
    sort!(all_vars, by=string)
    c_new = Constraint(rel)
    all_cs = vcat(sub_dom.constraints, [c_new])
    block = DomBlock(all_vars, ConstraintId[c.id for c in all_cs])
    temp_dom = SymDomain(all_cs, [block])
    inner, boundary = _pave_block(temp_dom, temp_dom.blocks[1])
    return include_boundary ? (!isempty(inner) || !isempty(boundary)) : !isempty(inner)
end

# beginning of the pipeline - always called first
function _prime_domain_bounds!(ctx::EvidenceDomain)
    for block in ctx.blocks
        ivs = block.variables
        bounds = Dict(iv => IntervalArithmetic.Interval(-Inf, Inf) for iv in ivs)
        strict_lo = Dict(iv => false for iv in ivs)
        strict_hi = Dict(iv => false for iv in ivs)
        for constraint in constraints_of(ctx.source, block)
            op = _get_relation(constraint.relation)
            op === (!=) && continue
            expr = Symbolics.unwrap(constraint.relation.residual)
            expr_vars = Symbolics.get_variables(expr)
            constraint_ivs = [iv for iv in ivs if _contains_equal(expr_vars, iv)]
            length(constraint_ivs) == 1 || continue
            iv = only(constraint_ivs)
            is_feasible = _update_affine_bound!(bounds, strict_lo, strict_hi, expr, iv, op)
            is_feasible || return false
        end
        # Inject the bounds into the global cache to prime _infer_tree
        for (iv, bound) in bounds
            cache_key = (:constraint_evidence, Symbolics.unwrap(iv), (block_content_key(ctx.source, block),))
            lo, hi = inf(bound), sup(bound)
            s_lo, s_hi = strict_lo[iv], strict_hi[iv]
            sign_state = (hi < 0 || (hi == 0 && s_hi)) ? negative :
                         (lo > 0 || (lo == 0 && s_lo)) ? positive :
                         (lo == 0 && hi == 0) ? iszero : undetermined
            divis_state = (sign_state in (positive, negative) || !(0 in bound)) ? divisible :
                          (sign_state === iszero ? haszero : undetermined)
            cache[cache_key] = ConstraintEvidence(bound, divis_state, sign_state)
        end
    end
    return true
end

function _infer_tree(expr, ctx::EvidenceDomain)
    isequal(expr, 0) && return ConstraintEvidence(interval(0, 0), haszero, iszero)

    # 1. Check existing cache
    local key
    if !SU.iscall(expr)
        var_block = block_of(ctx.source, expr)
        if var_block !== nothing
            key = (:constraint_evidence, Symbolics.unwrap(expr), (block_content_key(ctx.source, var_block),))
        else
            key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
        end
    else
        key = (:constraint_evidence, Symbolics.unwrap(expr), ctx.key)
    end

    if haskey(cache, key)
        return cache[key]
    end

    # 2. Check exact literals
    literal = SU.unwrap_const(Symbolics.unwrap(expr))
    if literal isa Real
        return _evidence_from_literal(literal)
    end

    # 3. Recursive subexpression inference
    simplified = simplify(expr)
    SU.iscall(simplified) || return ConstraintEvidence(interval(-Inf, Inf), undetermined, undetermined)

    op = SU.operation(simplified)
    args = SU.arguments(simplified)

    # Recurse down. If a leaf is undetermined and not cached, this will bubble up.
    children = [_infer_tree(arg, ctx) for arg in args]
    result = _combine_child_evidence(op, children)

    # Only cache if we actually deduced something useful to save memory
    if result.sign !== undetermined || result.divisibility !== undetermined
        cache[key] = result
    end

    return result
end

function _combine_child_evidence(op, children)
    # 1. Compute continuous numeric bounds using IntervalArithmetic
    bounds = [child.bound for child in children]
    # Safely apply the operation to the intervals if supported, else default to unbounded
    new_bound = if op in (+, -, *, /)
        op(bounds...)
    else
        IntervalArithmetic.Interval(-Inf, Inf)
    end

    # 2. Structural deduction
    struct_sign = _structural_sign(op, children)

    # 3. Reconcile numeric bounds with structural deduction
    final_sign = _reconcile_sign(new_bound, struct_sign)
    final_divis = _reconcile_divisibility(new_bound, final_sign)

    return ConstraintEvidence(new_bound, final_divis, final_sign)
end

# affine checks
function _update_affine_bound!(bounds, strict_lo, strict_hi, expr, iv, op)
    affine = _affine_coefficients(expr, Symbolics.unwrap(iv))
    affine === nothing && return true
    coeff = SU.unwrap_const(affine[1])
    intercept = SU.unwrap_const(affine[2])
    (coeff isa Real && intercept isa Real) || return true
    val = Float64(-intercept / coeff)
    effective_op = coeff > 0 ? op : _reverse_relation(op)
    old_lo, old_hi = inf(bounds[iv]), sup(bounds[iv])
    if effective_op in ((<), (<=))
        is_strict = effective_op === (<)
        if val < old_hi || (val == old_hi && is_strict)
            strict_hi[iv] = is_strict
        end
        bounds[iv] = intersect_interval(bounds[iv], Interval(-Inf, val))
    elseif effective_op in ((>), (>=))
        is_strict = effective_op === (>)
        if val > old_lo || (val == old_lo && is_strict)
            strict_lo[iv] = is_strict
        end
        bounds[iv] = intersect_interval(bounds[iv], Interval(val, Inf))
    else # effective_op === (==)
        bounds[iv] = intersect_interval(bounds[iv], Interval(val, val))
    end
    isempty(bounds[iv]) && return false
    lo, hi = inf(bounds[iv]), sup(bounds[iv])
    (lo == hi && (strict_lo[iv] || strict_hi[iv])) && return false
    return true
end

# Feasibility probes. The sign of `expr` over a domain is probed with
# non-strict inequalities; the zero set {expr = 0} is {expr <= 0} ∩ {expr >= 0},
# stated as two inequalities because domain constraints are inequalities.
function _sign_probe(expr, which::Symbol)
    which === :nonpositive && return [SymRelation(expr, Symbol("<="))]
    which === :nonnegative && return [SymRelation(expr, Symbol(">="))]
    which === :zero && return [SymRelation(expr, Symbol("<=")), SymRelation(expr, Symbol(">="))]
    throw(ArgumentError("unknown probe $which"))
end

_can_be(expr, domain::SymDomain, which::Symbol) =
    constraints_satisfiable(_sign_probe(expr, which), domain, true)

# Turn the three probe answers into evidence (shared by the affine and paved stages).
function _probe_evidence(factor, domain::SymDomain)
    _can_be(factor, domain, :nonpositive) ||
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, positive)
    _can_be(factor, domain, :nonnegative) ||
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, negative)
    _can_be(factor, domain, :zero) ||
        return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), divisible, either)
    return ConstraintEvidence(IntervalArithmetic.Interval(-Inf, Inf), haszero, undetermined)
end

"""
    _affine_factor_evidence(factor, ctx, sys)

Classify a factor that is affine in one independent variable.
"""
function _affine_factor_evidence(factor, ctx::EvidenceDomain)
    factor_variables = Symbolics.get_variables(Symbolics.unwrap(factor))
    domain_vars = [iv for iv in ctx.source.variables if _contains_equal(factor_variables, iv)]
    length(domain_vars) == 1 || return nothing
    iv = only(domain_vars)

    coefficients = _affine_coefficients(Symbolics.unwrap(factor), Symbolics.unwrap(iv))
    coefficients === nothing && return nothing

    coeff_evidence = _infer_tree(coefficients[1], ctx)
    coeff_evidence.sign in (positive, negative) || return nothing

    block = block_of(ctx.source, iv)
    block === nothing && return nothing
    return _probe_evidence(factor, subdomain(ctx.source, [block]))
end

function _centered_factor_evidence(factor, ctx::EvidenceDomain)
    return nothing # PSEUDOCODE: replace with centered/mean-value forms.
end

function _sturm_factor_evidence(factor, ctx::EvidenceDomain)
    return nothing # PSEUDOCODE: replace with certified Sturm isolation.
end

function _paved_factor_evidence(factor, ctx::EvidenceDomain)
    return _probe_evidence(factor, _ctx_domain!(ctx))
end

# evidence helpers
function _evidence_from_literal(literal::Real)
    if literal > 0
        return ConstraintEvidence(interval(literal, literal), divisible, positive)
    elseif literal < 0
        return ConstraintEvidence(interval(literal, literal), divisible, negative)
    else
        return ConstraintEvidence(interval(literal, literal), haszero, iszero)
    end
end

function _structural_sign(op, children)
    if op === (+)
        all(c -> c.sign === positive, children) && return positive
        all(c -> c.sign === negative, children) && return negative
        all(c -> c.sign === iszero, children) && return iszero
    elseif op === (-) && length(children) == 1
        c = children[1]
        return c.sign === positive ? negative : c.sign === negative ? positive : c.sign === iszero ? iszero : undetermined
    elseif op === (*)
        any(c -> c.sign === iszero, children) && return iszero
        if all(c -> c.sign in (positive, negative), children)
            negatives = count(c -> c.sign === negative, children)
            return isodd(negatives) ? negative : positive
        end
    elseif op === (/) && length(children) == 2
        num, den = children
        num.sign === iszero && den.sign in (positive, negative) && return iszero
        if den.sign in (positive, negative) && num.sign in (positive, negative)
            return num.sign === den.sign ? positive : negative
        end
    end
    return undetermined
end

function _reconcile_sign(bound, struct_sign)
    # Numeric bounds take precedence if they strictly exclude zero
    sup(bound) < 0 && return negative
    inf(bound) > 0 && return positive
    inf(bound) == 0 && sup(bound) == 0 && return iszero

    # Fallback to structural sign if the interval crosses zero (or is NaN/Inf)
    return struct_sign
end

function _reconcile_divisibility(bound, final_sign)
    # Divisible if strictly positive/negative structurally, or if 0 is outside the interval
    if final_sign in (positive, negative) || !(0 ∈ bound)
        return divisible
    elseif final_sign === iszero || (inf(bound) == 0 && sup(bound) == 0)
        return haszero
    end
    return undetermined
end

function _reverse_relation(op)
    op === (<) && return (>)
    op === (<=) && return (>=)
    op === (>) && return (<)
    op === (>=) && return (<=)
end

function _has_depvar_or_diff(expr, sys::DESys)
    any(variable -> _contains_equal(sys.dvs, variable),
        Symbolics.get_variables(Symbolics.unwrap(expr))) && return true
    expression = Symbolics.unwrap(expr)
    SU.iscall(expression) || return false
    Symbolics.operation(expression) isa Differential && return true
    any(argument -> _has_depvar_or_diff(argument, sys),
        SU.arguments(expression))
end

function _can_divide_by(expr::Symbolics.Num, sys::DESys)
    _contains_equal(sys.dvs, expr) && return false
    _has_depvar_or_diff(expr, sys) && return false
    return factor_divisibility(expr, sys) === divisible
end

"""
Return syntactic numerator-factor candidates shared by every addend.
This function deliberately does not decide whether a factor is cancellable. It
only computes a conservative candidate list; `factor_divisibility` remains the
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

common_divisors(expr, sys::DETree) =
    length(sys.active) == 1 ?
    common_divisors(expr, sys.nodes[first(sys.active)].system) :
    throw(ArgumentError("common divisors require one selected branch"))
