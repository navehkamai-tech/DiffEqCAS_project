# this file should deal with expression normalization, satisfiability agnostic simplification, and factorization

const normalization_rules = [
    # 1. Radical Normalization Rules
    @rule(sqrt(~x) => (~x)^(1//2)),
    @rule(cbrt(~x) => (~x)^(1//3)),
    @rule(fourthroot(~x) => (~x)^(1//4)),
    @rule(sin(~x+2*Constants.π
    ) => sin(~x)),
    @rule(sin(~x+Constants.π
        * ~n::is_even) => sin(~x)),
    @rule(cos(~x+2*Constants.π
    ) => cos(~x)),
    @rule(cos(~x+2 * Constants.π
        * ~n::is_even) => cos(~x)),
    # Hyperbolic Trig Normalization
    # 3. Exact Rational Normalization
    @rule(~n::AbstractFloat => rationalize(~n)),
    @rule(inv(~n::is_rational) => simplify(1//(~n)))
]

const NORMALIZER = SU.Postwalk(SU.PassThrough(SU.Chain(normalization_rules)))

function normalize_expr(expr::Symbolics.Num)
    return wrap(simplify(NORMALIZER(unwrap(expr))))
end

function normalize_expr(expr::Expr)
    return simplify(NORMALIZER(expr))
end

"""
    _connected_groups(constraints; key=_ckey)

Split constraints into connected groups: two constraints are in the same group
when they share a variable, directly or through other constraints. Constraints
with no variables each form their own group.

Duplicates (same `key`) are dropped. Within a group, constraints are ordered by
their key, and the groups themselves are ordered by their smallest key, so the
result is deterministic and independent of the input order.

Returns a vector of `(constraints, variables, keys)` named tuples, where
`variables` is the group's unique variables in order of first appearance and
`keys` are the constraint keys in the same order as `constraints`.
"""
function _connected_groups(constraints; key=_ckey)
    seen = Set{UInt64}()
    cs = Constraint[]
    ks = UInt64[]
    for c in constraints
        k = key(c)
        k in seen && continue
        push!(seen, k)
        push!(cs, c)
        push!(ks, k)
    end

    n = length(cs)
    parent = collect(1:n)
    function find(i)
        while parent[i] != i
            parent[i] = parent[parent[i]]
            i = parent[i]
        end
        return i
    end

    cvars = [_vars_of(c.relation.residual) for c in cs]
    owner = Dict{Symbolics.Num,Int}()
    for i in 1:n, v in cvars[i]
        j = get!(owner, v, i)
        j == i || (parent[find(i)] = find(j))
    end

    groups = Dict{Int,Vector{Int}}()
    for i in 1:n
        push!(get!(groups, find(i), Int[]), i)
    end

    result = NamedTuple{(:constraints, :variables, :keys),
        Tuple{Vector{Constraint},Vector{Symbolics.Num},Vector{UInt64}}}[]
    for idxs in values(groups)
        sort!(idxs, by=i -> ks[i])
        vars = Symbolics.Num[]
        varset = Set{Symbolics.Num}()
        for i in idxs, v in cvars[i]
            v in varset || (push!(varset, v); push!(vars, v))
        end
        push!(result, (constraints=cs[idxs], variables=vars, keys=ks[idxs]))
    end
    sort!(result, by=g -> first(g.keys))
    return result
end

#--------------------------------------------------------------------------
# Abstraction (expression -> skeleton with dummies)
#--------------------------------------------------------------------------

mutable struct Region
    dummy::Any
    expr::Any       # unwrapped; may contain dummies of regions created earlier
    count::Int      # number of direct uses
    state::Symbol   # :stable (skipped), :converged, :capped
end

mutable struct Abstraction
    regions::Vector{Region}          # creation order == dependency order
    index::Dict{Any,Int}             # abstracted expr -> position in regions
    by_dummy::Dict{Any,Int}          # dummy -> position in regions
end

struct Warning
    eq_index::Int
    symbol::Symbol
    message::String
end

Abstraction() = Abstraction(Region[], Dict{Any,Int}(), Dict{Any,Int}())

# D of a variable, of x(t), or of nested D of those, behaves like a leaf.
function _is_atomic(a)
    SU.iscall(a) || return true
    op = SU.operation(a)
    op isa SU.Symbolic && return true     # unknown function x(t)
    op isa SU.Differential &&
        return _is_atomic(SU.arguments(a)[1])
    return false
end

function _is_transparent_diff(expr)
    op = SU.operation(expr)
    return op isa SU.Differential &&
        _is_atomic(SU.arguments(expr)[1])
end

# Look up or create the region for `new_expr`; returns its dummy.
function _intern!(ab::Abstraction, new_expr)
    i = get!(ab.index, new_expr) do
        n = length(ab.regions) + 1
        d = SU.Sym{Real}(Symbol("_D_", n))  # can't collide with user names
        push!(ab.regions, Region(d, new_expr, 0, :converged))
        ab.by_dummy[d] = n
        n
    end
    ab.regions[i].count += 1
    return ab.regions[i].dummy
end

const ALGEBRAIC_OPS = Set([+, *, ^])

function _abstract(expr, ab::Abstraction, parent_alg::Bool)
    SU.iscall(expr) || return expr
    _is_transparent_diff(expr) && return expr
    op = SU.operation(expr)
    is_alg = op in ALGEBRAIC_OPS
    new_args = [_abstract(a, ab, is_alg) for a in SU.arguments(expr)]
    new_expr = maketerm(typeof(expr), op, new_args, SU.metadata(expr))
    # A non-algebraic node under an algebraic parent becomes a region.
    return (!is_alg && parent_alg) ? _intern!(ab, new_expr) : new_expr
end

# A root is abstracted, then interned itself, so it becomes the last region
# for that residual. Bare leaves (a lone symbol or number) need no region.
function _abstract_root!(expr, ab::Abstraction)
    skeleton = _abstract(expr, ab, false)
    return SU.iscall(skeleton) ? _intern!(ab, skeleton) : skeleton
end

# Resolve in creation order; each region only needs already-resolved dummies.
function _restore_all(ab::Abstraction)
    sub = Dict{Any,Any}()
    for r in ab.regions
        sub[r.dummy] = Symbolics.substitute(r.expr, sub)
    end
    return sub
end

# Dummies directly referenced by an expression (for dependency tracking).
function _dummies_in(expr, ab::Abstraction, acc=Set{Int}())
    if SU.iscall(expr)
        foreach(a -> _dummies_in(a, ab, acc), SU.arguments(expr))
    elseif haskey(ab.by_dummy, expr)
        push!(acc, ab.by_dummy[expr])
    end
    return acc
end

#--------------------------------------------------------------------------
# Cost / size helpers
#--------------------------------------------------------------------------

# Region bodies contain dummies as leaves, so this is automatically a DAG
# measure when summed over regions. Delegates to your existing counter.
_size(expr) = robust_node_count(expr)

# Estimated term count after full expansion, with early exit.
# Returns Inf as soon as the estimate exceeds `cap`, so it never overflows
# and never does the expensive arithmetic for hopeless cases.
function _expansion_cost(expr, cap::Real)
    SU.iscall(expr) || return 1.0
    op = SU.operation(expr)
    args = SU.arguments(expr)
    _is_transparent_diff(expr) && return 1.0
    isempty(args) && return 1.0

    c = if op === +
        sum(a -> _expansion_cost(a, cap), args)
    elseif op === *
        prod(a -> _expansion_cost(a, cap), args)
    elseif op === ^
        base_cost = _expansion_cost(args[1], cap)
        n = SU.unwrap_const(Symbolics.unwrap(args[2]))
        if n isa Real && isinteger(n) && n > 1 && base_cost > 1
            # C(base_cost + n - 1, n) as a running product with early exit
            r = 1.0
            for k in 1:Int(n)
                r *= (base_cost - 1 + k) / k
                r > cap && return Inf
            end
            r
        else
            base_cost
        end
    else
        max(1.0, sum(a -> _expansion_cost(a, cap), args))
    end
    return c > cap ? Inf : c
end

#--------------------------------------------------------------------------
# Per-region improvement
#--------------------------------------------------------------------------

# Simplify (and conditionally expand) one expression under the shared ledger.
function _improve(expr, ctx::SimplifyContext)
    base = _size(expr)
    cur = expr
    seen = Set{Any}([cur])
    converged = false

    for _ in 1:ctx.opts.max_stabilizer_passes
        nxt = simplify(cur)

        if _expansion_cost(nxt, ctx.headroom + base) < Inf
            ex = simplify(expand(nxt))
            _size(ex) - base <= ctx.headroom && (nxt = ex)
        end

        if nxt in seen      # fixpoint, or oscillation (both mean stop)
            converged = true
            break
        end
        push!(seen, nxt)
        cur = nxt
    end

    ctx.headroom -= _size(cur) - base    # growth is charged, shrinkage refunded
    return cur, converged
end

# Simplify every dirty region, then record which results are trustworthy.
function _simplify_regions!(ab::Abstraction, ctx::SimplifyContext)
    sub = _restore_all(ab)
    dirty = Region[]
    for r in ab.regions
        if sub[r.dummy] in ctx.stable
            r.state = :stable
        else
            push!(dirty, r)
        end
    end

    # High count first (gains are multiplied), cheaper first among ties.
    sort!(dirty, by=r -> (-r.count, _size(r.expr)))

    changed = Set{Int}()
    for r in dirty
        old = r.expr
        r.expr, conv = _improve(r.expr, ctx)
        r.state = conv ? :converged : :capped
        isequal(old, r.expr) || push!(changed, ab.by_dummy[r.dummy])
    end

    sub = _restore_all(ab)
    tainted = Set{Int}()
    for (i, r) in enumerate(ab.regions)
        deps = _dummies_in(r.expr, ab)
        if i in changed || any(d -> d in tainted, deps)
            push!(tainted, i)
        end
        if r.state === :converged && !any(d -> d in tainted, deps)
            push!(ctx.stable, sub[r.dummy])
        end
    end
    return sub
end

function classify_residuals!(residuals, ctx::SimplifyContext)
    for (i, res) in enumerate(residuals)
        v = SU.unwrap_const(unwrap(res))
        local class
        if v isa Number
            iszero(v) ? class = :identity : class = :contradiction
        else
            class = :normal
        end
        (class === :contradiction || class === :identity) && push!(ctx.warnings, Warning(i, class, "residual $i simplified to a$(class)"))
    end
end

function _is_algebraic(expr)
    SU.iscall(expr) || return true
    op = SU.operation(expr)
    op in ALGEBRAIC_OPS || return false
    return all(_is_algebraic, SU.arguments(expr))
end

#=
the plan:
factorize expressions. translate expressions into polynomial atoms that can be used for
factoring with Nemo.jl. Then, translate the factors back into Symbolics expressions.
might want separate functions for expressions with just independent variables, parameters, & constants,
and for expressions with dependent variables (like x(t), y(t), etc.) and their derivatives. 
the former is what's needed for combating the dependency problem in satisfiability.jl and paving.jl,
while the latter will be needed in simplification.jl for simplifying differential equations.
=#