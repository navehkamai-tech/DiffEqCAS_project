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
    @rule(~n::is_float => rationalize(~n)),
    @rule(inv(~n::is_rational) => simplify(1//(~n)))
]

const NORMALIZER = SU.Postwalk(SU.PassThrough(SU.Chain(normalization_rules)))

function normalize_expr(expr::Symbolics.Num)
    return wrap(simplify(NORMALIZER(unwrap(expr))))
end

function normalize_expr(expr::Expr)
    return simplify(NORMALIZER(expr))
end

test = 0

function SymRelation(residual, relation; limits=ExpansionLimits())
    rel = _relation_symbol(relation)
    res = _as_num(normalize_expr(residual))
    res = _as_num(_expand_residual(res, limits))
    res = Symbolics.simplify(res)
    type = _classify_residual(res, rel)
    type in (:d, :i, :p) && ((res, rel) = _canonicalize(res, rel))
    key = hash(Symbolics.unwrap(res), hash(rel))
    return SymRelation(res, rel, type, key)
end

# `x > 1`  ->  SymRelation(x - 1, _GT)
function SymRelation(expr::Symbolics.Num)
    unwrapped = Symbolics.unwrap(expr)
    SU.iscall(unwrapped) ||
        throw(ArgumentError("must be an expression"))
    op = _relation_symbol(SU.operation(unwrapped); error_message="a SymRelation must be a relation such as `x > 0`, got")
    lhs, rhs = SU.arguments(unwrapped)
    return SymRelation(wrap(lhs) - wrap(rhs), op)
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

Abstraction() = Abstraction(Region[], Dict{Any,Int}(), Dict{Any,Int}())

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
# Expansion budget (mutable state for one bounded-expansion run)
#--------------------------------------------------------------------------

"""
    ExpansionBudget(limits=ExpansionLimits())
 
Mutable companion to the immutable `ExpansionLimits`. One budget is
shared by everything expanded in a run, so growth in one region is charged
against all the others. 
 
- `headroom`: remaining DAG-node allowance. Re-derived at the start of every
  `bounded_expand` call from `limits.max_nodes`, so it never drifts.
- `stable`: dummy-free expressions already known to be at a fixpoint.
"""
mutable struct ExpansionBudget
    limits::ExpansionLimits
    headroom::Int
    stable::Set{Any}
end

ExpansionBudget(limits::ExpansionLimits=ExpansionLimits()) =
    ExpansionBudget(limits, limits.max_nodes, Set{Any}())

#--------------------------------------------------------------------------
# Per-region improvement
#--------------------------------------------------------------------------

# Simplify (and conditionally expand) one expression under the shared ledger.
function _improve(expr, budget::ExpansionBudget)
    base = _size(expr)
    cur = expr
    seen = Set{Any}([cur])
    converged = false

    for _ in 1:budget.limits.max_passes
        nxt = simplify(cur)

        if _expansion_cost(nxt, budget.headroom + base) < Inf
            ex = simplify(expand(nxt))
            _size(ex) - base <= budget.headroom && (nxt = ex)
        end

        if nxt in seen      # fixpoint, or oscillation (both mean stop)
            converged = true
            break
        end
        push!(seen, nxt)
        cur = nxt
    end

    budget.headroom -= _size(cur) - base    # growth is charged, shrinkage refunded
    return cur, converged
end

# Simplify every dirty region, then record which results are trustworthy.
function _simplify_regions!(ab::Abstraction, budget::ExpansionBudget)
    sub = _restore_all(ab)
    dirty = Region[]
    for r in ab.regions
        if sub[r.dummy] in budget.stable
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
        r.expr, conv = _improve(r.expr, budget)
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
            push!(budget.stable, sub[r.dummy])
        end
    end
    return sub
end

#--------------------------------------------------------------------------
# Bounded expansion: public entry points
#--------------------------------------------------------------------------

"""
    bounded_expand(exprs, budget) -> Vector
 
Simplify and (where affordable) expand a batch of unwrapped expressions under
`budget`. The batch is abstracted jointly, so non-algebraic subexpressions that
occur in several expressions are improved once and shared. Leaves (a lone symbol
or number) map to themselves.
"""
function bounded_expand(exprs::AbstractVector, budget::ExpansionBudget)
    ab = Abstraction()
    roots = [_abstract_root!(e, ab) for e in exprs]
    # Re-derive the ledger from the actual state every call (no drift).
    budget.headroom = budget.limits.max_nodes - sum(r -> _size(r.expr), ab.regions; init=0)
    isempty(ab.regions) && return Any[roots...]
    sub = _simplify_regions!(ab, budget)
    return Any[get(sub, root, root) for root in roots]
end

bounded_expand(expr, budget::ExpansionBudget) = only(bounded_expand([expr], budget))

"""
    expand_derivatives_bounded(expr, limits) -> expr
 
`expand_derivatives` with a size guard: if the expanded form reaches
`limits.max_derivative_nodes`, the original expression is returned unchanged.
Takes and returns an unwrapped expression.
"""
function expand_derivatives_bounded(expr, limits::ExpansionLimits)
    cand = Symbolics.unwrap(expand_derivatives(Symbolics.wrap(expr), simplify=true))
    return _size(cand) >= limits.max_derivative_nodes ? expr : cand
end

function _is_algebraic(expr)
    SU.iscall(expr) || return true
    op = SU.operation(expr)
    op in ALGEBRAIC_OPS || return false
    return all(_is_algebraic, SU.arguments(expr))
end

# True if some transcendental (non-algebraic function) has a non-leaf argument,
# e.g. exp(x + y) or sin(x*y), but not exp(x) or x(t).
function _needs_safe_expand(expr)
    SU.iscall(expr) || return false
    _is_transparent_diff(expr) && return false
    op = SU.operation(expr)
    args = SU.arguments(expr)
    if op isa Function && !(op isa SU.Differential) && !(op in ALGEBRAIC_OPS)
        all(_atomic, args) || return true
    end
    return any(_needs_safe_expand, args)
end

"""
    _expand_residual(expr, limits_or_budget=ExpansionLimits())
 
Expand one residual. Plain algebraic expressions use `Symbolics.expand`
directly; anything with a transcendental of a compound argument goes through
`bounded_expand`. Given `ExpansionLimits`, a fresh budget is made per call so
one residual's growth is never charged to another; pass an `ExpansionBudget`
to share one deliberately.
"""
function _expand_residual(expr::Symbolics.Num, budget::ExpansionBudget)
    u = Symbolics.unwrap(expr)
    (_is_algebraic(u) || !_needs_safe_expand(u)) && return Symbolics.expand(expr)
    return Symbolics.wrap(bounded_expand(u, budget))
end

_expand_residual(expr::Symbolics.Num, limits::ExpansionLimits=ExpansionLimits()) =
    _expand_residual(expr, ExpansionBudget(limits))

#--------------------------------------------------------------------------
# Coefficient grouping by derivative depth
#--------------------------------------------------------------------------
function _is_target(e, unwrapped_dvs::Set, dv_ops)
    # If it is a leaf node, check if it matches any dependent variable directly
    if !SU.iscall(e)
        return e in unwrapped_dvs
    end

    op = SU.operation(e)

    # Check if the operation matches any of our base dependent operations
    if any(isequal(op, d_op) for d_op in dv_ops)
        return true
    end

    # Support mixed derivatives by recursively checking arguments
    if op isa Differential
        args = SU.arguments(e)
        return _is_target(args[1], unwrapped_dvs, dv_ops)
    end

    return false
end

function _find_targets!(e, unwrapped_dvs::Set, dv_ops, targets::Set)
    # If we found a target, add it and stop recursing
    if _is_target(e, unwrapped_dvs, dv_ops)
        push!(targets, e)
        return
    end

    # Otherwise, keep digging through the expression tree
    if SU.iscall(e)
        for arg in SU.arguments(e)
            _find_targets!(arg, unwrapped_dvs, dv_ops, targets)
        end
    end
end

function _diff_depth(e)
    if !SU.iscall(e)
        return 0
    end
    # Increment depth for each Differential operation
    if SU.operation(e) isa Differential
        return 1 + _diff_depth(SU.arguments(e)[1])
    end
    return 0
end

function group_coefficients(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))
    unwrapped_dvs = Set([unwrap(d) for d in dvs])
    dv_ops = [SU.operation(unwrap(d)) for d in dvs]

    targets = Set()
    # Pass the required state into the mutator function
    _find_targets!(expr, unwrapped_dvs, dv_ops, targets)

    # Sort targets safely using the external helper
    sorted_targets = sort(collect(targets), by=_diff_depth, rev=true)

    grouped_expr = 0
    remainder = expr
    for target in sorted_targets
        max_deg = Symbolics.degree(remainder)
        for p in max_deg:-1:1
            target_term = p == 1 ? target : target^p
            coeff = simplify(Symbolics.coeff(remainder, target_term))
            if !isequal(coeff, 0)
                grouped_expr += coeff * wrap(target_term)
                remainder = simplify(remainder - coeff * target_term)
            end
        end
    end
    grouped_expr += simplify(remainder)
    return grouped_expr ~ 0
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

function _expr_to_poly(expr::Symbolics.Num)
    u=unwrap(expr)
    #=plan: first traversal to classify all atoms that need to be mapped to polynomial variables.
    then, after constructing the polynomial ring, a second traversal to replace those atoms with the polynomial variables.
    finally, return the polynomial and the mapping from polynomial variables to original atoms.
    =#
    atom_map = Dict{Any,Any}()
    # first traversal to classify atoms
    classify_atoms(u, atom_map)
    R, vars = Nemo.PolyRing(Nemo.QQ, ["x$i" for i in 1:length(atom_map)])
    # second traversal to replace atoms with polynomial variables
    poly_expr = _poly_replace(u, atom_map, vars)
    return R(poly_expr), atom_map
end

function classify_atoms(expr::Symbolics.Num, atom_map::Dict{Any,Any})
    if _atomic(expr)
        # If it's a leaf node (like a variable or constant), add it to the map
        atom_map[expr] = nothing  # Placeholder for now
        return
    end

    # Recursively classify arguments
    for arg in SU.arguments(expr)
        classify_atoms(arg, atom_map)
    end
end

function _poly_replace(expr::Symbolics.Num, atom_map::Dict{Any,Any}, vars)
    if haskey(atom_map, expr)
        # Replace the atom with the corresponding polynomial variable
        idx = findfirst(isequal(expr), keys(atom_map))
        return vars[idx]
    end

    # Recursively replace arguments
    new_args = [_poly_replace(arg, atom_map, vars) for arg in SU.arguments(expr)]
    return maketerm(typeof(expr), SU.operation(expr), new_args, SU.metadata(expr))
end
