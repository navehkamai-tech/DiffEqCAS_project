"""
Build a system from transformed residual expressions while preserving all
system metadata. Boundary conditions are normalized by the same expression
normalizer but are never subjected to equation splitting in this pass.
"""
function _with_simplified_expressions(sys::DESys, eqs, bcs, restrictions)
    DESys(
        eqs=eqs,
        ivs=sys.ivs,
        dvs=sys.dvs,
        ps=sys.ps,
        bcs=bcs,
        domain=sys.domain,
        restrictions=restrictions,
    )
end

_simplification_expression(eq::Symbolics.Equation) = eq.lhs - eq.rhs
_simplification_expression(eq::SymEquation) = eq.residual
_simplification_expression(expr) = expr
_normalize_restriction(r::SymRelation) = SymRelation(normalize_expr(r.residual), r.relation)

"""
Cancel only domain-certified common factors.
Candidate discovery and semantic cancellation are deliberately separate:
`common_divisors` proposes factors, while `factor_divisibility` decides whether
each factor is nonzero throughout the current system domain.
"""
function _cancel_certified_residual(residual, sys::DESys)
    current = wrap(residual)
    cancelled = Any[]
    for candidate in common_divisors(current, sys)
        candidate_num = wrap(candidate)
        _can_divide_by(candidate_num, sys) || continue
        next = simplify(current / candidate_num)
        isequal(unwrap(next), unwrap(current)) && continue
        current = next
        push!(cancelled, candidate)
    end
    current, cancelled
end

function _cancel_system(sys::DESys)
    eqs = Symbolics.Equation[]
    details = Any[]
    for eq in sys.eqs
        residual, cancelled = _cancel_certified_residual(
            _simplification_expression(eq), sys)
        push!(eqs, simplify(residual) ~ 0)
        push!(details, cancelled)
    end
    restrictions = [_normalize_restriction(restriction)
                    for restriction in sys.restrictions]
    _with_simplified_expressions(sys, eqs, sys.bcs, restrictions), details
end

"""
Run the factorization hook.
"""
function _factorization_stage(sys::DESys)
    sys, :not_implemented
end

function _factorization_atoms(residual, sys::DESys)
    nothing
end

function _factorization_partition(sys::DESys, factors)
    DESys[]
end

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

struct Warning
    eq_index::Int
    symbol::Symbol
    message::String
end

mutable struct SimplifyContext
    opts::Any                  # simplification options
    stable::Set{Any}           # DUMMY-FREE exprs known to be at a fixpoint
    headroom::Int              # remaining DAG-node allowance
    warnings::Vector{Warning}
end

SimplifyContext(opts) = SimplifyContext(opts, Set{Any}(), 0, Warning[])

#--------------------------------------------------------------------------
# Abstraction (expression -> skeleton with dummies)
#--------------------------------------------------------------------------

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

#--------------------------------------------------------------------------
# Phases (each: Vector of unwrapped residuals -> Vector of unwrapped residuals)
#--------------------------------------------------------------------------

function _attempt_expand_derivatives(expr, ctx::SimplifyContext)
    ctx.opts.expand_derivatives == true || return expr
    cand = Symbolics.unwrap(expand_derivatives(Symbolics.wrap(expr), simplify=true))
    return _size(cand) >= ctx.opts.max_derivative_nodes ? expr : cand
end

function _algebraic_pass(res, ctx::SimplifyContext)
    ctx.opts.expand_products == true || return res
    ab = Abstraction()
    roots = [_abstract_root!(r, ab) for r in res]
    # Re-derive the ledger from the actual state every pass (no drift).
    ctx.headroom = ctx.opts.max_nodes - sum(r -> _size(r.expr), ab.regions; init=0)
    sub = _simplify_regions!(ab, ctx)
    return [get(sub, root, root) for root in roots]   # leaves map to themselves
end

function _nonalgebraic_pass(res, ctx::SimplifyContext)
    return res
end

function rebuild_branch(sys::DESys, eqs, warnings, bcs, restrictions)
    restrictions = [_normalize_restriction(restriction) for restriction in sys.restrictions]
    return _with_simplified_expressions(sys, [e ~ 0 for e in eqs], sys.bcs, restrictions), warnings
end

#--------------------------------------------------------------------------
# Top level
#--------------------------------------------------------------------------

function _simplify_branch_eqs(sys::DESys, options::SimplificationOptions=SimplificationOptions())
    ctx = SimplifyContext(options)

    # Unwrap once here, wrap once in rebuild_branch.
    res = [unwrap(_simplification_expression(eq)) for eq in sys.eqs]
    res = normalize_expr.(res)
    res = [_attempt_expand_derivatives(r, ctx) for r in res]

    # Outer fixpoint: phases feed each other until nothing changes.
    seen = Set{Any}([res])
    for _ in 1:options.max_rounds
        new = _algebraic_pass(res, ctx)
        new = _nonalgebraic_pass(new, ctx)
        new = [_attempt_expand_derivatives(r, ctx) for r in new]
        res = new
        new in seen && break
        push!(seen, new)
        ctx.headroom <= 0 && break
    end

    classify_residuals!(res, ctx)
    return rebuild_branch(sys, wrap.(res), ctx.warnings, sys.bcs, sys.restrictions)
end

"""
    simplify_system(sys; options...)

Simplify every active branch in a system through the staged pipeline.
"""
function simplify_system(sys::DETree;
    options::SimplificationOptions=SimplificationOptions())
    for id in sys.active
        node = sys.nodes[id]
        if node isa ActiveNode
            simplified_sys, _ = _simplify_branch_eqs(node.system, options)
            node.system = simplified_sys
        end
    end
    return sys
end

# ===========================================================================
# 1. Coefficient Grouping by Derivative Depth
# ===========================================================================
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
                grouped_expr += coeff * wrap(target)
                remainder = simplify(remainder - coeff * target_term)
            end
        end
    end
    grouped_expr += simplify(remainder)
    return grouped_expr ~ 0
end
