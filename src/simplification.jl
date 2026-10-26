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

#--------------------------------------------------------------------------
# Context & diagnostics
#--------------------------------------------------------------------------
struct Warning
    eq_index::Int
    symbol::Symbol
    message::String
end

"""
Per-run state of the simplifier. Expansion bookkeeping (growth ledger, cache of
expressions already at a fixpoint) lives in `budget`, which is what gets handed
to algebra.jl; everything else here is simplifier-only.
"""
mutable struct SimplifyContext
    opts::SimplificationOptions
    budget::ExpansionBudget
    warnings::Vector{Warning}
end

SimplifyContext(opts::SimplificationOptions) =
    SimplifyContext(opts, ExpansionBudget(opts.expansion), Warning[])

function classify_residuals!(residuals, ctx::SimplifyContext)
    for (i, res) in enumerate(residuals)
        v = SU.unwrap_const(unwrap(res))
        v isa Number || continue
        class = iszero(v) ? :identity : :contradiction
        push!(ctx.warnings, Warning(i, class, "residual $i simplified to a $class"))
    end
end

#--------------------------------------------------------------------------
# Phases (each: Vector of unwrapped residuals -> Vector of unwrapped residuals)
#--------------------------------------------------------------------------

function _attempt_expand_derivatives(expr, ctx::SimplifyContext)
    ctx.opts.expand_derivatives || return expr
    return expand_derivatives_bounded(expr, ctx.opts.expansion)
end

function _algebraic_pass(res, ctx::SimplifyContext)
    ctx.opts.expand_products || return res
    return bounded_expand(res, ctx.budget)
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
        ctx.budget.headroom <= 0 && break
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

