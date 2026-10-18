# ===========================================================================
# Equations & Boundary Conditions Operations
# ===========================================================================
SymEquation(eq::Symbolics.Equation, id::EqId=UNASSIGNED_ID) = SymEquation(eq.lhs - eq.rhs, id)
SymEquation(expr::Expr, id::EqId=UNASSIGNED_ID) = SymEquation(wrap(expr), id)

Symbolics.simplify(eq::SymEquation) = SymEquation( simplify(eq.residual), eq.id)
Symbolics.expand(eq::SymEquation) = SymEquation(expand(eq.residual), eq.id)

function boundary_domain(bc::BoundaryCondition, domain::SymDomain)
    loc = bc.locus
    if typeof(loc) in (Limit, ExhaustiveLimit)
        return nothing
    end
    if typeof(loc) == Interior
        return domain
    end
    if typeof(loc) == Explicit
        return add_constraints(domain, _as_constraint(bc.relation))
    end
end

# ===========================================================================
# History & Transform Chain Operations
# ===========================================================================
function append_transform(history::XChain, step::Transform;
    cause::Union{Nothing,Int}=nothing)
    XChain(vcat(history.steps, [XStep(cause, step)]))
end

const append_derivation = append_transform

last_index(history::XChain) = length(history.steps)

# ===========================================================================
# DESys & RootSys Constructors and Helpers
# ===========================================================================
function Base.setproperty!(sys::DESys, name::Symbol, value)
    # Pavings live on the domain's factors, so replacing the domain needs no invalidation.
    name === :domain && (value = _as_domain(value))
    setfield!(sys, name, value)
end

function DESys(eqs, bcs, domain, ivs, dvs; ps=Symbolics.Num[],
    restrictions=SymRelation[], kwargs...)
    normalized_ivs = Symbolics.Num[ivs...]
    normalized_dvs = Symbolics.Num[dvs...]
    normalized_ps = Symbolics.Num[ps...]
    normalized_eqs = Symbolics.Equation[eqs...]
    normalized_bcs = Symbolics.Equation[bcs...]
    normalized_domain = _as_domain(domain) # SymDomain, `key => constraints` pairs, or bare constraints
    normalized_restrictions = SymRelation[restrictions...]
    DESys(normalized_ivs, normalized_dvs, normalized_ps,
        normalized_eqs, normalized_bcs, normalized_domain,
        normalized_restrictions)
end

function DESys(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system,
    restrictions=SymRelation[], history=XChain(), kwargs...)
    DESys(eqs, bcs, domain, ivs, dvs; ps=ps,
        restrictions=restrictions)
end

# needs to be redone to trace the history up the tree
_with_history(b::DESys, h::XChain) = DESys(
    eqs=b.eqs, ivs=b.ivs, dvs=b.dvs, ps=b.ps, bcs=b.bcs, domain=b.domain,
    restrictions=b.restrictions)

is_in_domain(coord::StaticArrays.SVector, sys::DESys, include_boundary::Bool=true) =
    is_in_domain(coord, sys.domain, include_boundary)

function RootSys(sys::DESys)
    ivs = tuple(sys.ivs...)
    dvs = tuple(sys.dvs...)
    ps = tuple(sys.ps...)
    eqs = tuple(sys.eqs...)
    bcs = tuple(sys.bcs...)
    RootSys(ivs, dvs, ps, eqs, bcs, sys.domain)
end

# Replace a branch's state without replacing the branch object stored by its
# parent system. This also preserves branch-local metadata not involved in
# the transformation.
function _replace_branch!(
    branch::DESys;
    eqs=branch.eqs, ivs=branch.ivs, dvs=branch.dvs, ps=branch.ps, bcs=branch.bcs,
    domain=branch.domain, restrictions=branch.restrictions, kwargs...
)
    # Constructors used to perform this conversion implicitly. Keep it here
    # because transformed intermediate collections may have eltype `Any`.
    branch.eqs = typeof(branch.eqs)(eqs)
    branch.ivs = typeof(branch.ivs)(ivs)
    branch.dvs = typeof(branch.dvs)(dvs)
    branch.ps = typeof(branch.ps)(ps)
    branch.bcs = typeof(branch.bcs)(bcs)
    branch.domain = domain
    branch.restrictions = SymRelation[restrictions...]
    return branch
end
