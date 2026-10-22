# ===========================================================================
# Relations
# ===========================================================================

# I want this to check if parameters can be divided by, and it should seek to have the leading variable coefficient be 1
function _canonicalize_relation(residual, rel_sym::Symbol)
    expr = Symbolics.unwrap(simplify(expand(wrap(residual))))
    val = SU.unwrap_const(expr)
    val isa Real && return (wrap(sign(val)), rel_sym)

    vars = Symbolics.get_variables(expr)
    isempty(vars) && return (wrap(expr), rel_sym)

    # Prefer true independent variables over parameters/constants, sorted alphabetically
    ivs = filter(v -> !ModelingToolkit.isparameter(Symbolics.unwrap(v)) &&
        !ModelingToolkit.isconstant(Symbolics.unwrap(v)), vars)
    target_vars = isempty(ivs) ? vars : ivs
    sort!(target_vars, by=string)
    lead_var = Symbolics.unwrap(first(target_vars))

    # Extract coefficient of highest power of `lead_var`
    deg = Symbolics.degree(expr, lead_var)
    lead_term = deg > 0 ? Symbolics.coeff(expr, deg == 1 ? lead_var : lead_var^deg) : expr
    c = _numeric_factor(lead_term)

    if c isa Real && !iszero(c)
        # Normalize magnitude and force leading numeric coefficient to be positive
        expr = simplify(expand(wrap(expr) / abs(c)))
        if c < 0
            expr = simplify(expand(-expr))
            rel_sym = _flip_relation_symbol(rel_sym)
        end
    else
        expr = wrap(expr)
    end
    return (expr, rel_sym)
end

function SymRelation(residual, relation)
    res, rel_sym = _canonicalize_relation(residual, _relation_symbol(relation))
    return _unchecked_relation(res, rel_sym)
end

# `x > 1`  ->  SymRelation(x - 1, :>)
function SymRelation(expr::Symbolics.Num)
    unwrapped = Symbolics.unwrap(expr)
    SU.iscall(unwrapped) ||
        throw(ArgumentError("must be an expression"))
    op = _relation_symbol(SU.operation(unwrapped), "a SymRelation must be a relation such as `x > 0`, got")
    lhs, rhs = SU.arguments(unwrapped)
    return SymRelation(wrap(lhs) - wrap(rhs), op)
end

# ===========================================================================
# Equations & Boundary Conditions Operations
# ===========================================================================
SymEquation(eq::Symbolics.Equation, id::EqId=fresh_id()) = SymEquation(eq.lhs - eq.rhs, id)
SymEquation(expr::Expr, id::EqId=fresh_id()) = SymEquation(wrap(expr), id)

Symbolics.simplify(eq::SymEquation) = SymEquation(simplify(eq.residual), eq.id)
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
# needs to be updated to handle the history of transformations, so should probably take in an ActiveNode and return an ActiveNode with the updated history
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
