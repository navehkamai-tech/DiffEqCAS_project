# ===========================================================================
# 1. Identifiers
# ===========================================================================
"""
Stable identity of a node, domain constraint, or equation.
Drawn from the same per-tree counter as every other Id (see `next_id!`), so it is
unique across the whole tree, is inherited unchanged by child nodes, and survives
rewrites of the constraint's expression (change of variables, simplification).
Boundary conditions refer to a constraint by this Id, never by its position.
`UNASSIGNED_ID` marks an item that has not been registered with a tree yet; see `assign_ids`.
"""
const NodeId = Int
const ConstraintId = Int
const EqId = Int
const UNASSIGNED_ID = 0

# ===========================================================================
# 2. Symbolic Relations & Equations
# ===========================================================================
"""
    SymRelation(residual, relation)

A branch-local relation between a symbolic residual and zero. Equalities are
represented by the branch equations; restrictions represent only non-equality
relations used to describe a branch cell.
"""
struct SymRelation
    residual::Symbolics.Num
    relation::Symbol

    function SymRelation(residual, relation)
        relation_symbol = relation isa Symbol ? relation : Symbol(string(relation))
        relation_symbol in (Symbol("!="), :>, Symbol(">="), :<, Symbol("<="), Symbol("==")) ||
            throw(ArgumentError("unsupported symbolic restriction relation: $relation"))
        new(wrap(residual), relation_symbol)
    end
end

const _restriction_relations = (Symbol("!="), :>, Symbol(">="), :<, Symbol("<="), Symbol("=="))

struct SymEquation
    id::EqId
    residual::Symbolics.Num
    function SymEquation(residual::Symbolics.Num, id::EqId=UNASSIGNED_ID)
        new(id, residual)
    end
end

# ===========================================================================
# 3. Domain Types
# ===========================================================================
"""
    DomConstraint(id, relation)

A `SymRelation` (`residual ⋈ 0`) together with its identity. The Id is
bookkeeping, not part of the constraint's meaning: two constraints with equal
`relation` describe the same set no matter what their Ids are.
"""
struct DomConstraint
    id::ConstraintId
    relation::SymRelation
end

constraint_variables(c::DomConstraint) =
    Symbolics.get_variables(Symbolics.unwrap(c.relation.residual))

# Canonical order inside a factor: by content, never by Id, so a domain does
# not depend on the order its constraints were supplied in. The Id is only a
# final tie-break between constraints with identical content.
_content_key(c::DomConstraint) = (string(c.relation.residual), String(c.relation.relation))
_constraint_sort_key(c::DomConstraint) = (_content_key(c)..., c.id)

# Binary search in a vector/tuple of constraints sorted by Id; 0 if absent.
function _constraint_index(constraints, id::ConstraintId)
    lo, hi = 1, length(constraints)
    while lo <= hi
        mid = (lo + hi) >>> 1
        mid_id = constraints[mid].id
        mid_id == id && return mid
        mid_id < id ? (lo = mid + 1) : (hi = mid - 1)
    end
    return 0
end

"""
    Paving(interior, boundary, roi, tolerance)

Branch-and-prune result for one domain factor: boxes certainly inside, and
boxes too small to classify (the boundary). `roi` and `tolerance` record the
global settings it was computed with, so a paving made under other settings is
recomputed rather than reused. Deliberately not parametrized: an empty paving
has no box type to infer from.
"""
struct Paving
    interior::Vector{<:IntervalBoxes.IntervalBox}
    boundary::Vector{<:IntervalBoxes.IntervalBox}
    roi::Float64
    tolerance::Float64
end

"""
    DomBlock(variables, constraint_ids)

One factor (i.e. 'Block') of a domain: a set of variables together with the
constraints that couple them. The domain is the Cartesian product of its factors.
A factor stores only the *Ids* of its constraints; the constraint data lives once,
in `SymDomain.constraints`.
"""
mutable struct DomBlock
    const variables::Tuple{Vararg{Symbolics.Num}}      # canonical order (by string)
    const constraint_ids::Tuple{Vararg{ConstraintId}}  # canonical order (by content)
    paving::Union{Nothing,Paving}
end

DomBlock(variables, constraint_ids) = DomBlock(variables, constraint_ids, nothing)

"""
    SymDomain

A domain is a Cartesian product of `DomBlock`s, each a connected group of
variables and the constraints coupling them.
`constraints` is the single source of truth: every constraint appears exactly once,
sorted by Id (so lookup by Id is a binary search). `factors` partition those
constraints by Id.

TODO: rename factors to blocks comprehensively in all DomBlock related semantics
"""
struct SymDomain
    constraints::Tuple{Vararg{DomConstraint}}
    factors::Tuple{Vararg{DomBlock}}
    variables::Tuple{Vararg{Symbolics.Num}}

    function SymDomain(constraints::AbstractVector{DomConstraint}, factors::AbstractVector{DomBlock})
        sorted = sort(collect(DomConstraint, constraints), by=c -> c.id)
        for i in eachindex(sorted)
            sorted[i].id == UNASSIGNED_ID &&
                throw(ArgumentError("constraints must have an Id (or a provisional one) before they enter a SymDomain"))
            i > 1 && sorted[i].id == sorted[i-1].id &&
                throw(ArgumentError("duplicate domain constraint id $(sorted[i].id)"))
        end

        claimed = falses(length(sorted))
        seen_variables = Symbolics.Num[]
        canonical = DomBlock[]

        for factor in factors
            variables = Symbolics.Num[]
            for v in factor.variables
                any(isequal(v), variables) || push!(variables, v)
            end
            isempty(variables) && throw(ArgumentError("domain factors cannot be empty"))
            for v in variables
                any(isequal(v), seen_variables) &&
                    throw(ArgumentError("variable $v appears in more than one domain factor"))
                push!(seen_variables, v)
            end
            sort!(variables, by=string)

            for id in factor.constraint_ids
                i = _constraint_index(sorted, id)
                i == 0 && throw(ArgumentError("factor refers to unknown constraint id $id"))
                claimed[i] && throw(ArgumentError("constraint $id belongs to more than one factor"))
                claimed[i] = true
                for v in constraint_variables(sorted[i])
                    _contains_equal(variables, v) ||
                        throw(ArgumentError("constraint $id references variable $v outside its factor"))
                end
            end

            members = ConstraintId[id for id in factor.constraint_ids]
            sort!(members, by=id -> _constraint_sort_key(sorted[_constraint_index(sorted, id)]))
            variables_t, members_t = Tuple(variables), Tuple(members)

            # An already-canonical factor is kept as is (object and paving). A
            # re-ordered one gets a new object with no paving: the paving's box
            # coordinates follow `variables`, so it would no longer line up.
            is_canonical = length(factor.variables) == length(variables_t) &&
                all(isequal(a, b) for (a, b) in zip(factor.variables, variables_t)) &&
                factor.constraint_ids == members_t
            push!(canonical, is_canonical ? factor : DomBlock(variables_t, members_t))
        end

        all(claimed) || throw(ArgumentError("every constraint must belong to a factor"))
        sort!(canonical, by=f -> string(f.variables[begin]))
        all_variables = Symbolics.Num[v for f in canonical for v in f.variables]
        new(Tuple(sorted), Tuple(canonical), Tuple(all_variables))
    end
end

# ===========================================================================
# 4. Series & Boundary Conditions
# ===========================================================================
struct SeriesTerm
    index::Symbolics.Num                 # e.g., n
    index_domain::SymDomain              # e.g., n >= 1
    eigenvalues::Vector{SymEquation}     # e.g., [λ_n ~ (n*π/L)^2]
    summand::Symbolics.Num               # e.g., A_n * sin(n*π*x/L) * exp(-λ_n*t)
end

# Register SeriesSum(term::SeriesTerm) so it can live inside any SymEquation residual!
@register_symbolic SeriesSum(term::SeriesTerm)

abstract type Locus end

struct Face <: Locus           # constraint(s) from the system's domain, made active
    constraints::Tuple{Vararg{ConstraintId}}   # 1 = face, 2+ = edge/corner (intersection)
end

struct Explicit <: Locus       # escape hatch: interior slices, e.g. u(t=0.5)
    eqs::Vector{SymRelation}
end

struct Interior <: Locus end   # whole domain (for integrals)

struct Limit <: Locus
    var::Symbolics.Num
    direction::Symbol #:pos,:neg,:both
end

struct ExhaustiveLimit <: Locus
    family::DomConstraint   # e.g. x^2 < R, with R -> ∞
    param::Symbolics.Num    # e.g. R
    target::Symbolics.Num   # e.g. ∞ or 0
end

struct BoundaryCondition
    id::Int
    relation::SymRelation
    locus::Locus
end

# ===========================================================================
# 5. Transforms & Derivation History
# ===========================================================================
abstract type Transform end

struct XStep
    cause::Union{Nothing,Int} # in the future special algorithms could also be referenced as the cause of a step
    step::Transform
end

struct XChain
    steps::Vector{XStep}
end
XChain() = XChain(XStep[])

struct IvTransform <: Transform
    iv_mapping::Dict
    old_ivs::Vector{Symbolics.Num}
    new_ivs::Vector{Symbolics.Num}
end

struct PsTransform <: Transform
    mapping::Dict
    old_parameters::Vector{Symbolics.Num}
    new_parameters::Vector{Symbolics.Num}
end

struct DvTransform <: Transform
    mapping::Dict
    old_dvs::Vector{Symbolics.Num}
    new_dvs::Vector{Symbolics.Num}
end

"""
Configuration for the system simplifier.
The pass limit is deliberately explicit. Simplification can increase expression
size, so the number of fixed-point passes is bounded.
"""
Base.@kwdef struct SimplificationOptions
    # Iteration caps
    max_stabilizer_passes::Int = 4      # per-region rounds in _improve
    max_rounds::Int = 4                 # outer fixpoint over phases
    # Size limits (DAG nodes, matching the region storage)
    max_nodes::Int = 100_000            # total headroom for the algebraic pass
    max_derivative_nodes::Int = 50_000  # reject a derivative expansion above this
    # Feature switches (only things that currently have code behind them)
    expand_derivatives::Bool = true
    expand_products::Bool = true        # gates `expand` in _improve only
    # Symbolic rules for _nonalgebraic_pass, composed by the caller
    rules::Vector{Any} = Any[]
    function SimplificationOptions(msp, mr, mn, mdn, ed, ep, rules)
        msp >= 1 || throw(ArgumentError("max_stabilizer_passes must be >= 1"))
        mr >= 1 || throw(ArgumentError("max_rounds must be >= 1"))
        mn >= 1 || throw(ArgumentError("max_nodes must be >= 1"))
        mdn >= 0 || throw(ArgumentError("max_derivative_nodes must be >= 0"))
        return new(msp, mr, mn, mdn, ed, ep, rules)
    end
end

struct Simplification <: Transform
    options::SimplificationOptions
end

# ===========================================================================
# 6. Differential Equation Systems & Solution Leaves
# ===========================================================================
mutable struct DESys{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector,B<:AbstractVector{<:Symbolics.Equation}}
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain
    restrictions::Vector{SymRelation}
end

@enum SolutionForm EXPLICIT IMPLICIT PARAMETRIC
@enum SolutionRole GENERAL PARTICULAR SINGULAR

"""
    SolutionFamily

Encapsulates the mathematical equations of the solved family and its remaining degrees of freedom.
"""
Base.@kwdef struct SolutionFamily
    form::SolutionForm = EXPLICIT
    role::SolutionRole = GENERAL
    relations::Vector{SymEquation} = SymEquation[]       # The solutions (SeriesSum lives inside these!)
    dofs::Vector{Symbolics.Num} = Symbolics.Num[]        # Unified DoFs: C_1, A(n), F(x - c*t)
    dof_constraints::Vector{SymEquation} = SymEquation[] # Optional ties between DoFs
end

"""
    SolvedLeaf

Mirrors `DESys` for a completed leaf node: holds the system context, any unapplied BCs, and the `SolutionFamily`.
"""
Base.@kwdef struct SolvedLeaf{
    I<:AbstractVector{<:Symbolics.Num},
    D<:AbstractVector{<:Symbolics.Num},
    P<:AbstractVector{<:Symbolics.Num},
    B<:AbstractVector{<:Symbolics.Equation}
}
    # Core System Context (matches DESys layout directly)
    ivs::I
    dvs::D
    ps::P
    bcs::B                                           # Unapplied BCs (emptied as DoFs are eliminated)
    domain::SymDomain
    restrictions::Vector{SymRelation} = SymRelation[]
    history::XChain = XChain(XStep[])
    # The Solved Payload
    family::SolutionFamily
end

struct RootSys{I<:Tuple,D<:Tuple,P<:Tuple,E<:Tuple,B<:Tuple}
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain
end

# ===========================================================================
# 7. Derivation Tree & Split Nodes
# ===========================================================================
abstract type Node end
abstract type Split end

Base.@kwdef struct RootNode <: Node
    id::NodeId
    child_id::NodeId
    system::RootSys
end

Base.@kwdef struct ActiveNode <: Node
    id::NodeId
    parent_id::NodeId
    system::DESys
    history::XChain = XChain(XStep[])
end

Base.@kwdef struct SolvedNode <: Node
    id::NodeId
    parent_id::NodeId
    solution::SolvedLeaf
    history::XChain
end

Base.@kwdef struct SplitNode <: Node
    id::NodeId
    parent_id::NodeId
    child_ids::Vector{NodeId}
    splittype::Split
    history::XChain
end

struct Interface # the interface conditions between one pair of branches that were split from a common parent
    a_id::NodeId
    b_id::NodeId
    locus::Symbolics.Equation
    crossing::Symbol               # :impossible | :matching | :branching | :undetermined
    conditions::Vector{Any}        # e.g. continuity of y and y' across the locus
end

struct DomainSplit <: Split
    split::Dict{Any,NodeId} # each pair is the domain constraint that was added to its paired child node
    type::Symbol            # :dichotomic | :trichotomic
    locus::Symbolics.Equation
    interfaces::Vector{Interface}
end

struct FactorSplit <: Split
    split::Dict{Any,NodeId} # each pair is the factor that was added to its paired child node
end

struct GuardSplit <: Split
    main::Pair{Symbolics.Equation,NodeId}
    guard::Pair{SymRelation,NodeId}
end

"""
Collection of branches representing a union of solution sets.
Branch generation is responsible for maintaining disjoint partition cells. No
global duplicate set is kept: a branch's inherited restrictions are part of the
logical cell it represents.
"""
mutable struct DETree
    nodes::Dict{NodeId,Node}
    active::Stack{NodeId}
    solved::Vector{NodeId}
    root::RootNode
    id_counter::Int # one counter shared by every kind of Id (nodes, constraints, ...)
end

# ===========================================================================
# 8. Divisibility & Sign Inference Types
# ===========================================================================
@enum SignState positive negative iszero either undetermined
@enum DivisState divisible haszero undetermined

"""
    ConstraintEvidence

Internal result for the factor zero-set pipeline. The public decision is `bound`;
`divisibility` and `sign` make numerical decisions inspectable and give later
stages a place to return their proof object.
"""
struct ConstraintEvidence
    bound::IntervalArithmetic.Interval
    divisibility::DivisState
    sign::SignState
end

"""
    EvidenceDomain

The part of a leaf's domain that bears on one expression: only the domain
factors that share a variable with it. Every other factor is irrelevant to the
expression and is never looked at.
"""
mutable struct EvidenceDomain
    source::SymDomain
    factors::Vector{DomBlock}
    key::Any
    sub::Union{Nothing,SymDomain}
end
