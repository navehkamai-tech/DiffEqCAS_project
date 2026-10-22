# ===========================================================================
# 1. Identifiers
# ===========================================================================
"""
Stable identity of a node, domain constraint, or equation.
Drawn from the same per-tree counter as every other Id (see `next_id!`), so it is
unique across the whole tree, is inherited unchanged by child nodes, and survives
rewrites of the constraint's expression (change of variables, simplification).
Boundary conditions refer to a constraint by this Id, never by its position.
"""
const NodeId = Int
const ConstraintId = Int
const EqId = Int

const _GLOBAL_ID_COUNTER = Threads.Atomic{Int}(0)
fresh_id() = Threads.atomic_add!(_GLOBAL_ID_COUNTER, 1) + 1

# ===========================================================================
# 2. Symbolic Relations & Equations
# ===========================================================================
const _LT = Symbol("<")
const _LE = Symbol("<=")
const _GT = Symbol(">")
const _GE = Symbol(">=")
const _EQ = Symbol("==")
const _NE = Symbol("!=")

const _RELATIONS = Set([_LT, _LE, _GT, _GE, _EQ, _NE])

"""
    SymRelation(residual, relation)

A relation between a symbolic residual and zero. 
"""
struct SymRelation
    residual::Symbolics.Num
    relation::Symbol

    function _unchecked_relation(residual, relation)
        rel_sym = _relation_symbol(relation)
        new(wrap(residual), rel_sym)
    end
end

struct SymEquation
    id::EqId
    residual::Symbolics.Num
    function SymEquation(residual::Symbolics.Num, id::EqId=fresh_id())
        new(id, residual)
    end
end

# ===========================================================================
# 3. Domain Types
# ===========================================================================
"""
    Constraint(id, relation)

A `SymRelation` (`residual ⋈ 0`) together with its identity. The Id is
bookkeeping, not part of the constraint's meaning: two constraints with equal
`relation` describe the same set no matter what their Ids are.
"""
struct Constraint
    id::ConstraintId
    relation::SymRelation
end

Constraint(relation::SymRelation) = Constraint(fresh_id(), relation)
Constraint(expr::Symbolics.Num) = Constraint(fresh_id(), SymRelation(expr))

constraint_variables(c::Constraint) =
    Symbolics.get_variables(Symbolics.unwrap(c.relation.residual))

# Canonical order inside a block: by content, never by Id, so a domain does
# not depend on the order its constraints were supplied in. The Id is only a
# final tie-break between constraints with identical content.
_content_key(c::Constraint) = (string(c.relation.residual), String(c.relation.relation))
_constraint_sort_key(c::Constraint) = (_content_key(c)..., c.id)

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
    DomBlock(variables, constraint_ids, [paving])

One block of a domain: a set of variables together with the
constraints that couple them. The domain is the Cartesian product of its factors.
A factor stores only the *Ids* of its constraints; the constraint data lives once,
in `SymDomain.constraints`.
"""
mutable struct DomBlock
    variables::Vector{Symbolics.Num}      # canonical order (by string)
    constraint_ids::Vector{ConstraintId}  # canonical order (by content)
end

"""
    SymDomain

A domain is a Cartesian product of `DomBlock`s, each a connected group of
variables and the constraints coupling them.
`constraints` is the single source of truth: every constraint appears exactly once,
sorted by Id (so lookup by Id is a binary search). `blocks` partition those
constraints by Id.

Use `_unchecked_domain(constraints, factors, variables)` for internal fast-path
construction when invariants are already guaranteed, or `SymDomain(...)` in
`domain_algebra.jl` for validated and canonicalized construction.
"""
struct SymDomain
    constraints::Vector{Constraint}
    blocks::Vector{DomBlock}
    variables::Vector{Symbolics.Num}

    global _unchecked_domain(
        constraints::Vector{Constraint},
        blocks::Vector{DomBlock},
        variables::Vector{Symbolics.Num},
    ) = new(constraints, blocks, variables)
end

function _unchecked_domain(constraints::Vector{Constraint}, blocks::Vector{DomBlock})
    variables = Symbolics.Num[v for b in blocks for v in b.variables]
    return _unchecked_domain(constraints, blocks, variables)
end

function _unchecked_domain(constraints::Vector{Constraint})
    blocks = DomBlock[]
    variables = Symbolics.Num[]
    return _unchecked_domain(constraints, blocks, variables)
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
    family::Constraint   # e.g. x^2 < R, with R -> ∞
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
    ps_constraints::Vector{Constraint}
    restrictions::Vector{Constraint}
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
end

# ===========================================================================
# 8. Divisibility & Sign Inference Types
# ===========================================================================
const _BI = BareInterval{Float64}

@inline _bi(a::Real, b::Real) = bareinterval(Float64(a), Float64(b))
@inline _bi(a::Real) = bareinterval(Float64(a))
@inline _bi(x::_BI) = x
@inline _bi(x::Interval) = bareinterval(x)
@inline _empty_bi() = emptyinterval(_BI)
@inline _entire_bi() = entireinterval(_BI)


const _SIGNS = (:neg, :zero, :pos)
@enum Answer Yes No Unknown

struct Comp
    constraints::Vector{Constraint}
    variables::Vector{Symbolics.Num}
    key::UInt64
end

struct Ctx
    comps::Vector{Comp}
    params::Vector{Constraint}
    key::Tuple
end

Base.@kwdef struct Evidence
    outer::_BI = _entire_bi()
    strict_lo::Bool = false
    strict_hi::Bool = false
    neg::Answer = Unknown
    zero::Answer = Unknown
    pos::Answer = Unknown
    ident_zero::Bool = false
end

const _EMPTY_EVIDENCE = Evidence(outer=_empty_bi(), neg=No, zero=No, pos=No)   # nothing attainable
const _IDENT_ZERO = Evidence(outer=_bi(0.0, 0.0), neg=No, zero=Yes, pos=No, ident_zero=true)
const _ALL = (:neg, :zero, :pos)

#------------------------------------------
# Paving & cache
#------------------------------------------

const ROI = Ref{Float64}(10000.0)
const tolerance = Ref{Float64}(0.01)

#=
this is how to Change the global bound for this session
DiffEqCAS.ROI[] = 50000.0
=#

const cache_size = Ref{Int64}(16384)
global cache = LRU{Any,Any}(maxsize=cache_size[])

