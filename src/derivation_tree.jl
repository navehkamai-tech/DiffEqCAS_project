
@enum SolutionForm EXPLICIT IMPLICIT PARAMETRIC
@enum SolutionRole GENERAL PARTICULAR SINGULAR

"""
    SolutionFamily
Encapsulates the mathematical equations of the solved family and its remaining degrees of freedom.
"""
Base.@kwdef struct SolutionFamily
    form::SolutionForm = EXPLICIT
    role::SolutionRole = GENERAL
    relations::Vector{SymEquation} = SymEquation[]  # The solutions (SeriesSum lives inside these!)
    dofs::Vector{Symbolics.Num} = Symbolics.Num[]   # Unified DoFs: C₁, A(n), F(x - c*t)
    dof_constraints::Vector{SymEquation} = SymEquation[] # Optional ties between DoFs, e.g. ω ~ α*k^2
end

"""
    SolvedLeaf
Mirrors `DESys` for a completed leaf node: holds the system context,
any unapplied BCs, and the `SolutionFamily`.
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

abstract type Transform end

struct XStep
    cause::Union{Nothing,Int} #in the future special algorithms could also be referenced as the cause of a step
    step::Transform
end

struct XChain
    steps::Vector{XStep}
end

function append_transform(history::XChain, step::Transform;
    cause::Union{Nothing,Int}=nothing)
    XChain(vcat(history.steps, [XStep(cause, step)]))
end

last_index(history::XChain) = length(history.steps)

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

mutable struct DESys{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:SymEquation},B<:AbstractVector{<:Symbolics.Equation}}
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain
    restrictions::Vector{SymRelation}
end

function Base.setproperty!(sys::DESys, name::Symbol, value)
    # Pavings live on the domain's factors, so replacing the domain needs no invalidation.
    name === :domain && (value = _as_domain(value))
    setfield!(sys, name, value)
end

function DESys(eqs, bcs, domain, ivs, dvs; ps=Symbolics.Num[],
    restrictions=SymRelation[])
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
    restrictions=SymRelation[], history=XChain())
    DESys(eqs, bcs, domain, ivs, dvs; ps=ps, name=name,
        restrictions=restrictions, history=history)
end

# needs to be redone to trace the history up the tree
_with_history(b::DESys, h::XChain) = DESys(
    eqs=b.eqs, ivs=b.ivs, dvs=b.dvs, ps=b.ps, bcs=b.bcs, domain=b.domain,
    name=b.name, restrictions=b.restrictions, history=h)

is_in_domain(coord::StaticArrays.SVector, sys::DESys, include_boundary::Bool=true) =
    is_in_domain(coord, sys.domain, include_boundary)

struct RootSys
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain

    function RootSys(sys::DESys)
    ivs = tuple(DESys.ivs...)
    dvs = tuple(DESys.dvs...)
    ps = tuple(DESys.ps...)
    eqs = tuple(DESys.eqs...)
    bcs = tuple(DESys.bcs...)
    RootSys(ivs, dvs, ps, eqs, bcs, DESys.domain)
end
end

const NodeId = Int
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
    history::XChain=XChain(XStep[])
end

Base.@kwdef struct SolvedNode <: Node
    id::NodeId
    parent_id::NodeId
    solution::SolvedLeaf #needs to be defined
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
    split::Dict{Any,NodeId} # each pair is the domain constraint that was added to it's paired child node
    type::Symbol # :dichotomic | :trichotomic
    locus::Symbolics.Equation
    interfaces::Vector{Interface}
end

struct FactorSplit <: Split
    split::Dict{Any,NodeId} # each pair is the factor that was added to it's paired child node
end

struct GuardSplit <: Split
    main::Pair{Symbolics.Equation,NodeId}
    guard::Pair{SymRelation,NodeId}
end
"""
Collection of branches representing a union of solution sets.

Branch generation is responsible for maintaining disjoint partition cells.
No global duplicate set is kept: a branch's inherited restrictions are part of
the logical cell it represents.
"""
mutable struct DETree
    nodes::Dict{NodeId,Node}
    active::Stack{NodeId}
    solved::Vector{NodeId}
    root::RootNode
    id_counter::Int # one counter shared by every kind of Id (nodes, constraints, ...)
end

# Every Id in the tree comes from this one counter, so an Id is unique across
# kinds as well as within one.  The typed wrappers below only document intent.
next_id!(tree::DETree) = (tree.id_counter += 1)
next_node_id!(tree::DETree)::NodeId = next_id!(tree)
next_constraint_id!(tree::DETree)::ConstraintId = next_id!(tree)
next_equation_id!(tree::DETree)::EqId = next_id!(tree)

function initialize_system(sys::DESys)
    root_id = 1
    child_id = 2
    id_counter = child_id

    # Register the domain's constraints with this tree *before* the root snapshot
    # is taken, so root and child share the same constraint Ids.
    sys.domain = assign_ids(sys.domain, () -> (id_counter += 1))

    root = RootNode(id=root_id, child_id=child_id, system=RootSys(sys))
    child = ActiveNode(id=child_id, parent_id=root_id, system=sys)

    nodes_dict = Dict{NodeId,Node}(child_id => child, root_id => root)

    active_stack = Stack{NodeId}()
    push!(active_stack, child_id)

    return DETree(nodes_dict, active_stack, NodeId[], root, id_counter)
end

# Replace a branch's state without replacing the branch object stored by its
# parent system.  This also preserves branch-local metadata not involved in
# the transformation.
# needs to be updated to handle the history of transformations, so should probably take in an ActiveNode and return an ActiveNode with the updated history
function _replace_branch!(
    branch::DESys;
    eqs=branch.eqs, ivs=branch.ivs, dvs=branch.dvs, ps=branch.ps, bcs=branch.bcs, domain=branch.domain, history=branch.history, restrictions=branch.restrictions
)
    # Constructors used to perform this conversion implicitly.  Keep it here
    # because transformed intermediate collections may have eltype `Any`.
    branch.eqs = typeof(branch.eqs)(eqs)
    branch.ivs = typeof(branch.ivs)(ivs)
    branch.dvs = typeof(branch.dvs)(dvs)
    branch.ps = typeof(branch.ps)(ps)
    branch.bcs = typeof(branch.bcs)(bcs)
    branch.domain = domain
    branch.restrictions = SymRelation[restrictions...]
    branch
end

Base.length(system::DETree) = length(system.nodes)
Base.getindex(system::DETree, index::Int) = system.nodes[index]

function new_node!(system::DETree, parent::NodeId, branch::DESys)
    new_id = next_node_id!(system)
    new_node = ActiveNode(id=new_id, parent_id=parent, system=branch)
    push!(system.active, new_id)
    system.nodes[new_id] = new_node
    push!(system.nodes[parent].child_ids, new_id)
end

"""
Split a node into multiple child nodes.
assumes the node was already popped from the active stack and is no longer active
the new children are added to the active stack and the original node is replaced with a SplitNode
"""
function split_node!(system::DETree, node::ActiveNode, new_children::Vector{ActiveNode}, split::Split)
    # 1. Create a new SplitNode to represent the split
    split_node = SplitNode(node.id, node.parent_id, [child.id for child in new_children], split, history=node.history)
    system.nodes[split_node.id] = split_node
    for child in new_children
        system.nodes[child.id] = child
        push!(system.active, child.id)
    end
end

"""
Complete a node by changing it to a solved node.
assumes the node was already popped from the active stack and is no longer active
the new solved node is added to the solved list and the original node is replaced with a SolvedNode
"""
function complete_node!(system::DETree, node::ActiveNode, solution::SolvedLeaf)
    solved_node = SolvedNode(node.id, node.parent_id, solution, history=node.history)
    system.nodes[solved_node.id] = solved_node
    push!(system.solved, solved_node.id)
end

function is_in_domain(coord::StaticArrays.SVector, sys::DETree,
    include_boundary::Bool=true)
    # the system domain is a union of the domains of its branches, so a point is in the system domain if it is in any branch's domain
    any(is_in_domain(coord, sys.nodes[leaf_id], include_boundary) for leaf_id in vcat(sys.active, sys.solved))
end

#=
the goal has changed, I've accepted I need a treelike structure.
rather than a DETree wrapper type I should have a node struct. 
there are two types of nodes, one is the root and intermediates, and the second is the leaves.
to be memory efficient leaves are the only node that should be able to contain a DESys 
leaves that are solved should not necessarily store an entire DESys but something else.

as for leaves that contain a contradiction:
option 1: I make sure that's impossible and can never happen (unless it's the root node and no splitting has occured yet)
option 2: I trace back the contradiction to it's origin and prune everything following it.
in principle I like option 1 better since it avoids the headache entirely, but I'll have to see what makes the most sense.

each node should contain it's parent and children, but in a special relation struct containing the information for why the system split.
most splits will be into 2 factors, but there can be trichotomic splits or theoretically factorization splits with an arbitrary number of children

the types of split will be: DomainSplit, FactorSplit, SeparationSplit, SingularSplit, TransformSplit. 

a DomainSplit must contain the domain constraint that caused the split, each child with the domain assumption that was added to it, and the boundary between them, along with wether they need to be glued together smoothly and under what conditions. 
there could be two different types for dichotomic and trichotomic, remains to be seen.
each child's domain is updated with it's additional constraint

a FactorSplit must contain the equation that was factored and what branch took each factor
each child's assumptions are updated with the factors that were not chosen for it not being 0 

a SeparationSplit will probably be simple as it will be accounting specifically for separation of variables

a SingularSplit is similar to a FactorSplit, but the equation doesn't factor multiplicatively, there just happens to be a singular solution. 
the children in this case are heterogenous, one being the singular solution and the other updating it's assumptions to not contain that singular solution.

a TransformSplit is for when a transformation is when the map from old variables to new variables is not injective, so the inverse map is not unique. 
thus a branch is created for each possible inverse map. 
=#