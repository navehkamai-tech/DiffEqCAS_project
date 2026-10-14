"""
    SymRelation(residual, relation)

A branch-local relation between a symbolic residual and zero.  Equalities are
represented by the branch equations; restrictions represent only non-equality
relations used to describe a branch cell.
"""
struct SymRelation
    residual::Symbolics.Num
    relation::Symbol

    function SymRelation(residual, relation)
        relation_symbol = relation isa Symbol ? relation : Symbol(string(relation))
        relation_symbol in (Symbol("!="), :>, Symbol(">="), :<, Symbol("<=")) ||
            throw(ArgumentError("unsupported symbolic restriction relation: $relation"))
        new(wrap(residual), relation_symbol)
    end
end

const _restriction_relations = (Symbol("!="), :>, Symbol(">="), :<, Symbol("<="))

function _get_relation(rel::SymRelation)
    relation = rel.relation
    relation === Symbol("!=") && return !=
    relation === :> && return >
    relation === Symbol(">=") && return >=
    relation === :< && return <
    relation === Symbol("<=") && return <=
end

function _eq_from_rel(rel::SymRelation)
    _get_relation(rel) !== (==) & return nothing
    return Symbolics.Equation(rel.residual, 0)
end

Symbolics.simplify(rel::SymRelation) = SymRelation(simplify(rel.residual), rel.relation)
Symbolics.expand(rel::SymRelation) = SymRelation(expand(rel.residual), rel.relation)

"""
    SymDomain

A domain is a set of constraints over a set of variables.  It is represented as a
tuple of pairs, where each pair consists of a key (a variable or tuple of
variables) and a tuple of constraints.
"""
struct SymDomain
    pairs::Tuple{Vararg{Pair{Any,Tuple{Vararg{SymRelation}}}}}
    variables::Tuple{Vararg{Symbolics.Num}}

    function SymDomain(pairs::AbstractVector{<:Pair{Any,AbstractVector{<:SymRelation}}})
        normalized = Pair[]
        variables = Any[]
        for pair in pairs
            pair isa Pair || throw(ArgumentError("domain entries must be pairs of variables and constraints"))
            key, constraints = pair
            key_variables = key isa Tuple ? collect(key) : Any[key]
            isempty(key_variables) && throw(ArgumentError("domain keys cannot be empty"))

            (constraints isa AbstractVector || constraints isa Tuple) ||
                throw(ArgumentError("domain constraints must be stored in a vector or tuple"))

            sort!(key_variables, by=string)
            for variable in key_variables
                any(isequal(variable), variables) || push!(variables, variable)
            end

            key isa Tuple ? sort!(key, by=string) : nothing

            # Convert the constraints list to a Tuple so the Pair holds deeply immutable data
            push!(normalized, key => Tuple(constraints))
        end
        sort!(normalized, by=pair -> string(pair.first isa Tuple ? pair.first[begin] : pair.first))

        # Finalize into Tuples instead of Vectors
        new(Tuple(normalized), Tuple(variables))
    end
end

function domain_product(domain1::SymDomain, domain2::SymDomain)
    isempty(intersect(domain1.variables, domain2.variables)) || throw(ArgumentError("domains must have different variables"))
    combined_pairs = Vector(domain1.pairs..., domain2.pairs...)
    sort!(combined_pairs, by=pair -> string(pair.first))
    return SymDomain(combined_pairs)
end

*(domain1::SymDomain, domain2::SymDomain) = domain_product(domain1, domain2)

struct Paving{N,T}
    interior::Vector{IntervalBoxes.IntervalBox{N,T}}
    boundary::Vector{IntervalBoxes.IntervalBox{N,T}}
end

Base.length(domain::SymDomain) = length(domain.pairs)
Base.getindex(domain::SymDomain, index::Int) = domain.pairs[index]
Base.iterate(domain::SymDomain, state...) = iterate(domain.pairs, state...)
Base.isempty(domain::SymDomain) = isempty(domain.pairs)

_domain_pairs(domain::SymDomain) = domain.pairs
_domain_pairs(domain) = domain

# Components are the connected groups represented by the domain keys. They are
# structural metadata only; integral factorization also requires a separable
# integrand and a product domain.
domain_variables(domain::SymDomain) = copy(domain.variables)
domain_components(domain::SymDomain) = copy(domain.pairs)

const EqId = Int

struct SymEquation
    id::EqId
    residual::Symbolics.Num

    function SymEquation(lhs, rhs)
        new(id, wrap(lhs) - wrap(rhs))
    end
end

Symbolics.simplify(eq::SymEquation) = SymEquation(eq.id, simplify(eq.residual))
Symbolics.expand(eq::SymEquation) = SymEquation(eq.id, expand(eq.residual))




abstract type Transform end

struct TransformStep
    cause::Union{Nothing,Int} #in the future special algorithms could also be referenced as the cause of a step
    step::Transform
end

struct TransformChain
    steps::Vector{TransformStep}
end

function append_transform(history::TransformChain, step::Transform;
    cause::Union{Nothing,Int}=nothing)
    TransformChain(vcat(history.steps, [TransformStep(cause, step)]))
end

last_index(history::TransformChain) = length(history.steps)

struct CoordTransform <: Transform
    iv_mapping::Dict
    old_ivs::Vector{Symbolics.Num}
    new_ivs::Vector{Symbolics.Num}
end

struct ParamTransform <: Transform
    mapping::Dict
    old_parameters::Vector{Symbolics.Num}
    new_parameters::Vector{Symbolics.Num}
end

struct DepTransform <: Transform
    mapping::Dict
    old_dvs::Vector{Symbolics.Num}
    new_dvs::Vector{Symbolics.Num}
end

mutable struct DiffEqLeaf{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:SymEquation},B<:AbstractVector{<:Symbolics.Equation}}
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain
    domain_set::Union{Nothing,Paving}
    restrictions::Vector{SymRelation}
end

function Base.setproperty!(sys::DiffEqLeaf, name::Symbol, value)
    if name === :domain
        normalized = value isa SymDomain ? value : SymDomain(value)
        setfield!(sys, :domain, normalized)
        setfield!(sys, :domain_set, nothing)
        return normalized
    end
    setfield!(sys, name, value)
end

function DiffEqLeaf(eqs, bcs, domain, ivs, dvs; ps=Symbolics.Num[], name=:system,
    domain_set=nothing, restrictions=SymRelation[],
    history=DerivationHistory())
    normalized_ivs = Symbolics.Num[ivs...]
    normalized_dvs = Symbolics.Num[dvs...]
    normalized_ps = Symbolics.Num[ps...]
    normalized_eqs = Symbolics.Equation[eqs...]
    normalized_bcs = Symbolics.Equation[bcs...]
    normalized_domain = domain isa SymDomain ? domain : SymDomain(domain)
    normalized_restrictions = SymRelation[restrictions...]
    DiffEqLeaf(String(name), normalized_ivs, normalized_dvs, normalized_ps,
        normalized_eqs, normalized_bcs, normalized_domain, domain_set,
        normalized_restrictions, history)
end

function DiffEqLeaf(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system, domain_set=nothing,
    restrictions=SymRelation[], history=DerivationHistory())
    DiffEqLeaf(eqs, bcs, domain, ivs, dvs; ps=ps, name=name,
        domain_set=domain_set, restrictions=restrictions,
        history=history)
end

# needs to be redone to trace the history up the tree
_with_history(b::DiffEqLeaf, h::DerivationHistory) = DiffEqLeaf(
    eqs=b.eqs, ivs=b.ivs, dvs=b.dvs, ps=b.ps, bcs=b.bcs, domain=b.domain,
    name=b.name, domain_set=b.domain_set, restrictions=b.restrictions, history=h)

struct RootDiffEq{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:Symbolics.Equation},B<:AbstractVector{<:Symbolics.Equation}}
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain
end

function RootDiffEq(DiffEqLeaf)
    ivs = tuple(DiffEqLeaf.ivs...)
    dvs = tuple(DiffEqLeaf.dvs...)
    ps = tuple(DiffEqLeaf.ps...)
    eqs = tuple(DiffEqLeaf.eqs...)
    bcs = tuple(DiffEqLeaf.bcs...)
    RootDiffEq(ivs, dvs, ps, eqs, bcs, DiffEqLeaf.domain)
end

const NodeId = Int
abstract type Node end
abstract type Split end

struct RootNode <: Node
    id::NodeId
    child_id::NodeId
    system::RootDiffEq
end

Base.@kwdef struct ActiveNode <: Node
    id::NodeId
    parent_id::NodeId
    system::DiffEqLeaf
    history::TransformChain=TransformChain(TransformStep[])
end

struct SolvedNode <: Node
    id::NodeId
    parent_id::NodeId
    solution::SolvedLeaf #needs to be defined
    history::TransformChain
end

struct SplitNode <: Node
    id::NodeId
    parent_id::NodeId
    child_ids::Vector{NodeId}
    splittype::Split
    history::TransformChain
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
    guard::Pair{SymbolicRestriction,NodeId}
end
"""
Collection of branches representing a union of solution sets.

Branch generation is responsible for maintaining disjoint partition cells.
No global duplicate set is kept: a branch's inherited restrictions are part of
the logical cell it represents.
"""
mutable struct DiffEqTree
    nodes::Dict{NodeId,Node}
    active::Stack{NodeId}
    solved::Vector{NodeId}
    root::RootNode
    id_counter::Int
end

function next_node_id!(tree::DiffEqTree)
    tree.id_counter += 1
    return tree.id_counter
end

function initialize_system(sys::DiffEqLeaf)
    root_id = 1
    child_id = 2

    root = RootNode(id=root_id, child_id=child_id, system=RootDiffEq(sys))
    child = ActiveNode(id=child_id, parent_id=root_id, system=sys)

    nodes_dict = Dict{NodeId,Node}(child_id => child, root_id => root)

    active_stack = Stack{NodeId}()
    push!(active_stack, child_id)

    return DiffEqTree(nodes_dict, active_stack, NodeId[], root, child_id)
end

# Replace a branch's state without replacing the branch object stored by its
# parent system.  This also preserves branch-local metadata not involved in
# the transformation.
# needs to be updated to handle the history of transformations, so should probably take in an ActiveNode and return an ActiveNode with the updated history
function _replace_branch!(
    branch::DiffEqLeaf;
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

Base.length(system::DiffEqSystem) = length(system.nodes)
Base.getindex(system::DiffEqSystem, index::Int) = system.nodes[index]

function new_node!(system::DiffEqTree, parent::NodeId, branch::DiffEqLeaf)
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
function split_node!(system::DiffEqTree, node::ActiveNode, new_children::Vector{ActiveNode}, split::Split)
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
function complete_node!(system::DiffEqTree, node::ActiveNode, solution::SolvedLeaf)
    solved_node = SolvedNode(node.id, node.parent_id, solution, history=node.history)
    system.nodes[solved_node.id] = solved_node
    push!(system.solved, solved_node.id)
end

#=
the goal has changed, I've accepted I need a treelike structure.
rather than a DiffEqSystem wrapper type I should have a node struct. 
there are two types of nodes, one is the root and intermediates, and the second is the leaves.
to be memory efficient leaves are the only node that should be able to contain a DiffEqLeaf 
leaves that are solved should not necessarily store an entire DiffEqLeaf but something else.

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