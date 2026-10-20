
function initialize_system(sys::DESys)
    root_id = fresh_id()
    child_id = fresh_id()

    root = RootNode(id=root_id, child_id=child_id, system=RootSys(sys))
    child = ActiveNode(id=child_id, parent_id=root_id, system=sys)

    nodes_dict = Dict{NodeId,Node}(child_id => child, root_id => root)

    active_stack = Stack{NodeId}()
    push!(active_stack, child_id)

    return DETree(nodes_dict, active_stack, NodeId[], root)
end

Base.length(system::DETree) = length(system.nodes)
Base.getindex(system::DETree, index::Int) = system.nodes[index]

function new_node!(system::DETree, parent::NodeId, branch::DESys)
    new_id = fresh_id()
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