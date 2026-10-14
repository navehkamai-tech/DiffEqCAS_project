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

# ---------------------------------------------------------------------------
# Domain constraints and their identity
# ---------------------------------------------------------------------------

"""
Stable identity of a domain constraint.

Drawn from the same per-tree counter as every other Id (see `next_id!`), so it
is unique across the whole tree, is inherited unchanged by child nodes, and
survives rewrites of the constraint's expression (change of variables,
simplification).  Boundary conditions refer to a constraint by this Id, never by
its position.  `UNASSIGNED_ID` marks a constraint that has not been registered
with a tree yet; see `assign_ids`.
"""
const ConstraintId = Int
const UNASSIGNED_ID = 0

"""
    DomConstraint(id, relation)

A `SymRelation` (`residual ⋈ 0`) together with its identity.  The Id is
bookkeeping, not part of the constraint's meaning: two constraints with equal
`relation` describe the same set no matter what their Ids are.
"""
struct DomConstraint
    id::ConstraintId
    relation::SymRelation
end

function _relation_symbol(op)
    op === (!=) && return Symbol("!=")
    op === (>) && return :>
    op === (>=) && return Symbol(">=")
    op === (<) && return :<
    op === (<=) && return Symbol("<=")
    throw(ArgumentError("unsupported domain relation: $op"))
end

# `x > 1`  ->  SymRelation(x - 1, :>)
function SymRelation(expr::Symbolics.Num)
    unwrapped = Symbolics.unwrap(expr)
    SymbolicUtils.iscall(unwrapped) ||
        throw(ArgumentError("a domain constraint must be a relation such as `x > 0`, got $expr"))
    lhs, rhs = SymbolicUtils.arguments(unwrapped)
    return SymRelation(wrap(lhs) - wrap(rhs), _relation_symbol(SymbolicUtils.operation(unwrapped)))
end

DomConstraint(relation::SymRelation) = DomConstraint(UNASSIGNED_ID, relation)
DomConstraint(expr::Symbolics.Num) = DomConstraint(SymRelation(expr))

# Accept raw relations (`x > 0`), SymRelations, or DomConstraints anywhere a
# constraint is expected.  Raw input gets `UNASSIGNED_ID`.
_as_constraint(c::DomConstraint) = c
_as_constraint(x) = DomConstraint(x)

_as_num(v) = v isa Symbolics.Num ? v : Symbolics.wrap(v)

constraint_variables(c::DomConstraint) =
    Symbolics.get_variables(Symbolics.unwrap(c.relation.residual))

# The hypersurface where the constraint is active (the "face" it bounds).
active_equation(c::DomConstraint) = Symbolics.Equation(c.relation.residual, 0)

_same_relation(a::DomConstraint, b::DomConstraint) =
    isequal(a.relation.residual, b.relation.residual) && a.relation.relation === b.relation.relation

# Canonical order inside a factor: by content, never by Id, so a domain does
# not depend on the order its constraints were supplied in.  The Id is only a
# final tie-break between constraints with identical content.
_content_key(c::DomConstraint) = (string(c.relation.residual), String(c.relation.relation))
_constraint_sort_key(c::DomConstraint) = (_content_key(c)..., c.id)

"""
    Paving(interior, boundary, roi, tolerance)

Branch-and-prune result for one domain factor: boxes certainly inside, and boxes
too small to classify (the boundary).  `roi` and `tolerance` record the global
settings it was computed with, so a paving made under other settings is
recomputed rather than reused.  Deliberately not parametrized: an empty paving
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

One factor of a domain: a set of variables together with the constraints that
couple them.  The domain is the Cartesian product of its factors.  A factor
stores only the *Ids* of its constraints; the constraint data lives once, in
`SymDomain.constraints`.  Consequently a factor says nothing about the content of
its constraints on its own (a rewrite can change that content while keeping the
Ids), so never cache anything keyed on a bare `DomBlock`.

Only `SymDomain`'s constructor creates these, and it establishes the invariants.

`variables` and `constraint_ids` are `const`: changing a factor's constraints means
building a new factor.  The one mutable field is `paving`, a lazily computed cache
that can be filled in on an existing factor (see `factor_paving!`) but never
describes anything but this factor's current, immutable content.  A factor object
may be shared by several domains; whoever builds a new domain must only reuse a
factor whose variables, Ids and constraint content are unchanged (`share_factors`
checks exactly that), so a stale paving can never be inherited.
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

`constraints` is the single source of truth: every constraint appears exactly
once, sorted by Id (so lookup by Id is a binary search).  `factors` partition
those constraints by Id.  Invariants, all enforced by the constructor:

- constraint Ids are unique and nonzero (negative Ids are *provisional*, see below);
- every constraint belongs to exactly one factor, and mentions only that factor's variables;
- factors have non-empty, pairwise-disjoint variable sets.

The stored form is canonical: variables inside a factor, constraints inside a
factor, and factors inside the domain are ordered by content, so the result does
not depend on input order.

Provisional Ids: constraints that arrive without an Id (`UNASSIGNED_ID`) are given
negative Ids `-1, -2, …` by canonical content order, so they can be referenced
inside the domain.  Provisional Ids are renumbered whenever the domain is rebuilt;
never keep one.  `assign_ids` swaps them for real Ids from a tree.
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
            # An already-canonical factor is kept as is (object and paving).  A
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

# Build from `key => constraints` pairs, one pair per factor.  Constraints may be
# raw relations, SymRelations or DomConstraints.
function SymDomain(pairs)
    factor_variables = Vector{Vector{Symbolics.Num}}()
    members = Vector{Vector{DomConstraint}}()
    for pair in pairs
        pair isa Pair || throw(ArgumentError("domain entries must be pairs of variables and constraints"))
        key, cs = pair
        (cs isa AbstractVector || cs isa Tuple) ||
            throw(ArgumentError("domain constraints must be stored in a vector or tuple"))
        key_variables = Symbolics.Num[_as_num(v) for v in (key isa Tuple ? key : (key,))]
        isempty(key_variables) && throw(ArgumentError("domain keys cannot be empty"))
        push!(factor_variables, key_variables)
        push!(members, DomConstraint[_as_constraint(c) for c in cs])
    end

    # Provisional Ids by canonical content order, independent of input order.
    pending = [(f, i) for f in eachindex(members) for i in eachindex(members[f]) if members[f][i].id <= 0]
    sort!(pending, by=fi -> _content_key(members[fi[1]][fi[2]]))
    for (rank, (f, i)) in enumerate(pending)
        members[f][i] = DomConstraint(-rank, members[f][i].relation)
    end

    constraints = DomConstraint[c for m in members for c in m]
    factors = DomBlock[
        DomBlock(Tuple(factor_variables[f]), Tuple(ConstraintId[c.id for c in members[f]]))
        for f in eachindex(members)]
    return SymDomain(constraints, factors)
end

"""All constraints, sorted by Id.  This is the single copy of the constraint data."""
all_constraints(domain::SymDomain) = domain.constraints
constraint_ids(domain::SymDomain) = ConstraintId[c.id for c in domain.constraints]

function find_constraint(domain::SymDomain, id::ConstraintId)
    i = _constraint_index(domain.constraints, id)
    return i == 0 ? nothing : domain.constraints[i]
end

# The factor's constraints, in the factor's canonical order (lazy: no allocation).
constraints_of(domain::SymDomain, factor::DomBlock) =
    (domain.constraints[_constraint_index(domain.constraints, id)] for id in factor.constraint_ids)

function factor_of(domain::SymDomain, variable)
    for factor in domain.factors
        _contains_equal(factor.variables, variable) && return factor
    end
    return nothing
end

function factor_of(domain::SymDomain, id::ConstraintId)
    for factor in domain.factors
        id in factor.constraint_ids && return factor
    end
    return nothing
end

"""
    assign_ids(domain, fresh_id)

Replace every provisional Id with an Id from the zero-argument function
`fresh_id` (e.g. `() -> next_constraint_id!(tree)`).  Constraints are visited in
canonical order, so the assignment does not depend on input order.  Constraints
with real Ids, and factors containing none, are left untouched (shared).
"""
function assign_ids(domain::SymDomain, fresh_id)
    any(c -> c.id < 0, domain.constraints) || return domain
    remap = Dict{ConstraintId,ConstraintId}()
    for factor in domain.factors, id in factor.constraint_ids
        id < 0 && (remap[id] = fresh_id())
    end
    constraints = DomConstraint[DomConstraint(get(remap, c.id, c.id), c.relation)
                                for c in domain.constraints]
    factors = DomBlock[
        any(<(0), f.constraint_ids) ?
        DomBlock(f.variables, map(id -> get(remap, id, id), f.constraint_ids), f.paving) : f
        for f in domain.factors]
    return SymDomain(constraints, factors)
end

# Structural equality: same factors, same constraints, Ids ignored.
_domain_structure(d::SymDomain) =
    [(map(string, f.variables), [(string(c.relation.residual), c.relation.relation) for c in constraints_of(d, f)])
     for f in d.factors]
same_domain(a::SymDomain, b::SymDomain) = _domain_structure(a) == _domain_structure(b)

function domain_product(domain1::SymDomain, domain2::SymDomain)
    isempty(intersect(domain1.variables, domain2.variables)) || throw(ArgumentError("domains must have different variables"))
    # the constructor re-sorts and rejects clashing constraint Ids
    return SymDomain(
        DomConstraint[domain1.constraints..., domain2.constraints...],
        DomBlock[domain1.factors..., domain2.factors...])
end

*(domain1::SymDomain, domain2::SymDomain) = domain_product(domain1, domain2)

# A domain iterates over its factors.
Base.length(domain::SymDomain) = length(domain.factors)
Base.getindex(domain::SymDomain, index::Int) = domain.factors[index]
Base.iterate(domain::SymDomain, state...) = iterate(domain.factors, state...)
Base.isempty(domain::SymDomain) = isempty(domain.factors)

# Compatibility view for code written against `key => constraints` pairs
# (add_constraints and friends).  Allocates; prefer `domain.factors` + `constraints_of`.
_domain_pairs(domain::SymDomain) = Pair[
    (length(f.variables) == 1 ? only(f.variables) : f.variables) => collect(DomConstraint, constraints_of(domain, f))
    for f in domain.factors]
_domain_pairs(domain) = domain

# Components are the connected groups represented by the domain keys. They are
# structural metadata only; integral factorization also requires a separable
# integrand and a product domain.
domain_variables(domain::SymDomain) = copy(domain.variables)
domain_components(domain::SymDomain) = collect(domain.factors)

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

function DESys(eqs, bcs, domain, ivs, dvs; ps=Symbolics.Num[], name=:system,
    restrictions=SymRelation[],
    history=DerivationHistory())
    normalized_ivs = Symbolics.Num[ivs...]
    normalized_dvs = Symbolics.Num[dvs...]
    normalized_ps = Symbolics.Num[ps...]
    normalized_eqs = Symbolics.Equation[eqs...]
    normalized_bcs = Symbolics.Equation[bcs...]
    normalized_domain = _as_domain(domain) # SymDomain, `key => constraints` pairs, or bare constraints
    normalized_restrictions = SymRelation[restrictions...]
    DESys(String(name), normalized_ivs, normalized_dvs, normalized_ps,
        normalized_eqs, normalized_bcs, normalized_domain,
        normalized_restrictions, history)
end

function DESys(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system,
    restrictions=SymRelation[], history=DerivationHistory())
    DESys(eqs, bcs, domain, ivs, dvs; ps=ps, name=name,
        restrictions=restrictions, history=history)
end

# needs to be redone to trace the history up the tree
_with_history(b::DESys, h::DerivationHistory) = DESys(
    eqs=b.eqs, ivs=b.ivs, dvs=b.dvs, ps=b.ps, bcs=b.bcs, domain=b.domain,
    name=b.name, restrictions=b.restrictions, history=h)

struct RootSys{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:Symbolics.Equation},B<:AbstractVector{<:Symbolics.Equation}}
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymDomain
end

function RootSys(DESys)
    ivs = tuple(DESys.ivs...)
    dvs = tuple(DESys.dvs...)
    ps = tuple(DESys.ps...)
    eqs = tuple(DESys.eqs...)
    bcs = tuple(DESys.bcs...)
    RootSys(ivs, dvs, ps, eqs, bcs, DESys.domain)
end

const NodeId = Int
abstract type Node end
abstract type Split end

struct RootNode <: Node
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

struct SolvedNode <: Node
    id::NodeId
    parent_id::NodeId
    solution::SolvedLeaf #needs to be defined
    history::XChain
end

struct SplitNode <: Node
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
    guard::Pair{SymbolicRestriction,NodeId}
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

Base.length(system::DiffEqSystem) = length(system.nodes)
Base.getindex(system::DiffEqSystem, index::Int) = system.nodes[index]

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

#=
the goal has changed, I've accepted I need a treelike structure.
rather than a DiffEqSystem wrapper type I should have a node struct. 
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