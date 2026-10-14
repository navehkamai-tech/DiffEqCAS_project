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
    _get_relation(rel) !== (==) && return nothing
    return Symbolics.Equation(rel.residual, 0)
end

Symbolics.simplify(rel::SymRelation) = SymRelation(simplify(rel.residual), rel.relation)
Symbolics.expand(rel::SymRelation) = SymRelation(expand(rel.residual), rel.relation)


# `x > 1`  ->  SymRelation(x - 1, :>)
function SymRelation(expr::Symbolics.Num)
    unwrapped = Symbolics.unwrap(expr)
    SU.iscall(unwrapped) ||
        throw(ArgumentError("a domain constraint must be a relation such as `x > 0`, got $expr"))
    lhs, rhs = SU.arguments(unwrapped)
    return SymRelation(wrap(lhs) - wrap(rhs), _relation_symbol(SU.operation(unwrapped)))
end

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

One factor (i.e. 'Block') of a domain: a set of variables together with the constraints that
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

function _record_variables!(variables, seen, key_variables)
    for variable in key_variables
        if !_contains_equal(seen, variable)
            push!(seen, variable)
            push!(variables, variable)
        end
    end
end

function _merge_domain_group!(
    groups::AbstractVector,
    key_set,
    constraints,
)
    intersecting = findall(i -> !isdisjoint(groups[i][1], key_set), eachindex(groups))
    if isempty(intersecting)
        push!(groups, (key_set, collect(Any, constraints)))
        return
    end

    first_group = first(intersecting)
    union!(groups[first_group][1], key_set)
    append!(groups[first_group][2], constraints)
    for i in reverse(intersecting[2:end])
        union!(groups[first_group][1], groups[i][1])
        append!(groups[first_group][2], groups[i][2])
        deleteat!(groups, i)
    end
end

# Canonicalize domain keys while preserving either the supplied IV order or
# the first-seen order of the domain keys when no IV order is available.
function _canonicalize_domain_pairs(domain_pairs, ivs=nothing)
    #the SymDomain constructor canonicalizes on it's own
    if domain_pairs isa SymDomain
        return domain_pairs
    end
    domain_pairs = _domain_pairs(domain_pairs)
    variables = ivs === nothing ? Any[] : sort(ivs, by=string)
    seen = ivs === nothing ? Set{Any}() : nothing
    groups = Vector{Tuple{Set{Any},Vector{Any}}}()

    for (key, constraints) in domain_pairs
        key_variables = _key_variables(key)
        ivs === nothing && _record_variables!(variables, seen, key_variables)
        _merge_domain_group!(groups, Set(key_variables), constraints)
    end

    result = Pair[]
    for (variable_set, constraints) in groups
        ordered_variables = [v for v in variables if _contains_equal(variable_set, v)]
        key = length(ordered_variables) == 1 ? only(ordered_variables) : Tuple(ordered_variables)
        push!(result, key => constraints)
    end
    return result
end

function _domain_variables(domain_pairs)
    domain_pairs = _domain_pairs(domain_pairs)
    variables = Any[]
    for (key, _) in domain_pairs
        append!(variables, _key_variables(key))
    end
    return variables
end

function _intersecting_group_indices(groups, variables)
    return findall(group -> !isdisjoint(group[1], variables), groups)
end

# Merge a new constraint into every existing group that shares one of its
# variables; this preserves connected domain components.
function _add_constraint!(
    groups::AbstractVector{<:Tuple{<:Set,Vector{Any}}},
    constraint::DomConstraint,
)
    new_variables = Set(constraint_variables(constraint))
    intersecting = _intersecting_group_indices(groups, new_variables)
    if isempty(intersecting)
        push!(groups, (new_variables, Any[constraint]))
        return groups
    end

    first_group = first(intersecting)
    union!(groups[first_group][1], new_variables)
    push!(groups[first_group][2], constraint)
    for i in reverse(intersecting[2:end])
        union!(groups[first_group][1], groups[i][1])
        append!(groups[first_group][2], groups[i][2])
        deleteat!(groups, i)
    end
    return groups
end

function _validate_iv_order!(variable_order, domain_pairs)
    for variable in _domain_variables(domain_pairs)
        if !_contains_equal(variable_order, variable)
            throw(ArgumentError("domain variable is absent from ivs"))
        end
    end
end

function _add_constraint_variables!(variable_order, constraint::DomConstraint, ivs)
    for variable in constraint_variables(constraint)
        if !_contains_equal(variable_order, variable)
            ivs === nothing && push!(variable_order, variable)
            ivs !== nothing && throw(ArgumentError("constraint variable is absent from ivs"))
        end
    end
end

function _ordered_group_variables(variable_set, variable_order)
    return [variable for variable in variable_order if _contains_equal(variable_set, variable)]
end

function _group_order_index(group, variable_order)
    return findfirst(variable -> _contains_equal(group[1], variable), variable_order)
end

# Add constraints to an already-canonical domain. If `ivs` is provided, it
# controls both the order inside tuple keys and the order of the output groups.
function add_constraints(
    domain_pairs,
    new_constraints::Union{AbstractVector,Tuple},
    ivs=nothing,
)
    original = domain_pairs isa SymDomain ? domain_pairs : nothing
    domain_pairs = _domain_pairs(domain_pairs)
    variable_order = ivs === nothing ? _domain_variables(domain_pairs) : collect(ivs)
    ivs !== nothing && _validate_iv_order!(variable_order, domain_pairs)
    groups = [(Set(_key_variables(key)), Any[_as_constraint(c) for c in constraints])
              for (key, constraints) in domain_pairs]

    for raw in new_constraints
        constraint = _as_constraint(raw)
        isempty(constraint_variables(constraint)) &&
            throw(ArgumentError("a domain constraint must mention at least one variable: $(constraint.relation.residual)"))
        # A new, unassigned constraint identical to one already present adds
        # nothing; the existing constraint (and its Id) is kept.
        constraint.id == UNASSIGNED_ID &&
            any(g -> any(existing -> _same_relation(existing, constraint), g[2]), groups) &&
            continue
        _add_constraint_variables!(variable_order, constraint, ivs)
        _add_constraint!(groups, constraint)
    end

    if ivs !== nothing
        sort!(groups, by=group -> _group_order_index(group, variable_order))
    end

    final_pairs = Pair[]
    for (variable_set, constraints) in groups
        ordered_variables = _ordered_group_variables(variable_set, variable_order)
        new_key = length(ordered_variables) == 1 ? only(ordered_variables) : Tuple(ordered_variables)
        push!(final_pairs, new_key => constraints)
    end
    result = SymDomain(final_pairs) # variables are derived by the constructor
    # Factors the new constraints did not touch are the old factor objects again,
    # which keeps their pavings (and shares them with the domain we started from).
    return original === nothing ? result : share_factors(result, original)
end

add_constraints(domain_pairs, constraint::Union{Symbolics.Num,SymRelation,DomConstraint}, ivs=nothing) =
    add_constraints(domain_pairs, (constraint,), ivs)

"""
    rewrite_constraints(f, domain, ivs=nothing)

Apply `f(::SymRelation) -> SymRelation` to every constraint, keeping each
constraint's Id, and regroup the result (a change of variables can merge or
split components).  This is what keeps boundary-condition references valid
through coordinate transforms and simplification.
"""
function rewrite_constraints(f, domain::SymDomain, ivs=nothing)
    rewritten = DomConstraint[DomConstraint(c.id, f(c.relation)) for c in all_constraints(domain)]
    return share_factors(add_constraints(SymDomain(Pair[]), rewritten, ivs), domain)
end

const ROI = Ref{Float64}(1000.0)
const tolerance = Ref{Float64}(0.01)
#=
this is how to Change the global bound for this session
DiffEqCAS.ROI[] = 50000.0
=#

#helper for constraints_to_domain
function shrink_bounds!(bounds, constraint::DomConstraint)
    vars = constraint_variables(constraint)
    if !(length(vars)==1)
        return bounds
    end
    var=vars[1]
    expr = simplify(Symbolics.unwrap(constraint.relation.residual))
    if !isequal(Symbolics.degree(expr, var), 1)
        return bounds
    end
    op = _get_relation(constraint.relation)
    coeff = Symbolics.coeff(expr, var)
    coeff_value = SU.unwrap_const(Symbolics.unwrap(coeff))
    coeff_value isa Real || return bounds
    num = SU.unwrap_const(Symbolics.unwrap(substitute(expr, var => 0) / coeff))
    num isa Real || return bounds
    if (((op === <) || (op === ≤)) && (coeff_value > 0)) ||
        (((op === >) || (op === ≥)) && (coeff_value < 0))
        bounds[var][2] = min(-num, bounds[var][2])
    elseif (((op === <) || (op === ≤)) && (coeff_value < 0)) ||
        (((op === >) || (op === ≥)) && (coeff_value > 0))
        bounds[var][1] = max(-num, bounds[var][1])
    end
    return bounds
end

function _domain_interval_value(expr, variables, box)
    unwrapped = Symbolics.unwrap(expr)
    literal = SU.unwrap_const(unwrapped)
    literal isa Real && return bareinterval(literal)
    for (index, variable) in pairs(variables)
        isequal(unwrapped, Symbolics.unwrap(variable)) &&
            return box[index]
    end
    SU.iscall(unwrapped) || return interval(-Inf, Inf)
    op = SU.operation(unwrapped)
    args = SU.arguments(unwrapped)
    values = [_domain_interval_value(arg, variables, box) for arg in args]
    if op === (+)
        return sum(values)
    elseif op === (-)
        return length(values) == 1 ? -values[1] : values[1] - values[2]
    elseif op === (*)
        return prod(values)
    elseif op === (/)
        return values[1] / values[2]
    elseif op === (^)
        return values[1] ^ values[2]
    elseif op === abs
        return abs(values[1])
    elseif op === exp
        return exp(values[1])
    elseif op === log
        return log(values[1])
    elseif op === sin
        return sin(values[1])
    elseif op === cos
        return cos(values[1])
    end
    return interval(-Inf, Inf)
end

function _domain_relation_status(constraint::DomConstraint, variables, box)
    op = _get_relation(constraint.relation)
    value = _domain_interval_value(constraint.relation.residual, variables, box)
    lower, upper = inf(value), sup(value)
    if op === (<)
        return upper < 0 ? :inside : lower >= 0 ? :outside : :unknown
    elseif op === (≤)
        return upper <= 0 ? :inside : lower > 0 ? :outside : :unknown
    elseif op === (>)
        return lower > 0 ? :inside : upper <= 0 ? :outside : :unknown
    elseif op === (≥)
        return lower >= 0 ? :inside : upper < 0 ? :outside : :unknown
    elseif op === (==)
        return lower == 0 && upper == 0 ? :inside :
               (upper < 0 || lower > 0) ? :outside : :unknown
    end
    return (upper < 0 || lower > 0) ? :inside :
           (lower == 0 && upper == 0) ? :outside : :unknown
end

"""
custom implimentation of intervalbox branch and prune algorithm similar to IntervalConstraintProgramming.pave
FUTURE DEVELOPMENT: add constraint propogation logic like in IntervalConstraintProgramming.pave
"""
function _pave_constraints(box, constraints, variables, epsilon)
    working = [box]
    inner = typeof(box)[]
    boundary = typeof(box)[]
    while !isempty(working)
        current = pop!(working)
        isempty(current) && continue
        statuses = [_domain_relation_status(c, variables, current) for c in constraints]
        any(isequal(:outside), statuses) && continue
        if all(isequal(:inside), statuses)
            push!(inner, current)
        elseif diam(current) < epsilon
            push!(boundary, current)
        else
            append!(working, bisect(current))
        end
    end
    return inner, boundary
end

# Pave one factor: the box search only ever sees that factor's variables, so
# the cost is exponential in the factor's dimension, not the domain's.
function _pave_factor(domain::SymDomain, factor::DomBlock)
    variables = collect(factor.variables)
    bounds = Dict{Any,Vector{Float64}}(v => [-ROI[], ROI[]] for v in variables)
    collected_constraints = DomConstraint[]
    for c in constraints_of(domain, factor)
        push!(collected_constraints, c)
        shrink_bounds!(bounds, c)
    end
    any(bounds[v][1] > bounds[v][2] for v in variables) &&
        return (IntervalBox[], IntervalBox[])
    intervals = [bareinterval(bounds[v][1], bounds[v][2]) for v in variables]
    box = IntervalBox(intervals...)
    return _pave_constraints(box, collected_constraints, variables, tolerance[])
end

"""
    factor_paving!(domain, factor)

The factor's paving, computed on first use and stored on the factor.  `factor`
must belong to `domain`.  A stored paving made under different `ROI`/`tolerance`
settings is recomputed.
"""
function factor_paving!(domain::SymDomain, factor::DomBlock)
    paving = factor.paving
    if paving === nothing || paving.roi < ROI[] || paving.tolerance > tolerance[]
        inner, boundary = _pave_factor(domain, factor)
        paving = Paving(inner, boundary, ROI[], tolerance[])
        factor.paving = paving
    end
    return paving
end

"""
    domain_pavings(domain)

One `Paving` per factor, in factor order, computed lazily and cached on the
factors.  The domain is the product of these, which is never expanded:
membership and feasibility are answered factor by factor.
"""
domain_pavings(domain::SymDomain) = Paving[factor_paving!(domain, f) for f in domain.factors]

constraints_to_domain(domain::SymDomain) = isempty(domain) ? nothing : domain_pavings(domain)
# raw `key => constraints` pairs (disjoint keys)
constraints_to_domain(domain_pairs) = constraints_to_domain(add_constraints(domain_pairs, ()))

# `coord` is ordered like `domain.variables`; each factor sees only its slice.
function _in_pavings(coord, domain::SymDomain, pavings, include_boundary::Bool)
    length(coord) == length(domain.variables) ||
        throw(DimensionMismatch("coords must have the same dimension as domain"))
    offset = 0
    for (factor, paving) in zip(domain.factors, pavings)
        n = length(factor.variables)
        sub = StaticArrays.SVector{n}(ntuple(i -> coord[offset+i], n))
        offset += n
        any(sub ∈ box for box in paving.interior) && continue
        include_boundary && any(sub ∈ box for box in paving.boundary) && continue
        return false
    end
    return true
end

function is_in_domain(coord::StaticArrays.SVector, domain::SymDomain, include_boundary::Bool=true)
    isempty(domain) && return false
    return _in_pavings(coord, domain, domain_pavings(domain), include_boundary)
end

# raw `key => constraints` pairs
is_in_domain(coord::StaticArrays.SVector, domain_constraints::AbstractVector, include_boundary::Bool=true) =
    is_in_domain(coord, add_constraints(domain_constraints, ()), include_boundary)

# ---------------------------------------------------------------------------
# Building domains and sub-domains
# ---------------------------------------------------------------------------

"""
    domain_from_constraints(constraints; variables=(), fresh_id=nothing)

Build a domain from bare constraints (`x > 0`, `x^2 + y^2 < 1`, SymRelations or
DomConstraints); the factors are found automatically as the connected groups
of variables.  `variables` declares variables that have no constraint at all
(an unbounded factor).  Without `fresh_id` the constraints carry provisional Ids;
pass e.g. `() -> next_constraint_id!(tree)` to register them right away.
"""
function domain_from_constraints(constraints; variables=(), fresh_id=nothing)
    declared = Pair[]
    seen = Symbolics.Num[]
    for v in variables
        n = _as_num(v)
        any(isequal(n), seen) && continue
        push!(seen, n)
        push!(declared, n => DomConstraint[])
    end
    domain = add_constraints(SymDomain(declared), constraints)
    return fresh_id === nothing ? domain : assign_ids(domain, fresh_id)
end

# What `DESys(domain=...)` accepts: a SymDomain, `key => constraints` pairs,
# or bare constraints.
_as_domain(domain::SymDomain) = domain
function _as_domain(x)
    items = x isa Union{Tuple,AbstractVector} ? x : (x,)
    isempty(items) && return SymDomain(Pair[])
    all(item -> item isa Pair, items) && return SymDomain(items)
    any(item -> item isa Pair, items) &&
        throw(ArgumentError("a domain is either `key => constraints` pairs or bare constraints, not a mix"))
    return domain_from_constraints(items)
end

"""
    subdomain(domain, factors)

The product of just the given factors of `domain`.  The factor objects are
shared, so their pavings come along.
"""
function subdomain(domain::SymDomain, factors)
    constraints = DomConstraint[c for f in factors for c in constraints_of(domain, f)]
    return SymDomain(constraints, collect(DomBlock, factors))
end

"""
    share_factors(new, old)

Replace each factor of `new` by the factor of `old` that has the same variables,
the same constraint Ids *and* the same constraint content, if there is one.
Sharing keeps the cached paving and means a paving computed later is seen by both
domains.  Because content is compared, a factor whose constraints were rewritten
can never inherit a paving, which makes this the one place that decides whether a
paving survives a domain rebuild.
"""
function share_factors(new::SymDomain, old::SymDomain)
    isempty(old.factors) && return new
    shared = DomBlock[_matching_factor(new, f, old) for f in new.factors]
    all(i -> shared[i] === new.factors[i], eachindex(shared)) && return new
    return SymDomain(collect(DomConstraint, new.constraints), shared)
end

function _matching_factor(new::SymDomain, f::DomBlock, old::SymDomain)
    for g in old.factors
        length(g.variables) == length(f.variables) || continue
        g.constraint_ids == f.constraint_ids || continue
        all(isequal(a, b) for (a, b) in zip(g.variables, f.variables)) || continue
        all(_same_relation(find_constraint(old, id), find_constraint(new, id))
            for id in f.constraint_ids) || continue
        return g
    end
    return f
end

"""
    factors_content_key(domain, factors)

A hashable key describing the given factors by content only: variables and
constraint expressions, no Ids and no pavings.  Two domains with equal keys
describe the same set, and any change to a constraint changes the key, so caches
keyed on it never need explicit invalidation.
"""
factors_content_key(domain::SymDomain, factors) = Tuple(
    (Tuple(Symbolics.unwrap(v) for v in f.variables),
        Tuple((Symbolics.unwrap(c.relation.residual), c.relation.relation) for c in constraints_of(domain, f)))
    for f in factors)

"""
    constraints_satisfiable(constraints, domain, include_boundary=true)

Check whether `constraints` can be added to `domain` without emptying it.  Only
the factors the new constraints touch are re-paved; untouched factors are
unchanged by definition.  The existing `domain` is assumed to be feasible
already, so this answers "is the addition compatible", not "is the whole domain
non-empty".
"""
function constraints_satisfiable(
    constraints,
    domain,
    include_boundary::Bool=true,
)
    new_constraints = constraints isa AbstractVector || constraints isa Tuple ?
                      constraints : (constraints,)
    combined = add_constraints(domain, new_constraints)
    touched = Any[]
    for raw in new_constraints
        append!(touched, constraint_variables(_as_constraint(raw)))
    end
    for factor in combined.factors
        any(v -> _contains_equal(factor.variables, v), touched) || continue
        inner, boundary = _pave_factor(combined, factor)
        feasible = include_boundary ? (!isempty(inner) || !isempty(boundary)) : !isempty(inner)
        feasible || return false
    end
    return true
end

# ---------------------------------------------------------------------------
# Domain rewriting
#
# A transformation rewrites the constraints of the factors it touches; the
# factors it does not touch are left alone.  The result is rebuilt from the
# rewritten constraints (a coordinate change can merge or split factors), and
# then `share_factors` hands every factor whose variables, Ids and constraint
# content came out unchanged its old factor object back, paving included.  A
# factor that was really rewritten therefore starts with no paving, and an
# untouched one keeps the one it had.  Nothing here ever copies a paving by hand.
# ---------------------------------------------------------------------------

# Variables a factor's variables turn into under `mapping`.
function _mapped_factor_variables(factor::DomBlock, mapping)
    variables = Any[]
    for variable in factor.variables
        mapped = haskey(mapping, variable) ? substitute(variable, mapping) : variable
        for mapped_variable in Symbolics.get_variables(Symbolics.unwrap(mapped))
            push!(variables, mapped_variable)
        end
    end
    return _ordered_unique(variables)
end

"""
    _rebuild_domain(domain, touched, rewrite, mapped_variables)

* `touched(factor)`: does the transformation affect this factor?
* `rewrite(relation)`: the transformed `SymRelation` (Ids are preserved).
* `mapped_variables(factor)`: the variables of a touched factor after the
  transformation.  Only used when the rewritten constraints mention no variable
  at all (an unconstrained factor, or a degenerate mapping): there is then
  nothing to regroup by, so the mapped variables become the factor's key.
  Otherwise factors are re-derived from the rewritten constraints, which lets
  coupled constraints collapse when a coordinate becomes redundant, e.g.
  x^2 + y^2 < 1 becoming r^2 < 1 under polar coordinates.
"""
function _rebuild_domain(domain::SymDomain, touched, rewrite, mapped_variables)
    declared = Pair[]
    constraints = DomConstraint[]
    for factor in domain.factors
        is_touched = touched(factor)
        members = DomConstraint[constraints_of(domain, factor)...]
        is_touched && (members = DomConstraint[DomConstraint(c.id, rewrite(c.relation)) for c in members])

        if any(c -> !isempty(constraint_variables(c)), members)
            append!(constraints, members)
        else
            variables = is_touched ? mapped_variables(factor) : collect(factor.variables)
            push!(declared, (length(variables) == 1 ? only(variables) : Tuple(variables)) => members)
        end
    end
    rebuilt = add_constraints(SymDomain(declared), constraints)
    return share_factors(rebuilt, domain)
end

# Transform domain constraints under an independent-variable change.  Only
# factors containing a mapped variable are rewritten.  `ivs` is accepted for
# compatibility; the stored form is canonical and does not depend on it.
function transform_domains(domain::SymDomain, iv_mapping::Dict, ivs=nothing)
    _rebuild_domain(
        domain,
        factor -> any(variable -> haskey(iv_mapping, variable), factor.variables),
        relation -> SymRelation(simplify(substitute(relation.residual, iv_mapping)), relation.relation),
        factor -> _mapped_factor_variables(factor, iv_mapping))
end

# Same for a parameter change: constraints such as `x < a` change when `a` does.
function transform_domain_parameters(domain::SymDomain, param_mapping::Dict)
    _rebuild_domain(
        domain,
        factor -> any(variable -> haskey(param_mapping, variable), factor.variables),
        relation -> SymRelation(simplify(substitute(relation.residual, param_mapping)), relation.relation),
        factor -> _mapped_factor_variables(factor, param_mapping))
end
