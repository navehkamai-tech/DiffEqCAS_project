function _get_relation(rel::SymRelation)
    relation = rel.relation
    relation === Symbol("!=") && return !=
    relation === :> && return >
    relation === Symbol(">=") && return >=
    relation === :< && return <
    relation === Symbol("<=") && return <=
    relation === Symbol("==") && return ==
end

function _eq_from_rel(rel::SymRelation)
    _get_relation(rel) !== (==) && return nothing
    return Symbolics.Equation(rel.residual, 0)
end

Symbolics.simplify(rel::SymRelation) = SymRelation(simplify(rel.residual), rel.relation)
Symbolics.expand(rel::SymRelation) = SymRelation(expand(rel.residual), rel.relation)

function _relation_symbol(op)
    op === (!=) && return Symbol("!=")
    op === (>) && return :>
    op === (>=) && return Symbol(">=")
    op === (<) && return :<
    op === (<=) && return Symbol("<=")
    op === (==) && return Symbol("==")
    throw(ArgumentError("unsupported domain relation: $op"))
end

# `x > 1`  ->  SymRelation(x - 1, :>)
function SymRelation(expr::Symbolics.Num)
    unwrapped = Symbolics.unwrap(expr)
    SU.iscall(unwrapped) ||
        throw(ArgumentError("a domain constraint must be a relation such as `x > 0`, got $expr"))
    lhs, rhs = SU.arguments(unwrapped)
    return SymRelation(wrap(lhs) - wrap(rhs), _relation_symbol(SU.operation(unwrapped)))
end

DomConstraint(relation::SymRelation) = DomConstraint(UNASSIGNED_ID, relation)
DomConstraint(expr::Symbolics.Num) = DomConstraint(SymRelation(expr))

# Accept raw relations (`x > 0`), SymRelations, or DomConstraints anywhere a
# constraint is expected. Raw input gets `UNASSIGNED_ID`.
_as_constraint(c::DomConstraint) = c
_as_constraint(x) = DomConstraint(x)
_as_num(v) = v isa Symbolics.Num ? v : Symbolics.wrap(v)

# The hypersurface where the constraint is active (the "face" it bounds).
active_equation(c::DomConstraint) = Symbolics.Equation(c.relation.residual, 0)

_same_relation(a::DomConstraint, b::DomConstraint) =
    isequal(a.relation.residual, b.relation.residual) && a.relation.relation === b.relation.relation

# Build from `key => constraints` pairs, one pair per factor. Constraints may be
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

"""All constraints, sorted by Id. This is the single copy of the constraint data."""
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
`fresh_id` (e.g. `() -> next_constraint_id!(tree)`). Constraints are visited in
canonical order, so the assignment does not depend on input order. Constraints
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
Base.:*(domain1::SymDomain, domain2::SymDomain) = domain_product(domain1, domain2)

# A domain iterates over its factors.
Base.length(domain::SymDomain) = length(domain.factors)
Base.getindex(domain::SymDomain, index::Int) = domain.factors[index]
Base.iterate(domain::SymDomain, state...) = iterate(domain.factors, state...)
Base.isempty(domain::SymDomain) = isempty(domain.factors)

# Compatibility view for code written against `key => constraints` pairs
# (add_constraints and friends). Allocates; prefer `domain.factors` + `constraints_of`.
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
    # the SymDomain constructor canonicalizes on its own
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
split components). This is what keeps boundary-condition references valid
through coordinate transforms and simplification.
"""
function rewrite_constraints(f, domain::SymDomain, ivs=nothing)
    rewritten = DomConstraint[DomConstraint(c.id, f(c.relation)) for c in all_constraints(domain)]
    return share_factors(add_constraints(SymDomain(Pair[]), rewritten, ivs), domain)
end

# ---------------------------------------------------------------------------
# Building domains and sub-domains
# ---------------------------------------------------------------------------
"""
    domain_from_constraints(constraints; variables=(), fresh_id=nothing)

Build a domain from bare constraints (`x > 0`, `x^2 + y^2 < 1`, SymRelations or
DomConstraints); the factors are found automatically as the connected groups of
variables. `variables` declares variables that have no constraint at all (an
unbounded factor). Without `fresh_id` the constraints carry provisional Ids;
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

The product of just the given factors of `domain`. The factor objects are
shared, so their pavings come along.
"""
function subdomain(domain::SymDomain, factors)
    constraints = DomConstraint[c for f in factors for c in constraints_of(domain, f)]
    return SymDomain(constraints, collect(DomBlock, factors))
end

"""
    share_factors(new, old)

Replace each factor of `new` by the factor of `old` that has the same
variables, the same constraint Ids *and* the same constraint content, if there
is one. Sharing keeps the cached paving and means a paving computed later is
seen by both domains.
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
constraint expressions, no Ids and no pavings.
"""
factors_content_key(domain::SymDomain, factors) = Tuple(
    (Tuple(Symbolics.unwrap(v) for v in f.variables),
        Tuple((Symbolics.unwrap(c.relation.residual), c.relation.relation) for c in constraints_of(domain, f)))
    for f in factors)

# ---------------------------------------------------------------------------
# Domain rewriting
# ---------------------------------------------------------------------------
# Variables a factor's variables turn into under `mapping`.
function _mapped_factor_variables(factor::DomBlock, mapping)
    variables = Any[]
    for variable in factor.variables
        mapped = haskey(mapping, variable) ? substitute(variable, mapping) : variable
        for mapped_variable in Symbolics.get_variables(unwrap(mapped))
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
  transformation.
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

# Transform domain constraints under an independent-variable change. Only
# factors containing a mapped variable are rewritten.
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
