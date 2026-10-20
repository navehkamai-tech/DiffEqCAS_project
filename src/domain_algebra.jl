
# Accept raw relations (`x > 0`), SymRelations, or DomConstraints anywhere a
# constraint is expected. Raw input gets `UNASSIGNED_ID`.
_as_constraint(c::DomConstraint) = c
_as_constraint(x) = DomConstraint(x)
_as_num(v) = v isa Symbolics.Num ? v : Symbolics.wrap(v)

# The hypersurface where the constraint is active (the "face" it bounds).
active_equation(c::DomConstraint) = Symbolics.Equation(c.relation.residual, 0)

# should be updated to be more sophisticated, OR should canonicalize constraints
_same_relation(a::DomConstraint, b::DomConstraint) =
    isequal(a.relation.residual, b.relation.residual) && a.relation.relation === b.relation.relation

# Validated and canonicalizing constructor from constraints.
function SymDomain(constraints::AbstractVector{DomConstraint}, blocks::AbstractVector{DomBlock})
    sorted = sort(collect(DomConstraint, constraints), by=c -> c.id)
    unique!(c->c.id, sorted)

    claimed = falses(length(sorted))
    seen_variables = Symbolics.Num[]
    canonical = DomBlock[]

    for block in blocks
        variables = Symbolics.Num[]
        for v in block.variables
            any(isequal(v), variables) || push!(variables, v)
        end
        isempty(variables) && throw(ArgumentError("domain blocks cannot be empty"))
        for v in variables
            any(isequal(v), seen_variables) &&
                throw(ArgumentError("variable $v appears in more than one domain block"))
            push!(seen_variables, v)
        end
        sort!(variables, by=string)

        for id in block.constraint_ids
            i = _constraint_index(sorted, id)
            i == 0 && throw(ArgumentError("block refers to unknown constraint id $id"))
            claimed[i] && throw(ArgumentError("constraint $id belongs to more than one block"))
            claimed[i] = true
            for v in constraint_variables(sorted[i])
                _contains_equal(variables, v) ||
                    throw(ArgumentError("constraint $id references variable$v outside its block"))
            end
        end

        members = ConstraintId[id for id in block.constraint_ids]
        sort!(members, by=id -> _constraint_sort_key(sorted[_constraint_index(sorted, id)]))

        # An already-canonical block is kept as is (object and paving). A
        # re-ordered one gets a new object with no paving: the paving's box
        # coordinates follow `variables`, so it would no longer line up.
        is_canonical = length(block.variables) == length(variables) &&
            all(isequal(a, b) for (a, b) in zip(block.variables, variables)) &&
            block.constraint_ids == members
        push!(canonical, is_canonical ? block : DomBlock(variables, members))
    end

    all(claimed) || throw(ArgumentError("every constraint must belong to a block"))
    sort!(canonical, by=b -> string(b.variables[begin]))
    all_variables = Symbolics.Num[v for b in canonical for v in b.variables]
    return _unchecked_domain(sorted, canonical, all_variables)
end

"""All constraints, sorted by Id. This is the single copy of the constraint data."""
all_constraints(domain::SymDomain) = domain.constraints

constraint_ids(domain::SymDomain) = ConstraintId[c.id for c in domain.constraints]

function find_constraint(domain::SymDomain, id::ConstraintId)
    i = _constraint_index(domain.constraints, id)
    return i == 0 ? nothing : domain.constraints[i]
end

# The block's constraints, in the block's canonical order (lazy: no allocation).
constraints_of(domain::SymDomain, block::DomBlock) =
    (domain.constraints[_constraint_index(domain.constraints, id)] for id in block.constraint_ids)

# ---------------------------------------------------------------------------
# 2. Fast Single-Block Satisfiability Check (No Recursion into add_constraints)
# ---------------------------------------------------------------------------
function _prune_block_constraints(
    variables::Vector{Symbolics.Num},
    constraints::Vector{DomConstraint},
    new_ids::Set{ConstraintId};
    throw_on_infeasible::Bool=true,
)
    # Pass 1: Collapse constraints sharing the exact same canonical residual
    deduped = DomConstraint[]
    for c in constraints
        idx = findfirst(existing -> isequal(existing.relation.residual, c.relation.residual), deduped)
        if idx === nothing
            push!(deduped, c)
        else
            existing = deduped[idx]
            combined_mask = _rel_mask(existing.relation.relation) & _rel_mask(c.relation.relation)
            if combined_mask == 0x00
                throw_on_infeasible || return nothing
                throw(DomainError(c.relation.residual, "contradictory domain constraints: $(existing.relation) and $(c.relation)"))
            end
            if combined_mask == _rel_mask(existing.relation.relation)
                continue
            elseif combined_mask == _rel_mask(c.relation.relation)
                keep_id = existing.id in new_ids ? c.id : existing.id
                deduped[idx] = DomConstraint(keep_id, c.relation)
                push!(new_ids, keep_id)
            else
                merged_rel = SymRelation(existing.relation.residual, _mask_to_rel(combined_mask))
                deduped[idx] = DomConstraint(existing.id, merged_rel)
                push!(new_ids, existing.id)
            end
        end
    end

    length(deduped) == 0 && return deduped

    # Pass 2: Check each new constraint against the remaining constraints using `relation_status`
    active = copy(deduped)
    i = 1
    while i <= length(active)
        c = active[i]
        if c.id in new_ids
            others = [active[j] for j in eachindex(active) if j != i]
            if isempty(others)
                unconstrained_dom = _unchecked_domain(DomConstraint[], [DomBlock(variables, ConstraintId[])], variables)
                status = relation_status(c.relation, unconstrained_dom)
                if status === :infeasible
                    throw_on_infeasible || return nothing
                    throw(DomainError(c.relation, "infeasible constraint: $(c.relation)"))
                elseif status === :redundant
                    deleteat!(active, i)
                    continue
                end
            else
                other_dom = SymDomain(others, [DomBlock(variables, ConstraintId[o.id for o in others])])
                status = relation_status(c.relation, other_dom)
                if status === :infeasible
                    throw_on_infeasible || return nothing
                    throw(DomainError(c.relation, "constraint $(c.relation) is infeasible on domain"))
                elseif status === :redundant
                    deleteat!(active, i)
                    continue
                end
            end
        end
        i += 1
    end

    # Pass 3: Backward check on old constraints (did a surviving new constraint make an old one redundant?)
    if any(c -> c.id in new_ids, active) && length(active) > 1
        i = 1
        while i <= length(active)
            c = active[i]
            if !(c.id in new_ids)
                others = [active[j] for j in eachindex(active) if j != i]
                other_dom = SymDomain(others, [DomBlock(variables, ConstraintId[o.id for o in others])])
                if relation_status(c.relation, other_dom) === :redundant
                    deleteat!(active, i)
                    continue
                end
            end
            i += 1
        end
    end

    return active
end

function block_of(domain::SymDomain, variable)
    for block in domain.blocks
        _contains_equal(block.variables, variable) && return block
    end
    return nothing
end

function block_of(domain::SymDomain, id::ConstraintId)
    for block in domain.blocks
        id in block.constraint_ids && return block
    end
    return nothing
end

# Structural equality: same blocks, same constraints, Ids ignored.
_domain_structure(d::SymDomain) =
    [(map(string, b.variables), [(string(c.relation.residual), c.relation.relation) for c in constraints_of(d, b)])
     for b in d.blocks]
same_domain(a::SymDomain, b::SymDomain) = _domain_structure(a) == _domain_structure(b)

function domain_product(domain1::SymDomain, domain2::SymDomain)
    isempty(intersect(domain1.variables, domain2.variables)) || throw(ArgumentError("domains must have different variables"))
    # the constructor re-sorts and rejects clashing constraint Ids
    return SymDomain(
        DomConstraint[domain1.constraints..., domain2.constraints...],
        DomBlock[domain1.blocks..., domain2.blocks...])
end
Base.:*(domain1::SymDomain, domain2::SymDomain) = domain_product(domain1, domain2)

# A domain iterates over its blocks.
Base.length(domain::SymDomain) = length(domain.blocks)
Base.getindex(domain::SymDomain, index::Int) = domain.blocks[index]
Base.iterate(domain::SymDomain, state...) = iterate(domain.blocks, state...)
Base.isempty(domain::SymDomain) = isempty(domain.blocks)

# Components are the connected groups represented by the domain keys. They are
# structural metadata only; integral factorization also requires a separable
# integrand and a product domain.
domain_variables(domain::SymDomain) = copy(domain.variables)
domain_components(domain::SymDomain) = copy(domain.blocks)

# Returns :true (tautology, drop), :false (contradiction, infeasible), or :parameter (keep in restrictions)
function _classify_non_iv_relation(rel::SymRelation)
    val = SU.unwrap_const(Symbolics.unwrap(rel.residual))
    if val isa Real
        op = _get_relation(rel)
        return op(val, 0) ? :true : :false
    end
    # Has symbolic parameters/constants but no ivs
    ev = _infer_tree(rel.residual, EvidenceDomain(_unchecked_domain(DomConstraint[]), DomBlock[], (), nothing))
    lo, hi = inf(ev.bound), sup(ev.bound)
    op = _get_relation(rel)
    if (op === (>) && lo > 0) || (op === (>=) && lo >= 0) || (op === (<) && hi < 0) || (op === (<=) && hi <= 0) || (op === (==) && lo == 0 && hi == 0) || (op === (!=) && (lo > 0 || hi < 0))
        return :true
    elseif (op === (>) && hi <= 0) || (op === (>=) && hi < 0) || (op === (<) && lo >= 0) || (op === (<=) && lo > 0) || (op === (==) && (lo > 0 || hi < 0)) || (op === (!=) && lo == 0 && hi == 0)
        return :false
    end
    return :possible
end

# Add constraints to an already-canonical domain. If `ivs` is provided, it
# controls both the order inside tuple keys and the order of the output groups.
function add_constraints(
    domain_input,
    new_constraints::Union{AbstractVector,Tuple},
    ivs=nothing;
    prune_redundant::Bool=true,
    throw_on_infeasible::Bool=true,
)
    original = domain_input isa SymDomain ? domain_input : SymDomain(domain_input)
    isempty(new_constraints) && return original

    # Start with existing blocks as mutable groups: (vars_vec, constraints_vec, touched_flag)
    groups = Vector{Tuple{Vector{Symbolics.Num},Vector{DomConstraint},Bool}}()
    for block in original.blocks
        push!(groups, (copy(block.variables), collect(DomConstraint, constraints_of(original, block)), false))
    end

    new_ids = Set{ConstraintId}()

    for raw in new_constraints
        constraint = _as_constraint(raw)
        c_vars = Symbolics.Num[_as_num(v) for v in constraint_variables(constraint)]
        if isempty(c_vars) || (ivs !== nothing && !any(v -> _contains_equal(ivs, v), c_vars))
            class = _classify_non_iv_relation(constraint.relation)
            class === :true && continue
            class === :false && (throw_on_infeasible ? throw(DomainError("infeasible domain")) : return nothing)
            class === :possible #need to somehow store parameter info
        end
        for v in c_vars
            (_contains_equal(ivs, v) && ivs !== nothing) || throw(ArgumentError("constraint variable $v is absent from ivs"))
        end


        push!(new_ids, constraint.id)

        # Find all existing groups that share a variable with `c_vars`
        intersecting = findall(g -> any(v -> _contains_equal(g[1], v), c_vars), groups)

        if isempty(intersecting)
            push!(groups, (c_vars, DomConstraint[constraint], true))
        else
            first_idx = first(intersecting)
            _push_unique!(groups[first_idx][1], c_vars)
            push!(groups[first_idx][2], constraint)
            groups[first_idx] = (groups[first_idx][1], groups[first_idx][2], true)

            for idx in Iterators.reverse(intersecting[2:end])
                _push_unique!(groups[first_idx][1], groups[idx][1])
                append!(groups[first_idx][2], groups[idx][2])
                deleteat!(groups, idx)
            end
        end
    end

    # Prune redundant constraints only in touched groups
    all_constraints_out = DomConstraint[]
    blocks_out = DomBlock[]

    for (vars, cs, touched) in groups
        sort!(vars, by=string)
        final_cs = (touched && prune_redundant) ?
                   _prune_block_constraints(vars, cs, new_ids; throw_on_infeasible=throw_on_infeasible) : cs
        final_cs === nothing && return nothing
        append!(all_constraints_out, final_cs)
        push!(blocks_out, DomBlock(vars, ConstraintId[c.id for c in final_cs]))
    end

    result = SymDomain(all_constraints_out, blocks_out)
    return share_blocks(result, original)
end

"""
    rewrite_constraints(f, domain, ivs=nothing)

Apply `f(::SymRelation) -> SymRelation` to every constraint, keeping each
constraint's Id, and regroup the result (a change of variables can merge or
split components). This is what keeps boundary-condition references valid
through coordinate transforms and simplification.
"""
function rewrite_constraints(f, domain::SymDomain, ivs=nothing)
    rewritten = DomConstraint[DomConstraint(c.id, f(c.relation)) for c in all_constraints(domain)]
    return share_blocks(add_constraints(domain_from_constraints(DomConstraint[], ivs), rewritten, ivs), domain)
end

# ---------------------------------------------------------------------------
# Building domains and sub-domains
# ---------------------------------------------------------------------------
"""
    domain_from_constraints(constraints; variables=(), fresh_id=nothing)

Build a domain from bare constraints (`x > 0`, `x^2 + y^2 < 1`, SymRelations or
DomConstraints); the blocks are found automatically as the connected groups of
variables. `variables` declares variables that have no constraint at all (an
unbounded block). Without `fresh_id` the constraints carry provisional Ids;
pass e.g. `() -> next_constraint_id!(tree)` to register them right away.
"""
function domain_from_constraints(constraints; variables=())
    seen = Symbolics.Num[]
    blocks = DomBlock[]

    for v in variables
        n = _as_num(v)
        any(isequal(n), seen) && continue
        push!(seen, n)
        push!(blocks, DomBlock([n], ConstraintId[]))
    end

    skeleton = _unchecked_domain(DomConstraint[], blocks, seen)
    return add_constraints(skeleton, constraints)
end

# 2. `SymDomain(constraints)` for bare constraints is now a 1-liner:
function SymDomain(constraints::Union{AbstractVector,Tuple})
    isempty(constraints) && return _unchecked_domain(DomConstraint[], DomBlock[], Symbolics.Num[])
    return domain_from_constraints(constraints)
end
# What `DESys(domain=...)` accepts: a SymDomain, `key => constraints` pairs,
# or bare constraints.
_as_domain(domain::SymDomain) = domain
function _as_domain(x)
    items = x isa Union{Tuple,AbstractVector} ? x : (x,)
    isempty(items) && return SymDomain(Pair[])
    return domain_from_constraints(items)
end

"""
    subdomain(domain, blocks)

The product of just the given blocks of `domain`. The block objects are
shared, so their pavings come along.
"""
function subdomain(domain::SymDomain, blocks)
    block_vec = DomBlock[b for b in blocks]
    sort!(block_vec, by=b -> string(b.variables[begin]))
    constraints = DomConstraint[c for b in block_vec for c in constraints_of(domain, b)]
    sort!(constraints, by=c -> c.id)
    variables = Symbolics.Num[v for b in block_vec for v in b.variables]
    return _unchecked_domain(constraints, block_vec, variables)
end

"""
    share_blocks(new, old)

Replace each block of `new` by the block of `old` that has the same
variables, the same constraint Ids *and* the same constraint content, if there
is one. Sharing keeps the cached paving and means a paving computed later is
seen by both domains.
"""
function share_blocks(new::SymDomain, old::SymDomain)
    isempty(old.blocks) && return new
    shared = DomBlock[_matching_block(new, b, old) for b in new.blocks]
    all(i -> shared[i] === new.blocks[i], eachindex(shared)) && return new
    return _unchecked_domain(copy(new.constraints), shared, copy(new.variables))
end

function _matching_block(new::SymDomain, b::DomBlock, old::SymDomain)
    for g in old.blocks
        length(g.variables) == length(b.variables) || continue
        g.constraint_ids == b.constraint_ids || continue
        all(isequal(x, y) for (x, y) in zip(g.variables, b.variables)) || continue
        all(_same_relation(find_constraint(old, id), find_constraint(new, id))
            for id in b.constraint_ids) || continue
        return g
    end
    return b
end

block_content_key(domain::SymDomain, b::DomBlock) = (
    Tuple(Symbolics.unwrap(v) for v in b.variables),
    Tuple((Symbolics.unwrap(c.relation.residual), c.relation.relation) for c in constraints_of(domain, b))
)

"""
    blocks_content_key(domain, blocks)

A hashable key describing the given blocks by content only: variables and
constraint expressions, no Ids and no pavings.
"""
blocks_content_key(domain::SymDomain, blocks) =
    Tuple(block_content_key(domain, b) for b in blocks)

# ---------------------------------------------------------------------------
# Domain rewriting
# ---------------------------------------------------------------------------
# Variables a block's variables turn into under `mapping`.
function _mapped_block_variables(block::DomBlock, mapping)
    variables = Any[]
    for variable in block.variables
        mapped = haskey(mapping, variable) ? substitute(variable, mapping) : variable
        for mapped_variable in Symbolics.get_variables(unwrap(mapped))
            push!(variables, mapped_variable)
        end
    end
    return _ordered_unique(variables)
end

"""
    _rebuild_domain(domain, touched, rewrite, mapped_variables)

* `touched(block)`: does the transformation affect this block?
* `rewrite(relation)`: the transformed `SymRelation` (Ids are preserved).
* `mapped_variables(block)`: the variables of a touched block after the
  transformation.
"""
function _rebuild_domain(domain::SymDomain, touched, rewrite, mapped_variables)
    all_vars = Symbolics.Num[]
    constraints = DomConstraint[]
    for block in domain.blocks
        is_touched = touched(block)
        vars = is_touched ? mapped_variables(block) : block.variables
        for v in vars
            _push_unique!(all_vars, (_as_num(v),))
        end
        for c in constraints_of(domain, block)
            push!(constraints, is_touched ? DomConstraint(c.id, rewrite(c.relation)) : c)
        end
    end
    rebuilt = domain_from_constraints(constraints; variables=all_vars)
    return share_blocks(rebuilt, domain)
end

# Transform domain constraints under an independent-variable change. Only
# blocks containing a mapped variable are rewritten.
function transform_domains(domain::SymDomain, iv_mapping::Dict, ivs=nothing)
    _rebuild_domain(
        domain,
        block -> any(variable -> haskey(iv_mapping, variable), block.variables),
        relation -> SymRelation(simplify(substitute(relation.residual, iv_mapping)), relation.relation),
        block -> _mapped_block_variables(block, iv_mapping))
end

# Same for a parameter change: constraints such as `x < a` change when `a` does.
function transform_domain_parameters(domain::SymDomain, param_mapping::Dict)
    _rebuild_domain(
        domain,
        block -> any(variable -> haskey(param_mapping, variable), block.variables),
        relation -> SymRelation(simplify(substitute(relation.residual, param_mapping)), relation.relation),
        block -> _mapped_block_variables(block, param_mapping))
end