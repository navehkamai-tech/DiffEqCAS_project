#operator used for boundary conditions
@register_symbolic Restrict(expr, domain)
SymbolicUtils.promote_symtype(::typeof(Restrict), _...) = Real


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

# `fresh_id` (e.g. `() -> next_constraint_id!(tree)`) gives the new constraint
# its Id; without it the constraint stays UNASSIGNED until registered with a tree.
function restrict_domain(sys::DESys, constraint; fresh_id=nothing)
    domain = add_constraints(sys.domain, constraint)
    fresh_id === nothing || (domain = assign_ids(domain, fresh_id))
    sys.domain = domain
    vars = constraint_variables(_as_constraint(constraint))
    push!(sys.history.steps, RestrictDomain(vars, constraint))
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
    coeff_value = SymbolicUtils.unwrap_const(Symbolics.unwrap(coeff))
    coeff_value isa Real || return bounds
    num = SymbolicUtils.unwrap_const(Symbolics.unwrap(substitute(expr, var => 0) / coeff))
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
    literal = SymbolicUtils.unwrap_const(unwrapped)
    literal isa Real && return bareinterval(literal)
    for (index, variable) in pairs(variables)
        isequal(unwrapped, Symbolics.unwrap(variable)) &&
            return box[index]
    end
    SymbolicUtils.iscall(unwrapped) || return interval(-Inf, Inf)
    op = SymbolicUtils.operation(unwrapped)
    args = SymbolicUtils.arguments(unwrapped)
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
    if paving === nothing || paving.roi != ROI[] || paving.tolerance != tolerance[]
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

add_domain_paving(sys::DESys) = domain_pavings(sys.domain)

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

is_in_domain(coord::StaticArrays.SVector, sys::DESys, include_boundary::Bool=true) =
    is_in_domain(coord, sys.domain, include_boundary)

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

add_domain_paving(sys::DiffEqSystem) = foreach(add_domain_paving, sys.branches)

function is_in_domain(coord::StaticArrays.SVector, sys::DiffEqSystem,
    include_boundary::Bool=true)
    all(is_in_domain(coord, branch, include_boundary) for branch in sys.branches)
end
