
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
    #the SymbolicDomain constructor canonicalizes on it's own
    if domain_pairs isa SymbolicDomain
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
    constraint,
)
    constraint_variables = Set(Symbolics.get_variables(Symbolics.unwrap(constraint)))
    intersecting = _intersecting_group_indices(groups, constraint_variables)
    if isempty(intersecting)
        push!(groups, (constraint_variables, Any[constraint]))
        return groups
    end

    first_group = first(intersecting)
    union!(groups[first_group][1], constraint_variables)
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

function _add_constraint_variables!(variable_order, constraint, ivs)
    for variable in Symbolics.get_variables(Symbolics.unwrap(constraint))
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
    domain::SymbolicDomain,
    new_constraints::AbstractVector,
    ivs=nothing,
)
    domain_pairs = _domain_pairs(domain)
    variable_order = ivs === nothing ? _domain_variables(domain_pairs) : collect(ivs)
    ivs !== nothing && _validate_iv_order!(variable_order, domain_pairs)
    groups = [(Set(_key_variables(key)), collect(Any, constraints))
              for (key, constraints) in domain_pairs]

    for constraint in new_constraints
        _add_constraint_variables!(variable_order, constraint, ivs)
        _add_constraint!(groups, constraint)
    end

    if ivs !== nothing
        sort!(groups, by=group -> _group_order_index(group, variable_order))
    end

    final_pairs = Pair[]
    final_variables = Symbolics.Num[]
    for (variable_set, constraints) in groups
        ordered_variables = _ordered_group_variables(variable_set, variable_order)
        new_key = length(ordered_variables) == 1 ? only(ordered_variables) : Tuple(ordered_variables)
        push!(final_pairs, new_key => constraints)
        append!(final_variables, ordered_variables)
    end
    return SymbolicDomain(final_pairs, final_variables)
end

add_constraints(domain_pairs::AbstractVector{<:Pair}, new_constraints::Pair, ivs=nothing) =
    add_constraints(domain_pairs, [new_constraints], ivs)

function restrict_domain(sys::DiffEqBranch, constraint::Symbolics.Num)
    sys.domain=add_constraints(sys.domain, constraint)
    vars = Symbolics.get_variables(constraint)
    push!(sys.history.steps, DomainRestrictStep(vars, constraint))
end

const ROI = Ref{Float64}(1000.0)
const tolerance = Ref{Float64}(0.01)
#=
this is how to Change the global bound for this session
DiffEqCAS.ROI[] = 50000.0
=#

#helper for constraints_to_domain
function shrink_bounds!(bounds, constraint)
    vars = Symbolics.get_variables(constraint)
    if !(length(vars)==1)
        return bounds
    end
    var=vars[1]
    relation = Symbolics.unwrap(constraint)
    lhs, rhs = SymbolicUtils.arguments(relation)
    expr = simplify(lhs - rhs)
    if !isequal(Symbolics.degree(expr, var), 1)
        return bounds
    end
    op = Symbolics.operation(relation)
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
    SymbolicUtils.istree(unwrapped) || return interval(-Inf, Inf)
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

function _domain_relation_status(constraint, variables, box)
    relation = Symbolics.unwrap(constraint)
    op = Symbolics.operation(relation)
    op in ((<), (≤), (>), (≥), (==), (!=)) || return :unknown
    lhs, rhs = SymbolicUtils.arguments(relation)
    value = _domain_interval_value(lhs - rhs, variables, box)
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

function constraints_to_domain(domain_pairs)
    domain_pairs = _domain_pairs(domain_pairs)
    isempty(domain_pairs) && return nothing
    all_vars = _domain_variables(domain_pairs)
    bounds = Dict{Any,Vector{Float64}}(v => [-ROI[], ROI[]] for v in all_vars)
    collected_constraints = Any[]
    for (_, group_constraints) in domain_pairs, c in group_constraints
        u_c = Symbolics.unwrap(c)
        constraint_vars = Symbolics.get_variables(u_c)
        all(v -> haskey(bounds, v), constraint_vars) ||
            throw(ArgumentError("domain constraints reference variables absent from their domain keys"))
        push!(collected_constraints, u_c)
        shrink_bounds!(bounds, c)
    end
    any(bounds[v][1] > bounds[v][2] for v in all_vars) &&
        return (IntervalBox[], IntervalBox[])
    intervals = [bareinterval(bounds[v][1], bounds[v][2]) for v in all_vars]
    box = IntervalBox(intervals...)
    return _pave_constraints(box, collected_constraints, all_vars, tolerance[])
end

function add_domain_paving(sys::DiffEqBranch)
    sys.domain_set === nothing && (sys.domain_set = constraints_to_domain(sys.domain))
    return sys.domain_set
end

function is_in_domain(coord::StaticArrays.SVector, sys::DiffEqBranch, include_boundary::Bool=true)
    domain_data = constraints_to_domain(sys)
    domain_data === nothing && return false
    length(coord) == length(_domain_variables(sys.domain)) ||
        throw(DimensionMismatch("coords must have the same dimension as domain"))
    domain, boundary = domain_data
    domain_data === nothing && return false
    boxes = include_boundary ? (domain..., boundary...) : domain
    return any(coord ∈ box for box in boxes)
end


function is_in_domain(coord::StaticArrays.SVector, domain_constraints::AbstractVector, include_boundary::Bool=true)
    length(coord) == length(_domain_variables(domain_constraints)) ||
        throw(DimensionMismatch("coords must have the same dimension as domain"))
    domain_data = constraints_to_domain(domain_constraints)
    domain_data === nothing && return false
    domain, boundary = domain_data
    boxes = include_boundary ? (domain..., boundary...) : domain
    return any(coord ∈ box for box in boxes)
end

"""
    constraints_satisfiable(constraints, domain_constraints, include_boundary=true)

Check whether `constraints` have a feasible point in the supplied domain
component. The component should contain every variable referenced by the new
constraints; unrelated Cartesian factors should be omitted.
"""
function constraints_satisfiable(
    constraints,
    domain_constraints,
    include_boundary::Bool=true,
)
    new_constraints = constraints isa AbstractVector || constraints isa Tuple ?
                      constraints : (constraints,)
    combined = add_constraints(domain_constraints, new_constraints)
    result = constraints_to_domain(combined)
    result === nothing && return false
    domain, boundary = result
    return include_boundary ? (!isempty(domain) || !isempty(boundary)) : !isempty(domain)
end

add_domain_paving(sys::DiffEqSystem) = foreach(add_domain_paving, sys.branches)

function is_in_domain(coord::StaticArrays.SVector, sys::DiffEqSystem,
    include_boundary::Bool=true)
    all(is_in_domain(coord, branch, include_boundary) for branch in sys.branches)
end
