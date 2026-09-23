
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
function _canonicalize_domain_pairs(domain_pairs::AbstractVector{<:Pair}, ivs=nothing)
    variables = ivs === nothing ? Any[] : ivs
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
    domain_pairs::AbstractVector{<:Pair},
    new_constraints::AbstractVector,
    ivs=nothing,
)
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
    for (variable_set, constraints) in groups
        ordered_variables = _ordered_group_variables(variable_set, variable_order)
        new_key = length(ordered_variables) == 1 ? only(ordered_variables) : Tuple(ordered_variables)
        push!(final_pairs, new_key => constraints)
    end
    return final_pairs
end

add_constraints(domain_pairs::AbstractVector{<:Pair}, new_constraints::Pair, ivs=nothing) =
    add_constraints(domain_pairs, [new_constraints], ivs)

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
    expr = simplify(constraint.lhs-constraint.rhs)
    if !(Symbolics.degree(expr, var)==1)
        return bounds
    end
    op = Symbolics.operation(constraint)
    coeff = Symbolics.coeff(expr, var)
    num = substitute(expr, var => 0)/coeff
    if (((op === <) || (op === ≤)) && (coeff > 0)) || (((op === >) || (op === ≥))&&(coeff < 0))
        bounds[var][2] = min(-num, bounds[var][2])
    elseif (((op === <) || (op === ≤)) && (coeff < 0)) || (((op === >) || (op === ≥))&&(coeff > 0))
        bounds[var][1] = max(-num, bounds[var][1])
    end
    return bounds
end

function constraints_to_domain(domain_pairs::AbstractVector{<:Pair})
    if isempty(domain_pairs)
        return nothing
    end

    # 1. Establish canonical order
    all_vars = _domain_variables(domain_pairs)

    bounds = Dict{Any,Vector{Float64}}()
    for v in all_vars
        bounds[v] = [-ROI[], ROI[]]
    end

    # 2. Build constraints over the full canonical space
    local C = nothing
    for (_, constraints) in domain_pairs
        for c in constraints
            u_c = Symbolics.unwrap(c)
            constraint_vars = Symbolics.get_variables(u_c)
            all(v -> haskey(bounds, v), constraint_vars) ||
                throw(ArgumentError("domain constraints reference variables absent from their domain keys"))

            # Pass all_vars instead of the local vars_list
            new_C = ICP.constraint(u_c, all_vars)

            C = C === nothing ? new_C : C ∩ new_C
            shrink_bounds!(bounds, c)
        end
    end

    # 3. Construct the bounding box using the exact canonical order
    intervals = [bareinterval(bounds[v][1], bounds[v][2]) for v in all_vars]
    Box = IntervalBox(intervals...)

    C === nothing && return ([Box], IntervalBox[])
    (domain, boundary) = ICP.pave(C, Box, tolerance[])
    return (domain, boundary)
end

function is_in_domain(
    coord::StaticArrays.SVector,
    domain_constraints::AbstractVector,
    include_boundary::Bool=true,
)
    if length(coord) != length(_domain_variables(domain_constraints))
        throw(DimensionMismatch("coords must have the same dimension as domain"))
    end

    result = constraints_to_domain(domain_constraints)
    result === nothing && return false
    domain, boundary = result
    boxes = include_boundary ? (domain..., boundary...) : domain
    return any(coord ∈ box for box in boxes)
end

function anywhere_in_domain(
    constraints,
    domain_constraints::AbstractVector{<:Pair},
    include_boundary::Bool=true,
    ivs=nothing,
)
    new_constraints = constraints isa AbstractVector || constraints isa Tuple ?
        constraints : (constraints,)
    combined = add_constraints(domain_constraints, new_constraints, ivs)
    result = constraints_to_domain(combined)
    result === nothing && return false
    domain, boundary = result
    return include_boundary ? (!isempty(domain) || !isempty(boundary)) : !isempty(domain)
end
