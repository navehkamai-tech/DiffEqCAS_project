
# 1. Internal mutating helper (operates on the mutable groups structure)
function _add_constraint!(groups::Vector{Tuple{Set{Any},Vector{Any}}}, nc)
    nc_unwrapped = Symbolics.unwrap(nc)
    nc_vars = Set(Symbolics.get_variables(nc_unwrapped))

    intersecting_indices = Int[]
    for i in eachindex(groups)
        if !isdisjoint(groups[i][1], nc_vars)
            push!(intersecting_indices, i)
        end
    end

    if isempty(intersecting_indices)
        push!(groups, (nc_vars, Any[nc]))
    else
        first_idx = intersecting_indices[1]
        union!(groups[first_idx][1], nc_vars)
        push!(groups[first_idx][2], nc)

        for i in reverse(intersecting_indices[2:end])
            union!(groups[first_idx][1], groups[i][1])
            append!(groups[first_idx][2], groups[i][2])
            deleteat!(groups, i)
        end
    end
    return groups
end

# 2. Plural API function (Handles array initialization and finalization)
function add_constraints(domain_pairs::Vector{Pair}, new_constraints::AbstractVector)
    groups = Vector{Tuple{Set{Any},Vector{Any}}}()
    for (k, c) in domain_pairs
        k_set = k isa Tuple ? Set(k) : Set([k])
        push!(groups, (k_set, collect(Any, c)))
    end

    for nc in new_constraints
        _add_constraint!(groups, nc) # Mutates in-place, preventing array allocations
    end

    final_pairs = Pair[]
    for (vars_set, constraints) in groups
        vars_arr = collect(vars_set)
        new_key = length(vars_arr) == 1 ? vars_arr[1] : Tuple(vars_arr)
        push!(final_pairs, new_key => constraints)
    end

    return final_pairs
end

const ROI = Ref{Float64}(1000.0)
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

function constraints_to_domain(domain::Vector{Pair})
    bounds = Dict()

    C = ICP.constraint(domain[1].second[1], domain[1].first)
    for (vars, constraints) in domain
        vars_list = vars isa Tuple ? vars : (vars,)
        for v in vars_list
            bounds[v] = [-ROI[], ROI[]]
        end
        for c in constraints
            u_c = unwrap(c)
            C = C ∩ constraint(u_c, vars_list)
            shrink_bounds!(bounds, c)
        end
    end

end
