
#for just changing parameters
function change_parameters(sys::PDESystem, param_mapping::Dict)
    # Pass 1: Raw substitution without the special rewriter
    substituted_eqs = [wrap(substitute(eq.lhs - eq.rhs, param_mapping)) for eq in sys.eqs]
    substituted_bcs_lhs = [wrap(substitute(bc.lhs, param_mapping)) for bc in sys.bcs]
    substituted_bcs_rhs = [wrap(substitute(bc.rhs, param_mapping)) for bc in sys.bcs]

    # Pass 2: Extract NEW parameters directly from the expressions
    # Leveraging your ability to pass Symbolics.Num directly into the tuple
    exprs_tuple = Tuple(vcat(substituted_eqs, substituted_bcs_lhs, substituted_bcs_rhs))
    new_params = extract_parameters(exprs_tuple)

    transformed_eqs = Symbolics.Equation[]
    for seq in substituted_eqs
        push!(transformed_eqs, simplify(SPECIAL_REWRITER(seq)) ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for (slhs, srhs) in zip(substituted_bcs_lhs, substituted_bcs_rhs)
        push!(transformed_bcs, simplify(SPECIAL_REWRITER(slhs)) ~ simplify(SPECIAL_REWRITER(srhs)))
    end
    # *need to add a helper function for getting the new domains
    return PDESystem(eqs=transformed_eqs, ivs=sys.ivs, dvs=sys.dvs, ps=new_params, bcs=transformed_bcs, domain=new_domains, name=sys.name)
end

#helper for change_independents - recursively traverses expression trees
function custom_rewrite(expr, var_map, J_inv, new_ivs, old_u, new_u, dv_funcs, cache=Dict())
    expr = unwrap(expr)

    if haskey(cache, expr)
        return cache[expr]
    end

    # Base case: if it's not a tree (like a standalone x), replace if mapped
    if !SymbolicUtils.istree(expr)
        res = haskey(var_map, expr) ? var_map[expr] : expr
        cache[expr] = res
        return res
    end

    op = SymbolicUtils.operation(expr)
    args = SymbolicUtils.arguments(expr)

    # Intercept dependent variables (e.g., changing u(x,y) to u(r,θ))
    # Done top-down, skipping the arguments inside so they never become polar coordinates.
    if any(isequal(op, d) for d in dv_funcs)
        res = unwrap(op(new_u...))
        cache[expr] = res
        return res
    end

    # Intercept Differential operators
    if op isa Differential
        diff_var = op.x
        # Grab the order, defaulting to 1 for standard first-order derivatives
        diff_order = hasproperty(op, :order) ? op.order : 1

        idx = findfirst(isequal(unwrap(diff_var)), old_u)
        if idx !== nothing
            # Process the argument inside the differential first
            rewritten_arg = custom_rewrite(args[1], var_map, J_inv, new_ivs, old_u, new_u, dv_funcs, cache)

            res = chain_rule(J_inv, idx, new_ivs, rewritten_arg, diff_order)
            cache[expr] = res
            return res
        end
    end

    new_args = [custom_rewrite(a, var_map, J_inv, new_ivs, old_u, new_u, dv_funcs, cache) for a in args]

    if all(a === b for (a, b) in zip(args, new_args))
        cache[expr] = expr
        return expr
    end
    res = maketerm(typeof(expr), op, new_args, nothing)
    cache[expr] = res
    return res
end

#helper for change_independents - changes domain Dict 
#*needs updating so it can also separate vars and not only join them together
function transform_domains(old_domain_pairs, iv_mapping::Dict)
    new_domain_pairs = Pair[]

    for (old_vars, constraints) in old_domain_pairs
        # Normalize the key to a tuple for uniform processing
        var_tuple = old_vars isa Tuple ? old_vars : (old_vars,)

        # Check if any variable in this specific domain block is being mapped
        if any(haskey(iv_mapping, v) for v in var_tuple)

            # 1. Substitute the mapping directly into the symbolic constraints
            # This applies the coordinate transformation algebraically
            new_constraints = [simplify(substitute(c, iv_mapping)) for c in constraints]

            # 2. Identify the new variables that make up this transformed domain
            found_vars = Set{Symbolics.Num}()
            for nc in new_constraints
                union!(found_vars, Symbolics.get_variables(Symbolics.unwrap(nc)))
            end

            # 3. Format the new key (tuple for 2D+, single var for 1D)
            found_vars_arr = collect(found_vars)
            new_key = length(found_vars_arr) == 1 ? found_vars_arr[1] : Tuple(found_vars_arr)

            # Push the updated symbolic pair
            push!(new_domain_pairs, new_key => new_constraints)
        else
            # If no mapping affects this block, pass it through unchanged[cite: 1]
            push!(new_domain_pairs, old_vars => constraints)
        end
    end

    return new_domain_pairs
end

function change_ivs(sys::PDESystem, new_ivs::Vector{Symbolics.Num}, iv_mapping::Dict)
    #make sure iv_mapping is from old variables to expressions containing new variables
    iv_exprs = Symbolics.Num[]
    for old_iv in sys.ivs
        if haskey(iv_mapping, old_iv)
            push!(iv_exprs, iv_mapping[old_iv])
        else
            # Fallback: if the user omits a variable from the dictionary, keep it unchanged
            push!(iv_exprs, old_iv)
        end
    end

    replaced_old_ivs = collect(keys(iv_mapping))
    # Keep old variables that do not appear in the dictionary keys
    kept_old_ivs = setdiff(sys.ivs, replaced_old_ivs)

    final_ivs = vcat(kept_old_ivs, new_ivs)
    old_u = unwrap.(sys.ivs)
    new_u = unwrap.(new_ivs)
    dv_funcs = unique([get_base_op(unwrap(dv)) for dv in sys.dvs])
    params = extract_parameters(Tuple(vcat(sys.eqs, sys.bcs, iv_exprs)))

    J_inv = compute_J_inv(iv_exprs, new_ivs)
    var_map = Dict(old_u .=> unwrap.(iv_exprs))

    transformed_eqs = Symbolics.Equation[]
    for eq in sys.eqs
        lhs_expr = eq.lhs - eq.rhs
        lhs_u = unwrap(lhs_expr)
        rewritten_lhs = custom_rewrite(lhs_u, var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)
        simplified_lhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(rewritten_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end
    transformed_bcs = Symbolics.Equation[]
    for bc in sys.bcs
        # Transform LHS and RHS separately to maintain equations like u(0, y) ~ 1
        rewritten_lhs = custom_rewrite(unwrap(bc.lhs), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)
        simplified_lhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(rewritten_lhs))))

        rewritten_rhs = custom_rewrite(unwrap(bc.rhs), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)
        simplified_rhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(rewritten_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end

    new_domains = transform_domains(sys.domain, iv_mapping, new_ivs)

    new_dvs = [Symbolics.wrap(custom_rewrite(unwrap(dv), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)) for dv in sys.dvs]
    return PDESystem(eqs=transformed_eqs, ivs=final_ivs, dvs=new_dvs, ps=params, bcs=transformed_bcs, domain=sys.domain, name=sys.name)
end


function substitute_dvs(expr, old_dvs, dv_exprs, ivs, cache=Dict())
    expr = unwrap(expr)

    if haskey(cache, expr)
        return cache[expr]
    end

    if !SymbolicUtils.istree(expr)
        cache[expr] = expr
        return expr
    end

    idx = nothing
    for (i, dv) in enumerate(old_dvs)
        if isequal(get_base_op(expr), get_base_op(dv))
            if isequal(SymbolicUtils.operation(expr), getindex) && isequal(SymbolicUtils.operation(dv), getindex)
                if isequal(SymbolicUtils.arguments(expr)[2:end], SymbolicUtils.arguments(dv)[2:end])
                    idx = i
                    break
                end
            elseif isequal(SymbolicUtils.operation(expr), SymbolicUtils.operation(dv))
                idx = i
                break
            end
        end
    end

    if idx !== nothing
        curr = expr
        while isequal(SymbolicUtils.operation(curr), getindex)
            curr = SymbolicUtils.arguments(curr)[1]
        end
        args = SymbolicUtils.arguments(curr)

        arg_sub = Dict(wrap.(ivs) .=> wrap.(args))
        res = unwrap(substitute(wrap(dv_exprs[idx]), arg_sub))
        cache[expr] = res
        return res
    end

    op = SymbolicUtils.operation(expr)
    args = SymbolicUtils.arguments(expr)
    new_args = [substitute_dvs(a, old_dvs, dv_exprs, ivs, cache) for a in args]

    if all(a === b for (a, b) in zip(args, new_args))
        cache[expr] = expr
        return expr
    end

    res = maketerm(typeof(expr), op, new_args, nothing)
    cache[expr] = res
    return res
end



function change_dvs(sys::PDESystem, new_dvs::Vector{Symbolics.Num}, dv_mapping::Dict)
    # 1. Align expressions with the existing dvendency order
    dv_exprs = Symbolics.Num[]
    for old_dv in sys.dvs
        if haskey(dv_mapping, old_dv)
            push!(dv_exprs, dv_mapping[old_dv])
        else
            push!(dv_exprs, old_dv)
        end
    end

    replaced_old_dvs = collect(keys(dv_mapping))
    kept_old_dvs = setdiff(sys.dvs, replaced_old_dvs)

    final_dvs = vcat(kept_old_dvs, new_dvs)

    ivs = unwrap.(sys.ivs)
    old_dvs = unwrap.(sys.dvs)
    u_dv_exprs = unwrap.(dv_exprs)

    params = extract_parameters(Tuple(vcat(sys.eqs, sys.bcs, dv_exprs)))

    transformed_eqs = Symbolics.Equation[]
    for eq in sys.eqs
        # Move to LHS and unwrap
        lhs_expr = unwrap(eq.lhs - eq.rhs)

        # Traverse and forcefully substitute inside Differentials
        substituted_lhs = substitute_dvs(lhs_expr, old_dvs, u_dv_exprs, ivs)
        simplified_lhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(substituted_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for bc in sys.bcs
        substituted_lhs = substitute_dvs(unwrap(bc.lhs), old_dvs, u_dv_exprs, ivs)
        simplified_lhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(substituted_lhs))))

        substituted_rhs = substitute_dvs(unwrap(bc.rhs), old_dvs, u_dv_exprs, ivs)
        simplified_rhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(substituted_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end

    # Passing sys.params assuming you want to retain the original params block manually
    return PDESystem(eqs=transformed_eqs, ivs=sys.ivs, dvs=final_dvs, ps=params, bcs=transformed_bcs, domain=sys.domain, name=sys.name)
end
