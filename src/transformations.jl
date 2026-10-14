
function _transform_restrictions(restrictions, transform)
    SymRestriction[
        SymRestriction(transform(restriction.residual), restriction.relation)
        for restriction in restrictions
    ]
end

# Change parameters in place.  The return value is intentional: it supports
# chaining while the `!` name makes the mutation explicit to callers.
function change_parameters!(sys::DESys, param_mapping::Dict)
    # Pass 1: Raw substitution without the special rewriter
    substituted_eqs = [wrap(substitute(eq.lhs - eq.rhs, param_mapping)) for eq in sys.eqs]
    substituted_bcs_lhs = [wrap(substitute(bc.lhs, param_mapping)) for bc in sys.bcs]
    substituted_bcs_rhs = [wrap(substitute(bc.rhs, param_mapping)) for bc in sys.bcs]

    # Pass 2: Extract NEW parameters directly from the expressions
    # Leveraging your ability to pass Symbolics.Num directly into the tuple
    substituted_restrictions = [
        wrap(substitute(restriction.residual, param_mapping))
        for restriction in sys.restrictions
    ]
    exprs_tuple = Tuple(vcat(substituted_eqs, substituted_bcs_lhs,
        substituted_bcs_rhs, substituted_restrictions))
    new_params = extract_parameters(exprs_tuple)

    transformed_eqs = Symbolics.Equation[]
    for seq in substituted_eqs
        push!(transformed_eqs, simplify(SPECIAL_REWRITER(seq)) ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for (slhs, srhs) in zip(substituted_bcs_lhs, substituted_bcs_rhs)
        push!(transformed_bcs, simplify(SPECIAL_REWRITER(slhs)) ~ simplify(SPECIAL_REWRITER(srhs)))
    end
    transformed_restrictions = _transform_restrictions(
        sys.restrictions,
        residual -> simplify(SPECIAL_REWRITER(substitute(residual, param_mapping))))
    new_domain = transform_domain_parameters(sys.domain, param_mapping)
    step = PsTransform(
        param_mapping, sys.ps, new_params)
    _replace_branch!(sys; eqs=transformed_eqs, ivs=sys.ivs, dvs=sys.dvs,
        ps=new_params, bcs=transformed_bcs, domain=new_domain,
        restrictions=transformed_restrictions,
        history=append_derivation(sys.history, step))
end

#helper for change_independents - recursively traverses expression trees
function custom_rewrite(expr, var_map, J_inv, new_ivs, old_u, new_u, dv_funcs, cache=Dict())
    expr = unwrap(expr)

    if haskey(cache, expr)
        return cache[expr]
    end

    # Base case: if it's not a tree (like a standalone x), replace if mapped
    if !SymbolicUtils.iscall(expr)
        res = haskey(var_map, expr) ? var_map[expr] : expr
        cache[expr] = res
        return res
    end

    op = SymbolicUtils.operation(expr)
    args = SymbolicUtils.arguments(expr)

    # Intercept dependent variables (e.g., changing u(x,y) to u(r,θ))
    # Done top-down, skipping the arguments inside so they never become polar coordinates.
    if _contains_equal(dv_funcs, op)
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

function change_ivs!(sys::DESys, new_ivs::Vector{Symbolics.Num}, iv_mapping::Dict)
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
    params = extract_parameters(Tuple(vcat(sys.eqs, sys.bcs, iv_exprs,
        [restriction.residual for restriction in sys.restrictions])))

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
    transformed_restrictions = _transform_restrictions(
        sys.restrictions,
        residual -> simplify(SPECIAL_REWRITER(expand_derivatives(wrap(
            custom_rewrite(unwrap(residual), var_map, J_inv, new_ivs,
                old_u, new_u, dv_funcs))))))

    new_domains = transform_domains(sys.domain, iv_mapping, final_ivs)

    new_dvs = [Symbolics.wrap(custom_rewrite(unwrap(dv), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)) for dv in sys.dvs]
    step = IvTransform(
        iv_mapping, sys.ivs, new_ivs)
    _replace_branch!(sys; eqs=transformed_eqs, ivs=final_ivs, dvs=new_dvs,
        ps=params, bcs=transformed_bcs, domain=new_domains,
        restrictions=transformed_restrictions,
        history=append_derivation(sys.history, step))
end


function substitute_dvs(expr, old_dvs, dv_exprs, ivs, cache=Dict())
    expr = unwrap(expr)

    if haskey(cache, expr)
        return cache[expr]
    end

    if !SymbolicUtils.iscall(expr)
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



function change_dvs!(sys::DESys, new_dvs::Vector{Symbolics.Num}, dv_mapping::Dict)
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

    params = extract_parameters(Tuple(vcat(sys.eqs, sys.bcs, dv_exprs,
        [restriction.residual for restriction in sys.restrictions])))

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
    transformed_restrictions = _transform_restrictions(
        sys.restrictions,
        residual -> simplify(SPECIAL_REWRITER(expand_derivatives(wrap(
            substitute_dvs(unwrap(residual), old_dvs, u_dv_exprs, ivs))))))

    # Passing sys.params assuming you want to retain the original params block manually
    mapping = Dict(old_dvs .=> dv_exprs)
    step = DvTransform(mapping, sys.dvs, final_dvs)
    _replace_branch!(sys; eqs=transformed_eqs, ivs=sys.ivs, dvs=final_dvs,
        ps=params, bcs=transformed_bcs, domain=sys.domain,
        restrictions=transformed_restrictions,
        history=append_derivation(sys.history, step))
end

# Collection-level hooks apply the transformation independently to every
# branch while retaining the identity and bookkeeping of the system object.
function change_parameters!(sys::DiffEqSystem, param_mapping::Dict)
    foreach(branch -> change_parameters!(branch, param_mapping), sys.branches)
    sys
end

function change_ivs!(
    sys::DiffEqSystem, new_ivs::Vector{Symbolics.Num}, iv_mapping::Dict,
)
    foreach(branch -> change_ivs!(branch, new_ivs, iv_mapping), sys.branches)
    sys
end

function change_dvs!(
    sys::DiffEqSystem, new_dvs::Vector{Symbolics.Num}, dv_mapping::Dict,
)
    foreach(branch -> change_dvs!(branch, new_dvs, dv_mapping), sys.branches)
    sys
end

# Keep the established names as mutating aliases.  Callers that need a
# non-mutating transformation should explicitly copy the branch/system first.
change_parameters(sys::DESys, param_mapping::Dict) =
    change_parameters!(sys, param_mapping)
change_ivs(sys::DESys, new_ivs::Vector{Symbolics.Num}, iv_mapping::Dict) =
    change_ivs!(sys, new_ivs, iv_mapping)
change_dvs(sys::DESys, new_dvs::Vector{Symbolics.Num}, dv_mapping::Dict) =
    change_dvs!(sys, new_dvs, dv_mapping)
change_parameters(sys::DiffEqSystem, param_mapping::Dict) =
    change_parameters!(sys, param_mapping)
change_ivs(sys::DiffEqSystem, new_ivs::Vector{Symbolics.Num}, iv_mapping::Dict) =
    change_ivs!(sys, new_ivs, iv_mapping)
change_dvs(sys::DiffEqSystem, new_dvs::Vector{Symbolics.Num}, dv_mapping::Dict) =
    change_dvs!(sys, new_dvs, dv_mapping)
