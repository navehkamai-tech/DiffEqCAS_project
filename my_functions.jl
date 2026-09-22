#=
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, independent variables, dependent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
=#
using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets, ModelingToolkit, Unitful, IntervalArithmetic
import IntervalConstraintProgramming as ICP
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule
import ModelingToolkit: PDESystem

#region special functions
#defining sign metadata for symbols
@enum SignState positive negative undetermined
struct VariableSign end
Symbolics.option_to_metadata_type(::Val{:sign}) = VariableSign

function get_sign(var)
    var_unwrapped = Symbolics.unwrap(var)

    if var_unwrapped isa Real
        return var_unwrapped > 0 ? positive : (var_unwrapped < 0 ? negative : undetermined)
    end

    # Otherwise, query the metadata
    return Symbolics.getmetadata(var_unwrapped, VariableSign, undetermined)
end

#operator used for boundary conditions
@register_symbolic Restrict(expr, domain)
SymbolicUtils.promote_symtype(::typeof(Restrict), _...) = Real

#defining special functions
#Dirac Delta function
@register_symbolic Dirac(x::Union{Symbolics.Num,AbstractVector}, n::Int)
@register_symbolic Dirac(x::Union{Symbolics.Num,AbstractVector})

#Heaviside step function
@register_symbolic Heaviside(x::Union{AbstractVector,Symbolics.Num})
# 1. Define the helper functions as standard or anonymous functions
notavariable(x) = ModelingToolkit.isparameter(x) || ModelingToolkit.isconstant(x) || x isa Number
is_pos_param(var) = notavariable(var) && get_sign(var) == positive
is_neg_param(var) = notavariable(var) && get_sign(var) == negative

function is_array_literal(x)
    return SymbolicUtils.istree(x) && SymbolicUtils.operation(x) === SymbolicUtils.array_literal
end

# 2. Define the rule arrays as constants
const diff_op_rules = [
    # Handles explicit higher-order differentials: D(y, m)(D(x, n)(f))
    @rule(Differential(~y, ~m)(Differential(~x, ~n)(~f)) =>
        string(~x) < string(~y) ? Differential(~x, ~n)(Differential(~y, ~m)(~f)) : nothing),

    # Handles mixed cases: D(y)(D(x, n)(f)) and D(y, m)(D(x)(f))
    @rule(Differential(~y)(Differential(~x, ~n)(~f)) =>
        string(~x) < string(~y) ? Differential(~x, ~n)(Differential(~y)(~f)) : nothing),
    @rule(Differential(~y, ~m)(Differential(~x)(~f)) =>
        string(~x) < string(~y) ? Differential(~x)(Differential(~y, ~m)(~f)) : nothing),

    # rule for standard first-order differentials
    @rule(Differential(~y)(Differential(~x)(~f)) =>
        string(~x) < string(~y) ? Differential(~x)(Differential(~y)(~f)) : nothing)
]

const dirac_rules = [
    @rule(Dirac(~x) => is_array_literal(~x) ? prod([Symbolics.unwrap(Dirac(Symbolics.wrap(el), 0)) for el in SymbolicUtils.arguments(~x)[2:end]]) : nothing),
    @rule(Dirac(~x, ~n) => (is_array_literal(~x) && ~n isa AbstractArray) ? prod([Symbolics.unwrap(Dirac(Symbolics.wrap(el_x), el_n)) for (el_x, el_n) in zip(SymbolicUtils.arguments(~x)[2:end], ~n)]) : nothing),
    @rule(Dirac(~x) => Dirac(~x, 0)),
    @rule(Dirac(-(~x), ~n) => (-1)^(~n)*Dirac(~x, ~n)),
    @acrule(Dirac(~a::notavariable * ~x, ~n) => Dirac(~x, ~n) / (abs(~a) * (~a)^(~n))),
    @acrule(Dirac(~a::notavariable*(~x - ~c::Number), ~n) => Dirac(~x - ~c, ~n)/(abs(~a)*(~a)^(~n))),
    @rule(~x*Dirac(~x, 0) => 0),
    @rule(~x * Dirac(~x, ~n) => -(~n)*Dirac(~x, ~n-1)),
    @rule(Integral(~vars, ~domain::DomainSets.Domain)(~f * Dirac(~vars - ~c)) =>
        ~c ∈ ~domain ? substitute(~f, Dict(Symbolics.unwrap.(~vars) .=> Symbolics.unwrap.(~c))) : 0),
    @rule(Integral(~vars, ~domain::DomainSets.Domain)(Dirac(~vars - ~c)) =>
        ~c ∈ ~domain ? 1 : 0),
    @rule(Differential(~var, ~k)(Dirac(~var, ~n)) => Dirac(~var, ~n+~k))
]

const heaviside_rules = [
    @rule(Heaviside(-(~x)) => 1-Heaviside(~x)),
    @acrule(Heaviside(~a::is_pos_param * ~x) => Heaviside(~x)),
    @acrule(Heaviside(~a::is_neg_param * ~x) => 1 - Heaviside(~x)),
    @rule(Heaviside(~x)^~k::is_pos_param => Heaviside(~x)),
    @rule(Differential(~var, ~n)(Heaviside(~var)) => Dirac(~var, ~n-1)),
    @rule(Differential(~var, ~n)(Heaviside(~var - ~c::is_scalar)) => Dirac(~var - ~c, ~n-1)),
    @rule(Integral(~vars, ~domain::AbstractVector)(~f*Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(~f)),
    @rule(Integral(~vars, ~domain::AbstractVector)(Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(1))
]

# 3. Create the single, compiled rewriter constant
const SPECIAL_REWRITER = SymbolicUtils.Postwalk(SymbolicUtils.Chain(vcat(diff_op_rules, dirac_rules, heaviside_rules)))
#endregion

#region API/UI
#shorthand for creating Differentials
function D(vars...)
    # 1. Sort the provided variables alphabetically right away
    sorted_vars = sort(collect(vars), by=string)

    # 2. Return a custom operator that nests the Differentials from the inside out
    return expr -> foldr((v, ex) -> Differential(v)(ex), sorted_vars, init=expr)
end

function display_expr(expr)
    # Unwrap to access the raw SymbolicUtils tree
    expr_unwrapped = Symbolics.unwrap(expr)

    # 1. Base Case: If it's just a variable (x) or a number (5), leave it alone
    if !SymbolicUtils.istree(expr_unwrapped)
        return expr
    end

    op = SymbolicUtils.operation(expr_unwrapped)
    args = SymbolicUtils.arguments(expr_unwrapped)

    # 2. The Magic: Intercepting the Differentials
    if op isa Differential
        vars = []
        curr = expr_unwrapped

        # Dig all the way down the nested rabbit hole and collect the variables
        while SymbolicUtils.istree(curr) && SymbolicUtils.operation(curr) isa Differential
            push!(vars, SymbolicUtils.operation(curr).x)
            curr = SymbolicUtils.arguments(curr)[1]
        end

        # Join the variables into a single string (e.g., "x", "y" becomes "xy")
        var_str = join(string.(vars), "")

        # Create a temporary, fake function operator just for printing
        # This creates a callable symbol like D_xy
        display_op = SymbolicUtils.Sym{SymbolicUtils.FnType{Tuple,Real}}(Symbol("D_{$var_str}"))

        # Process whatever is inside the derivative, then wrap it in our fake function
        return wrap(display_op(Symbolics.unwrap(display_pde(curr))))
    end

    # 3. For Everything Else: (+, *, ^), rebuild the tree normally
    processed_args = map(a -> Symbolics.unwrap(display_pde(a)), args)
    return wrap(SymbolicUtils.similarterm(expr_unwrapped, op, processed_args))
end

function display_pde(eq::Symbolics.Equation)
    return display_expr(eq.lhs) ~ display_expr(eq.rhs)
end

display_pde(expr) = display_expr(expr)
#endregion

#region domain handling
function expr_to_domain(expr, vars)
    vars_array = vars isa AbstractVector ? Symbolics.unwrap.(vars) : [Symbolics.unwrap(vars)]
    # Similar to your transform_domains logic[cite: 1]
    expr_unwrapped = Symbolics.unwrap(expr)
    func_expr, _ = Symbolics.build_function(expr_unwrapped, vars_array, expression=Val{false})
    # SuperlevelSet(f, c) creates the domain where f(x) >= c
    new_domain = DomainSets.SuperlevelSet(x -> func_expr(collect(x)), 0.0)
    if new_domain === DomainSets.EmptySpace
        throw(DomainError("resulting domain is empty"))
    end
    return new_domain
end

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

const ROI = 1e3
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
            bounds[v] = [-ROI, ROI]
        end
        for c in constraints
            u_c = unwrap(c)
            C = C ∩ constraint(u_c, vars_list)
            shrink_bounds!(bounds, c)
        end
    end

end
#endregion

#region reusable computation helpers
function compute_J_inv(var_exprs, new_vars)
    J_T = transpose(jacobian(var_exprs, new_vars))
    J_inv = inv(Matrix(J_T))
    return simplify.(J_inv)
end

function chain_rule(J_inv, old_var_idx, new_vars, arg, order=1)
    term = wrap(arg)
    # Iteratively apply the chain rule for higher-order derivatives
    for _ in 1:order
        next_term = 0
        for j in eachindex(new_vars)
            D_j = Differential(new_vars[j])
            next_term += J_inv[old_var_idx, j] * D_j(term)
        end
        term = next_term
    end
    return unwrap(term)
end
#parameter helper
function extract_parameters(list::Tuple)
    symbols = Symbolics.Num[]
    for i in list
        if i isa Symbolics.Equation
            vars = collect(Symbolics.get_variables(unwrap(i.lhs - i.rhs)))
            append!(symbols, vars)
        elseif i isa Symbolics.Num
            vars = collect(Symbolics.get_variables(unwrap(i)))
            append!(symbols, vars)
        else
            throw(ArgumentError("cannot extract parameters from $(typeof(i))"))
        end
    end

    # Keep only unique variables found in the expressions
    unique_vars = unique(symbols)

    # Filter using ModelingToolkit's native parameter metadata check
    params = filter(unique_vars) do v
        ModelingToolkit.isparameter(unwrap(v))
    end

    # Return as Vector{Symbolics.Num} to maintain compatibility with your other functions
    return convert(Vector{Symbolics.Num}, wrap.(params))
end
#endregion

#region changes of variables
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
function transform_domains_symbolic(old_domain_pairs, iv_mapping::Dict)
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
    dv_funcs = [SymbolicUtils.operation(unwrap(dv)) for dv in sys.dvs]
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

    new_dvs = [Symbolics.wrap(SymbolicUtils.term(op, Symbolics.unwrap.(new_ivs)...)) for op in dv_funcs]
    return PDESystem(eqs=transformed_eqs, ivs=final_ivs, dvs=new_dvs, ps=params, bcs=transformed_bcs, domain=new_domains, name=sys.name)
end

#helper for change_dependents - recursively traverses expression trees
function substitute_dvs(expr, old_dv_ops, dv_exprs, ivs, cache=Dict())
    expr = unwrap(expr)

    if haskey(cache, expr)
        return cache[expr]
    end

    # If it's a leaf node (e.g., a standalone number or variable not in sub_dict)
    if !SymbolicUtils.istree(expr)
        cache[expr] = expr
        return expr
    end

    op = SymbolicUtils.operation(expr)
    args = SymbolicUtils.arguments(expr)

    # Check if the operation matches one of our old dependent variables (e.g., 'u' or 'v')
    idx = findfirst(isequal(op), old_dv_ops)
    if idx !== nothing
        # Map the independent variables to whatever arguments are currently inside the function
        # For u(0, t), this maps x => 0 and t => t
        arg_sub = Dict(wrap.(ivs) .=> wrap.(args))

        # Substitute these arguments into the corresponding new dependent expression
        # For f(x, t) + g(x, t), this yields f(0, t) + g(0, t)
        res = unwrap(substitute(wrap(dv_exprs[idx]), arg_sub))

        cache[expr] = res
        return res
    end

    # Recursively apply to arguments (drilling into Differential operators)
    new_args = [substitute_dvs(a, old_dv_ops, dv_exprs, ivs, cache) for a in args]

    # Reconstruct the tree if any arguments changed
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
    old_dv_ops = [SymbolicUtils.operation(unwrap(dv)) for dv in sys.dvs]
    u_dv_exprs = unwrap.(dv_exprs)

    params = extract_parameters(Tuple(vcat(sys.eqs, sys.bcs, dv_exprs)))

    transformed_eqs = Symbolics.Equation[]
    for eq in sys.eqs
        # Move to LHS and unwrap
        lhs_expr = unwrap(eq.lhs - eq.rhs)

        # Traverse and forcefully substitute inside Differentials
        substituted_lhs = substitute_dvs(lhs_expr, old_dv_ops, u_dv_exprs, ivs)
        simplified_lhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(substituted_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for bc in sys.bcs
        substituted_lhs = substitute_dvs(unwrap(bc.lhs), old_dv_ops, u_dv_exprs, ivs)
        simplified_lhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(substituted_lhs))))

        substituted_rhs = substitute_dvs(unwrap(bc.rhs), old_dv_ops, u_dv_exprs, ivs)
        simplified_rhs = simplify(SPECIAL_REWRITER(expand_derivatives(wrap(substituted_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end

    # Passing sys.params assuming you want to retain the original params block manually
    return PDESystem(eqs=transformed_eqs, ivs=sys.ivs, dvs=final_dvs, ps=params, bcs=transformed_bcs, domain=sys.domain, name=sys.name)
end
#endregion

#region equation simplifiers
#helpers for divide_common
function get_addends(expr)
    expr = Symbolics.unwrap(expr)
    if SymbolicUtils.istree(expr) && SymbolicUtils.operation(expr) === (+)
        return reduce(vcat, get_addends.(SymbolicUtils.arguments(expr)))
    end
    return [expr]
end

function get_factors(expr)
    expr = Symbolics.unwrap(expr)
    if SymbolicUtils.istree(expr) && SymbolicUtils.operation(expr) === (*)
        return reduce(vcat, get_factors.(SymbolicUtils.arguments(expr)))
    end
    return [expr]
end

function is_divisible(expr, sys::PDESystem)
    if !SymbolicUtils.istree(expr)
        if (isequal(expr, p) for p in sys.ps)
            return true
        elseif (p isa Number) && p != 0
            return true
        elseif (isequal(expr, p) for p in sys.ivs)

        end
    end
end

function extract_and_divide_common(expr)
    expr_unwrapped = Symbolics.unwrap(expr)

    # Get a flat list of every term separated by a + or -
    addends = get_addends(expr_unwrapped)

    if length(addends) <= 1
        return expr
    end

    # Break the first addend into its multiplicative components to use as a baseline
    common_factors = get_factors(addends[1])

    # Intersect factors across all other addends
    for i in 2:length(addends)
        current_factors = get_factors(addends[i])

        # Keep only the factors that exist in BOTH the baseline and the current term
        filter!(f -> f in current_factors, common_factors)

        # Early exit if we lose all common factors
        if isempty(common_factors)
            break
        end
    end

    # Reconstruct the common divisor by multiplying the surviving factors
    if !isempty(common_factors)
        common_divisor = prod(common_factors)

        # needs modification for checking if dividing is allowed, depending on the type of common_divisor and on the domain.
        return simplify(expr_unwrapped / common_divisor)
    end

    return expr
end

# helpers for simplify_and_group
function _is_target(e, unwrapped_dvs::Set, dv_ops)
    # If it is a leaf node, check if it matches any dvendent variable directly
    if !SymbolicUtils.istree(e)
        return e in unwrapped_dvs
    end

    op = SymbolicUtils.operation(e)

    # Check if the operation matches any of our base dependent operations
    if any(isequal(op, d_op) for d_op in dv_ops)
        return true
    end

    # Support mixed derivatives by recursively checking arguments
    if op isa Differential
        args = SymbolicUtils.arguments(e)
        return _is_target(args[1], unwrapped_dvs, dv_ops)
    end

    return false
end

function _find_targets!(e, unwrapped_dvs::Set, dv_ops, targets::Set)
    # If we found a target, add it and stop recursing
    if _is_target(e, unwrapped_dvs, dv_ops)
        push!(targets, e)
        return
    end

    # Otherwise, keep digging through the expression tree
    if SymbolicUtils.istree(e)
        for arg in SymbolicUtils.arguments(e)
            _find_targets!(arg, unwrapped_dvs, dv_ops, targets)
        end
    end
end

function _diff_depth(e)
    if !SymbolicUtils.istree(e)
        return 0
    end

    # Increment depth for each Differential operation
    if SymbolicUtils.operation(e) isa Differential
        return 1 + _diff_depth(SymbolicUtils.arguments(e)[1])
    end

    return 0
end

function simplify_and_group(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))

    unwrapped_dvs = Set([unwrap(d) for d in dvs])
    dv_ops = [SymbolicUtils.operation(unwrap(d)) for d in dvs]
    targets = Set()

    # Pass the required state into the mutator function
    _find_targets!(expr, unwrapped_dvs, dv_ops, targets)

    # Sort targets safely using the external helper
    sorted_targets = sort(collect(targets), by=_diff_depth, rev=true)

    grouped_expr = 0
    remainder = expr

    for target in sorted_targets
        max_deg = Symbolics.degree(remainder)
        for p in max_deg:-1:1
            target_term = p==1 ? target : target^p
            coeff = simplify(Symbolics.coeff(remainder, target_term))

            if !isequal(coeff, 0)
                grouped_expr += coeff * wrap(target)
                remainder = simplify(remainder - coeff * target_term)
            end
        end
    end

    grouped_expr += simplify(remainder)

    return grouped_expr ~ 0
end
#endregion

#region units handling 
const SI_BASIS = [:Mass, :Length, :Time, :Temperature, :Current, :Luminosity, :Amount]

#=
if defining a custom basis with a new unit U with dimension D, then each unit in the system that has a non zero power of U needs to be redefined with U
example - defining heat as a new basis unit:

Unitful.register(@__MODULE__)
@dimension 𝐇 "𝐇" Heat
@refunit J_h "J_h" HeatJoule 𝐇 true
const Heat_Basis = vcat(SI_BASIS,[:Heat])

then defining a modified version of another unit such as Watt for this system:

@unit W_h "W_h" HeatWatt 1J_h/s true (true for automatic metric prefixes and scaling)

good practice to have the custom basis unit in the subscript of the modified unit
    =#

#helpers for nondimensionalize_pde
function has_full_dimensions(sys::PDESystem)
    symbols = vcat(sys.ivs, sys, dvs, sys.ps)
    return !any(getunit(v)===nothing for v in symbols)
end

function get_units_vector(var, basis::AbstractVector{Symbol}=SI_BASIS)
    # 1. Extract the unit and underlying dimensions
    u = ModelingToolkit.get_unit(var)
    d = dimension(u)
    dims = typeof(d).parameters[1]

    # 2. Initialize a dictionary with 0//1 for every dimension in our basis
    powers = Dict{Symbol,Rational{Int}}(dim => 0//1 for dim in basis)

    # 3. Populate the dictionary with the extracted rational powers
    for dim in dims
        dim_name = Unitful.name(dim)
        if haskey(powers, dim_name)
            powers[dim_name] = Unitful.power(dim)
        end
    end

    # 4. Extract and return the values in the exact order of the basis array
    return [powers[b] for b in basis]
end
#endregion

println("my_functions.jl ran successfully")