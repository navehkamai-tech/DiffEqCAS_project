#=
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, ivendent variables, dvendent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
=#
using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets, ModelingToolkit, Unitful
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule

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

function special_rewriter()
    notavariable(x) = ModelingToolkit.isparameter(x) || ModelingToolkit.isconstant(x) || x isa Number

    function is_array_literal(x)
        return SymbolicUtils.istree(x) && SymbolicUtils.operation(x) === SymbolicUtils.array_literal
    end

    diff_op_rules = [
        @rule(Differential(~y)(Differential(~x)(~f)) =>
            string(~x) < string(~y) ? Differential(~x)(Differential(~y)(~f)) : nothing)
    ]
    dirac_rules = [
        #multivariate rules
        @rule(Dirac(~x) => is_array_literal(~x) ? prod([Symbolics.unwrap(Dirac(Symbolics.wrap(el), 0)) for el in SymbolicUtils.arguments(~x)[2:end]]) : nothing),
        @rule(Dirac(~x, ~n) => (is_array_literal(~x) && ~n isa AbstractArray) ? prod([Symbolics.unwrap(Dirac(Symbolics.wrap(el_x), el_n)) for (el_x, el_n) in zip(SymbolicUtils.arguments(~x)[2:end], ~n)]) : nothing),
        #rule for easier definition
        @rule(Dirac(~x) => Dirac(~x, 0)),
        #algebraic rules
        @rule(Dirac(-(~x), ~n) => (-1)^(~n)*Dirac(~x, ~n)),
        @acrule(Dirac(~a::notavariable * ~x, ~n) => Dirac(~x, ~n) / (abs(~a) * (~a)^(~n))),
        @acrule(Dirac(~a::notavariable*(~x - ~c::Number), ~n) => Dirac(~x - ~c, ~n)/(abs(~a)*(~a)^(~n))),
        @rule(~x*Dirac(~x, 0) => 0),
        @rule(~x * Dirac(~x, ~n) => -(~n)*Dirac(~x, ~n-1)),
        #sifting rules
        @rule(Integral(~vars, ~domain::DomainSets.Domain)(~f * Dirac(~vars - ~c)) =>
            ~c ∈ ~domain ? substitute(~f, Dict(Symbolics.unwrap.(~vars) .=> Symbolics.unwrap.(~c))) : 0),
        @rule(Integral(~vars, ~domain::DomainSets.Domain)(Dirac(~vars - ~c)) =>
            ~c ∈ ~domain ? 1 : 0),
        #derivative rule
        @rule(Differential(~var, ~k)(Dirac(~var, ~n)) => Dirac(~var, ~n+~k))
    ]
    heaviside_rules = [
        #algebraic rules
        @rule(Heaviside(-(~x)) => 1-Heaviside(~x)),
        @acrule(Heaviside(~a::notavariable * ~x) => Heaviside(~x) where (get_sign(~a) == positive)),
        @acrule(Heaviside(~a::notavariable * ~x) => 1 - Heaviside(~x) where (get_sign(~a) == negative)),
        @rule(Heaviside(~x)^~k::notavariable => Heaviside(~x) where (get_sign(~k)) == positive),
        #derivative rules
        @rule(Differential(~var, ~n)(Heaviside(~var)) => Dirac(~var, ~n-1)),
        @rule(Differential(~var, ~n)(Heaviside(~var - ~c::is_scalar)) => Dirac(~var - ~c, ~n-1)),
        #integration rules:
        @rule(Integral(~vars, ~domain::DomainSets.Domain)(~f*Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(~f)),
        @rule(Integral(~vars, ~domain::DomainSets.Domain)(Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(1))
    ]

    combined_rules = vcat(dirac_rules, heaviside_rules)
    return SymbolicUtils.Postwalk(SymbolicUtils.Chain(combined_rules))
end

#shorthand for creating Differentials
function D(vars...)
    # 1. Sort the provided variables alphabetically right away
    sorted_vars = sort(collect(vars), by=string)

    # 2. Return a custom operator that nests the Differentials from the inside out
    return expr -> foldr((v, ex) -> Differential(v)(ex), sorted_vars, init=expr)
end

#generic helpers
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
        # Unwrap for the next iteration to maintain type consistency
        term = next_term
    end
    return unwrap(term)
end

function expr_to_domain(expr, vars)
    vars_array = vars isa AbstractVector ? Symbolics.unwrap.(vars) : [Symbolics.unwrap(vars)]
    # Similar to your transform_domains logic[cite: 1]
    expr_unwrapped = Symbolics.unwrap(expr)
    func_expr, _ = Symbolics.build_function(expr_unwrapped, vars_array, expression=Val{false})

    # SuperlevelSet(f, c) creates the domain where f(x) >= c
    return DomainSets.SuperlevelSet(x -> func_expr(collect(x)), 0.0)
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

display_pde(expr) = display_expr(expr)

function display_pde(eq::Symbolics.Equation)
    return display_expr(eq.lhs) ~ display_expr(eq.rhs)
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

#for just changing parameters
function change_parameters(sys::DiffEq, param_mapping::Dict)
    # Pass 1: Raw substitution without the special rewriter
    substituted_eqs = [wrap(substitute(eq.lhs - eq.rhs, param_mapping)) for eq in sys.eqs]
    substituted_bcs_lhs = [wrap(substitute(bc.lhs, param_mapping)) for bc in sys.bcs]
    substituted_bcs_rhs = [wrap(substitute(bc.rhs, param_mapping)) for bc in sys.bcs]

    # Pass 2: Extract NEW parameters directly from the expressions
    # Leveraging your ability to pass Symbolics.Num directly into the tuple
    exprs_tuple = Tuple(vcat(substituted_eqs, substituted_bcs_lhs, substituted_bcs_rhs))
    new_params = extract_parameters(exprs_tuple, vcat(sys.ivs, sys.dvs)) #[cite: 1]

    # Pass 3: Initialize the rewriter with the updated parameter list and apply it
    dr = special_rewriter(new_params)

    transformed_eqs = Symbolics.Equation[]
    for seq in substituted_eqs
        push!(transformed_eqs, simplify(dr(seq)) ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for (slhs, srhs) in zip(substituted_bcs_lhs, substituted_bcs_rhs)
        push!(transformed_bcs, simplify(dr(slhs)) ~ simplify(dr(srhs)))
    end
    # *need to add a helper function for getting the new domains
    return DiffEq(transformed_eqs, sys.ivs, sys.dvs, new_params, transformed_bcs, new_domains) #[cite: 1]
end

#helper for change_ivendents - recursively traverses expression trees
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

    # Intercept dvendent variables (e.g., changing u(x,y) to u(r,θ))
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

#helper for change_ivendents - changes domain Dict 
function transform_domains(old_domains::Vector{Pair}, iv_mapping::Dict, new_ivs::Vector{Symbolics.Num})
    new_domain_pairs = Pair[]

    for (old_vars, dom) in old_domains
        # Normalize the key to a tuple for uniform processing
        var_tuple = old_vars isa Tuple ? old_vars : (old_vars,)

        # Check if any variable in this specific domain block is being mapped
        if any(haskey(iv_mapping, v) for v in var_tuple)

            # 1. Grab the substitution expressions (e.g., [r*cos(θ), r*sin(θ)])
            exprs = [get(iv_mapping, v, v) for v in var_tuple]

            # 2. Find all unique new variables present in these expressions
            found_vars = Set{Symbolics.Num}()
            for expr in exprs
                union!(found_vars, Symbolics.get_variables(Symbolics.unwrap(expr)))
            end

            # Preserve the strict ordering defined by the user in `new_ivs`
            new_vars = Tuple(filter(v -> v in found_vars, new_ivs))

            # 3. Compile a numeric function: F(new_vars) -> old_vars
            # We must unwrap to work directly with SymbolicUtils expressions
            exprs_unwrapped = Symbolics.unwrap.(exprs)
            new_vars_unwrapped = Symbolics.unwrap.(new_vars)

            # build_function creates an executable Julia function out of the AST
            func_expr, _ = Symbolics.build_function(exprs_unwrapped, collect(new_vars_unwrapped), expression=Val{false})

            # DomainSets prefers functions that take vectors/tuples as single arguments
            forward_map = x -> func_expr(collect(x))

            # 4. Wrap the old domain via its pre-image
            # MappedDomain(f, d) represents all points x such that f(x) ∈ d.
            new_dom = DomainSets.MappedDomain(forward_map, dom)

            # 5. Push to the new array, flattening the key if it's 1D
            new_key = length(new_vars) == 1 ? new_vars[1] : new_vars
            push!(new_domain_pairs, new_key => new_dom)

        else
            # If no mapping affects this block, pass it through unchanged
            push!(new_domain_pairs, old_vars => dom)
        end
    end

    return new_domain_pairs
end

function change_ivs(sys::DiffEq, new_ivs, iv_mapping::Dict)
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
    dr = special_rewriter(params)

    transformed_eqs = Symbolics.Equation[]
    for eq in sys.eqs
        lhs_expr = eq.lhs - eq.rhs
        lhs_u = unwrap(lhs_expr)
        rewritten_lhs = custom_rewrite(lhs_u, var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(rewritten_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end
    transformed_bcs = Symbolics.Equation[]
    for bc in sys.bcs
        # Transform LHS and RHS separately to maintain equations like u(0, y) ~ 1
        rewritten_lhs = custom_rewrite(unwrap(bc.lhs), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(rewritten_lhs))))

        rewritten_rhs = custom_rewrite(unwrap(bc.rhs), var_map, J_inv, new_ivs, old_u, new_u, dv_funcs)
        simplified_rhs = simplify(dr(expand_derivatives(wrap(rewritten_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end

    new_domains = transform_domains(sys.domains, iv_mapping, new_ivs)

    new_dvs = [Symbolics.wrap(SymbolicUtils.term(op, Symbolics.unwrap.(new_ivs)...)) for op in dv_funcs]
    return DiffEq(transformed_eqs, final_ivs, new_dvs, params, transformed_bcs, new_domains)
end

#helper for change_dvendents - recursively traverses expression trees
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

    # Check if the operation matches one of our old dvendent variables (e.g., 'u' or 'v')
    idx = findfirst(isequal(op), old_dv_ops)
    if idx !== nothing
        # Map the ivendent variables to whatever arguments are currently inside the function
        # For u(0, t), this maps x => 0 and t => t
        arg_sub = Dict(wrap.(ivs) .=> wrap.(args))

        # Substitute these arguments into the corresponding new dvendent expression
        # For f(x, t) + g(x, t), this yields f(0, t) + g(0, t)
        res = unwrap(substitute(wrap(dv_exprs[idx]), arg_sub))

        cache[expr] = res
        return res
    end

    # Recursively apply to arguments (drilling into Differential operators)
    new_args = [substitute_dvendents(a, old_dv_ops, dv_exprs, ivs, cache) for a in args]

    # Reconstruct the tree if any arguments changed
    if all(a === b for (a, b) in zip(args, new_args))
        cache[expr] = expr
        return expr
    end

    res = maketerm(typeof(expr), op, new_args, nothing)
    cache[expr] = res
    return res
end

function change_dvs(sys::DiffEq, new_dvs::Vector{Symbolics.Num}, dv_mapping::Dict)
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
    dr = special_rewriter(params)

    transformed_eqs = Symbolics.Equation[]
    for eq in sys.eqs
        # Move to LHS and unwrap
        lhs_expr = unwrap(eq.lhs - eq.rhs)

        # Traverse and forcefully substitute inside Differentials
        substituted_lhs = substitute_dvs(lhs_expr, old_dv_ops, u_dv_exprs, ivs)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(substituted_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for bc in sys.bcs
        substituted_lhs = substitute_dvendents(unwrap(bc.lhs), old_dv_ops, u_dv_exprs, ivs)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(substituted_lhs))))

        substituted_rhs = substitute_dvendents(unwrap(bc.rhs), old_dv_ops, u_dv_exprs, ivs)
        simplified_rhs = simplify(dr(expand_derivatives(wrap(substituted_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end
    params = extract_parameters(Tuple(vcat(sys.eqs, sys.bcs, dv_exprs)))

    # Passing sys.params assuming you want to retain the original params block manually
    return PDESystem(transformed_eqs, sys.ivs, final_dvs, params, transformed_bcs)
end

# helpers for simplify_and_group
function _is_target(e, dvs::Vector{Symbolics.Num}, dv_ops)
    # If it is a leaf node, check if it matches any dvendent variable directly
    if !SymbolicUtils.istree(e)
        return ModelingToolkit.isvariable(e)
    end

    op = SymbolicUtils.operation(e)

    # Check if the operation matches any of our base dvendent operations
    if any(isequal(op, d_op) for d_op in dv_ops)
        return true
    end

    # Support mixed derivatives by recursively checking arguments
    if op isa Differential
        args = SymbolicUtils.arguments(e)
        return _is_target(args[1], dvs, dv_ops)
    end

    return false
end

function _find_targets!(e, dvs::Vector{Symbolics.Num}, dv_ops, targets::Set)
    # If we found a target, add it and stop recursing
    if _is_target(e, dvs, dv_ops)
        push!(targets, e)
        return
    end

    # Otherwise, keep digging through the expression tree
    if SymbolicUtils.istree(e)
        for arg in SymbolicUtils.arguments(e)
            _find_targets!(arg, dvs, dv_ops, targets)
        end
    end
end

function _diff_depth(e)
    if !SymbolicUtils.istree(e)
        return 0
    end

    # Increment dvth for each Differential operation
    if SymbolicUtils.operation(e) isa Differential
        return 1 + _diff_dvth(SymbolicUtils.arguments(e)[1])
    end

    return 0
end

# main function
function simplify_and_group(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))

    dv_ops = [SymbolicUtils.operation(unwrap(d)) for d in dvs]
    targets = Set()

    # Pass the required state into the mutator function
    _find_targets!(expr, dvs, dv_ops, targets)

    # Sort targets safely using the external helper
    sorted_targets = sort(collect(targets), by=_diff_dvth, rev=true)

    grouped_expr = 0
    remainder = expr

    for target in sorted_targets
        coeff = simplify(expand_derivatives(Differential(target)(remainder)))

        if !isequal(coeff, 0)
            grouped_expr += coeff * wrap(target)
            remainder = simplify(remainder - coeff * target)
        end
    end

    grouped_expr += simplify(remainder)

    return grouped_expr ~ 0
end

println("my_functions.jl ran successfully")