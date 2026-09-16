#=
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, independent variables, dependent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
=#
using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule


struct DiffEq
    eqs::Vector{Symbolics.Equation}
    indeps::Vector{Symbolics.Num}
    deps::Vector{Symbolics.Num}
    params::Vector{Symbolics.Num}
    bcs::Vector{Symbolics.Equation}
    domains::Pair{Any,DomainSets.Domain}

    function DiffEq(
        eqs::Vector{Symbolics.Equation},
        indeps::Vector{Symbolics.Num},
        deps::Vector{Symbolics.Num},
        params::Vector{Symbolics.Num}=Symbolics.Num[],
        bcs::Vector{Symbolics.Equation}=Symbolics.Equation[],
        domains::Vector{Pair{Any,DomainSets.Domain}}=Pair{Any,DomainSets.Domain}[] # Default to an empty array
    )
        # If the user provides no domains, automatically fallback to mapping 
        # every independent variable to the entire real line
        if isempty(domains)
            domains = [var::Any => DomainSets.FullSpace(Float64) for var in indeps]
        end

        new(eqs, indeps, deps, params, bcs, domains)
    end
end

# struct helpers
function build_system(eqs::Vector{Symbolics.Equation}, deps::Vector{Symbolics.Num}, bcs::Vector{Symbolics.Equation}=Symbolics.Equation[]) #
    indeps_set = Set{Symbolics.Num}()
    for dep in deps
        unwrapped_dep = unwrap(dep)
        # Check if it's a function like u(x, t)
        if SymbolicUtils.istree(unwrapped_dep)
            args = SymbolicUtils.arguments(unwrapped_dep)
            # Wrap the arguments back into Symbolics.Num and store them
            union!(indeps_set, wrap.(args))
        else
            throw(ArgumentError("Dependent variables must be defined as functions, e.g., u(x, t)"))
        end
    end

    indeps = collect(indeps_set)
    params = extract_parameters(Tuple(vcat(eqs, bcs)), vcat(indeps, deps)) #[cite: 1]

    return DiffEq(eqs, indeps, deps, params, bcs) #[cite: 1]
end

function addtodiffeq(sys::DiffEq, field::Symbol, addition::Vector)
    if field == :domain || field == :domains
        throw(ArgumentError("Domain additions are ambiguous. Use `change_domain` instead."))
    end

    # Create new vectors by concatenating the addition if the field matches, 
    # otherwise retain the existing data from the struct[cite: 1].
    new_eqs = field == :eqs ? vcat(sys.eqs, addition) : sys.eqs
    new_indeps = field == :indeps ? vcat(sys.indeps, addition) : sys.indeps
    new_deps = field == :deps ? vcat(sys.deps, addition) : sys.deps
    new_params = field == :params ? vcat(sys.params, addition) : sys.params
    new_bcs = field == :bcs ? vcat(sys.bcs, addition) : sys.bcs

    # Rebuild and return the new struct
    # (Assuming you updated DiffEq to include the `domains` field as previously discussed)
    return DiffEq(new_eqs, new_indeps, new_deps, new_params, new_bcs, sys.domains)
end

function change_domain(sys::DiffEq, new_domains::Vector{Pair})
    # completely overwrite the domains field while preserving everything else
    return DiffEq(sys.eqs, sys.indeps, sys.deps, sys.params, sys.bcs, new_domains)
end

function D(var::Symbolics.Num, order::Int)
    return Differential(var, order)
end

#defining special functions
#Dirac Delta function
@register_symbolic Dirac(x::Symbolics.Num, n::Int)
@register_symbolic Dirac(x::Symbolics.Num)
@register_symbolic Dirac(x::AbstractVector, n::AbstractVector)
@register_symbolic Dirac(x::AbstractVector)

#Heaviside step function
@register_symbolic Heaviside(x::Real)

# metadata structs
struct VariableUnit end
struct ParameterSign end

function build_variable(name::Symbol, unit)
    v = Symbolics.unwrap(first(@variables $name))
    return Symbolics.wrap(Symbolics.setmetadata(v, VariableUnit, unit))
end

function build_parameter(name::Symbol, unit, sign::Symbol=:both)
    p = Symbolics.unwrap(first(@variables $name))
    p = Symbolics.setmetadata(p, VariableUnit, unit)
    p = Symbolics.setmetadata(p, ParameterSign, sign)
    return Symbolics.wrap(p)
end

function get_unit(x)
    Symbolics.getmetadata(Symbolics.unwrap(x), VariableUnit)
end

function get_sign(x)
    unwrapped = Symbolics.unwrap(x)
    if unwrapped isa Real
        return unwrapped > 0 ? :positive : unwrapped < 0 ? :negative : :zero
    end
    if Symbolics.hasmetadata(unwrapped, ParameterSign)
        return Symbolics.getmetadata(unwrapped, ParameterSign)
    end
    return :both
end

function special_rewriter(params=[])
    is_scalar(x) = any(isequal(x, p) for p in params) || x isa Number

    function is_array_literal(x)
        return SymbolicUtils.istree(x) && SymbolicUtils.operation(x) === SymbolicUtils.array_literal
    end

    dirac_rules = [
        #multivariate rules
        @rule(Dirac(~x) => is_array_literal(~x) ? prod([Symbolics.unwrap(Dirac(Symbolics.wrap(el), 0)) for el in SymbolicUtils.arguments(~x)[2:end]]) : nothing),
        @rule(Dirac(~x, ~n) => (is_array_literal(~x) && ~n isa AbstractArray) ? prod([Symbolics.unwrap(Dirac(Symbolics.wrap(el_x), el_n)) for (el_x, el_n) in zip(SymbolicUtils.arguments(~x)[2:end], ~n)]) : nothing),
        #rule for easier definition
        @rule(Dirac(~x) => !is_array_literal(~x) ? Symbolics.unwrap(Dirac(Symbolics.wrap(~x), 0)) : nothing),
        #algebraic rules
        @rule(Dirac(-(~x), ~n) => (-1)^(~n)*Symbolics.unwrap(Dirac(Symbolics.wrap(~x), ~n))),
        @acrule(Dirac(~a::is_scalar * ~x, ~n) => Symbolics.unwrap(Dirac(Symbolics.wrap(~x), ~n)) / (abs(~a) * (~a)^(~n))),
        @acrule(Dirac(~a::is_scalar*(~x - ~c::Number), ~n) => Symbolics.unwrap(Dirac(Symbolics.wrap(~x - ~c), ~n))/(abs(~a)*(~a)^(~n))),
        @acrule(~x*Dirac(~x, 0) => 0),
        @acrule(~x * Dirac(~x, ~n) => -(~n)*Symbolics.unwrap(Dirac(Symbolics.wrap(~x), ~n-1))),
        #sifting rules
        # *needs to be generalized for Dirac functions of more than one variable later on
        @rule(Integral(~var::Symbolics.Num, ~domain::DomainSets.Domain)(~f*Dirac(~var - ~c, ~n)) => ~c ∈ ~domain ? substitute((-1)^(~n)*expand_derivatives(Differential(~var, ~n)((~f))), Dict(~var => ~c)) : 0),
        @rule(Integral(~var::Symbolics.Num, ~domain::DomainSets.Domain)(Dirac(~var - ~c, ~n)) => (~c ∈ ~domain)&&((~n)==0) ? 1 : 0),
        #derivative rule
        @rule(Differential(~var, ~k)(Dirac(~var, ~n)) => Dirac(~var, ~n+~k))
    ]
    heaviside_rules = [
        #algebraic rules
        @rule(Heaviside(-1 * ~x) => 1 - Symbolics.unwrap(Heaviside(Symbolics.wrap(~x)))),
        @acrule(Heaviside(~a * ~x) => begin
            sign_a = get_sign(Symbolics.wrap(~a))
            if sign_a == :positive
                Symbolics.unwrap(Heaviside(Symbolics.wrap(~x)))
            elseif sign_a == :negative
                1 - Symbolics.unwrap(Heaviside(Symbolics.wrap(~x)))
            elseif sign_a == :zero
                0.5
            else
                nothing
            end
        end),
        @rule(Heaviside(~x)^~k => begin
            if ~k isa Real && ~k > 0
                Symbolics.unwrap(Heaviside(Symbolics.wrap(~x)))
            else
                nothing
            end
        end),
        #derivative rules
        @rule(Differential(~var, ~n)(Heaviside(~var)) => Dirac(~var, ~n-1)),
        @rule(Differential(~var, ~n)(Heaviside(~var - ~c::is_scalar)) => Dirac(~var - ~c, ~n-1)),
        #integration rules:
        # *all need to be reworked using Intervals from IntervalSets.jl
        @rule(Integral(~var::Symbolics.Num, ~domain::DomainSets.Interval)(~f*Heaviside(~var)) =>
            0<=~domain[1] ? nothing :
            0>=~domain[2] ? 0 :
            Integral(~var::Symbolics.Num, (0, ~domain[2]))(~f)),
        @rule(Integral(~var::Symbolics.Num, ~interval::DomainSets.Interval)(~f * Heaviside(~var - ~c::Real)) =>
            ~c >= ~domain[2] ? 0 :
            ~c <= ~domain[1] ? Integral(~var, ~domain)(~f) :
            Integral(~var, (~c, ~domain[2]))(~f)),
        @rule(Integral(~var::Symbolics.Num, ~domain::DomainSets.Interval)(Heaviside(~var)) =>
            0<=~domain[1] ? 0 :
            0>=~domain[2] ? nothing :
            ~domain[2]),
        @rule(Integral(~var::Symbolics.Num, ~domain::DomainSets.Interval)(Heaviside(~var - ~c::Real)) =>
            ~c >= ~domain[2] ? 0 :
            ~c <= ~domain[1] ? ~domain[2] - ~domain[1] :
            ~domain[2] - ~c)
    ]

    combined_rules = vcat(dirac_rules, heaviside_rules)
    return SymbolicUtils.Postwalk(SymbolicUtils.Chain(combined_rules))
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

#parameter helper - gives full list of parameters appearing in system of equations
function extract_parameters(list::Tuple, nonparams::Vector{Symbolics.Num})
    symbols = Symbolics.Num[]
    for i in list
        if i isa Symbolics.Equation
            vars = collect(Symbolics.get_variables(unwrap(i.lhs - i.rhs)))
            append!(symbols, vars)
        elseif i isa Symbolics.Num
            vars = collect(Symbolics.get_variables(unwrap(i)))
            append!(symbols, vars)
        else
            println(i)
            throw(ArgumentError("cannot extract parameters from $(typeof(i))"))
        end
    end

    unique_vars = unique(symbols)
    known_vars = unwrap.(nonparams)
    # Filter out known nonparams AND any expression that is a tree (like a Differential)
    params = filter(unique_vars) do v
        val = unwrap(v)
        is_known = any(isequal(val, k) for k in known_vars)

        !is_known && !SymbolicUtils.istree(val)
    end

    # Return as Vector{Symbolics.Num} to match your struct definition
    return convert(Vector{Symbolics.Num}, wrap.(params))
end

#for just changing parameters
function change_parameters(DiffEqInput::DiffEq, param_mapping::Dict)
    # Pass 1: Raw substitution without the special rewriter
    substituted_eqs = [wrap(substitute(eq.lhs - eq.rhs, param_mapping)) for eq in DiffEqInput.eqs]
    substituted_bcs_lhs = [wrap(substitute(bc.lhs, param_mapping)) for bc in DiffEqInput.bcs]
    substituted_bcs_rhs = [wrap(substitute(bc.rhs, param_mapping)) for bc in DiffEqInput.bcs]

    # Pass 2: Extract NEW parameters directly from the expressions
    # Leveraging your ability to pass Symbolics.Num directly into the tuple
    exprs_tuple = Tuple(vcat(substituted_eqs, substituted_bcs_lhs, substituted_bcs_rhs))
    new_params = extract_parameters(exprs_tuple, vcat(DiffEqInput.indeps, DiffEqInput.deps)) #[cite: 1]

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

    return DiffEq(transformed_eqs, DiffEqInput.indeps, DiffEqInput.deps, new_params, transformed_bcs) #[cite: 1]
end

#helper for change_independents - recursively traverses expression trees
function custom_rewrite(expr, var_map, J_inv, new_indeps, old_u, new_u, dep_funcs, cache=Dict())
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
    if any(isequal(op, d) for d in dep_funcs)
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
            rewritten_arg = custom_rewrite(args[1], var_map, J_inv, new_indeps, old_u, new_u, dep_funcs, cache)

            res = chain_rule(J_inv, idx, new_indeps, rewritten_arg, diff_order)
            cache[expr] = res
            return res
        end
    end

    new_args = [custom_rewrite(a, var_map, J_inv, new_indeps, old_u, new_u, dep_funcs, cache) for a in args]

    if all(a === b for (a, b) in zip(args, new_args))
        cache[expr] = expr
        return expr
    end
    res = maketerm(typeof(expr), op, new_args, nothing)
    cache[expr] = res
    return res
end

#helper for change_independents - changes domain Dict 
function transform_domains(old_domains::Vector{Pair}, indep_mapping::Dict, new_indeps::Vector{Symbolics.Num})
    new_domain_pairs = Pair[]

    for (old_vars, dom) in old_domains
        # Normalize the key to a tuple for uniform processing
        var_tuple = old_vars isa Tuple ? old_vars : (old_vars,)

        # Check if any variable in this specific domain block is being mapped
        if any(haskey(indep_mapping, v) for v in var_tuple)

            # 1. Grab the substitution expressions (e.g., [r*cos(θ), r*sin(θ)])
            exprs = [get(indep_mapping, v, v) for v in var_tuple]

            # 2. Find all unique new variables present in these expressions
            found_vars = Set{Symbolics.Num}()
            for expr in exprs
                union!(found_vars, Symbolics.get_variables(Symbolics.unwrap(expr)))
            end

            # Preserve the strict ordering defined by the user in `new_indeps`
            new_vars = Tuple(filter(v -> v in found_vars, new_indeps))

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

# *needs to be updated to use transform_domains
function change_independents(DiffEqInput::DiffEq, new_indeps, indep_mapping::Dict)
    indep_exprs = Symbolics.Num[]
    for old_indep in DiffEqInput.indeps
        if haskey(indep_mapping, old_indep)
            push!(indep_exprs, indep_mapping[old_indep])
        else
            # Fallback: if the user omits a variable from the dictionary, keep it unchanged
            push!(indep_exprs, old_indep)
        end
    end

    replaced_old_indeps = collect(keys(indep_mapping))
    # Keep old variables that do not appear in the dictionary keys
    kept_old_indeps = setdiff(DiffEqInput.indeps, replaced_old_indeps)

    final_indeps = vcat(kept_old_indeps, new_indeps)
    old_u = unwrap.(DiffEqInput.indeps)
    new_u = unwrap.(new_indeps)
    dep_funcs = [SymbolicUtils.operation(unwrap(dep)) for dep in DiffEqInput.deps]
    params = extract_parameters(Tuple(vcat(DiffEqInput.eqs, DiffEqInput.bcs, indep_exprs)), vcat(final_indeps, DiffEqInput.deps, DiffEqInput.indeps))

    J_inv = compute_J_inv(indep_exprs, new_indeps)
    var_map = Dict(old_u .=> unwrap.(indep_exprs))
    dr = special_rewriter(params)

    transformed_eqs = Symbolics.Equation[]
    for eq in DiffEqInput.eqs
        lhs_expr = eq.lhs - eq.rhs
        lhs_u = unwrap(lhs_expr)
        rewritten_lhs = custom_rewrite(lhs_u, var_map, J_inv, new_indeps, old_u, new_u, dep_funcs)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(rewritten_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end
    transformed_bcs = Symbolics.Equation[]
    for bc in DiffEqInput.bcs
        # Transform LHS and RHS separately to maintain equations like u(0, y) ~ 1
        rewritten_lhs = custom_rewrite(unwrap(bc.lhs), var_map, J_inv, new_indeps, old_u, new_u, dep_funcs)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(rewritten_lhs))))

        rewritten_rhs = custom_rewrite(unwrap(bc.rhs), var_map, J_inv, new_indeps, old_u, new_u, dep_funcs)
        simplified_rhs = simplify(dr(expand_derivatives(wrap(rewritten_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end

    new_domains = transform_domains(DiffEqInput.domains, indep_mapping, new_indeps)

    new_deps = [Symbolics.wrap(SymbolicUtils.term(op, Symbolics.unwrap.(new_indeps)...)) for op in dep_funcs]
    return DiffEq(transformed_eqs, final_indeps, new_deps, params, transformed_bcs, new_domains)
end

#helper for change_dependents - recursively traverses expression trees
function substitute_dependents(expr, old_dep_ops, dep_exprs, indeps, cache=Dict())
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
    idx = findfirst(isequal(op), old_dep_ops)
    if idx !== nothing
        # Map the independent variables to whatever arguments are currently inside the function
        # For u(0, t), this maps x => 0 and t => t
        arg_sub = Dict(wrap.(indeps) .=> wrap.(args))

        # Substitute these arguments into the corresponding new dependent expression
        # For f(x, t) + g(x, t), this yields f(0, t) + g(0, t)
        res = unwrap(substitute(wrap(dep_exprs[idx]), arg_sub))

        cache[expr] = res
        return res
    end

    # Recursively apply to arguments (drilling into Differential operators)
    new_args = [substitute_dependents(a, old_dep_ops, dep_exprs, indeps, cache) for a in args]

    # Reconstruct the tree if any arguments changed
    if all(a === b for (a, b) in zip(args, new_args))
        cache[expr] = expr
        return expr
    end

    res = maketerm(typeof(expr), op, new_args, nothing)
    cache[expr] = res
    return res
end

function change_dependents(DiffEqInput::DiffEq, new_deps::Vector{Symbolics.Num}, dep_mapping::Dict)
    # 1. Align expressions with the existing dependency order
    dep_exprs = Symbolics.Num[]
    for old_dep in DiffEqInput.deps
        if haskey(dep_mapping, old_dep)
            push!(dep_exprs, dep_mapping[old_dep])
        else
            push!(dep_exprs, old_dep)
        end
    end

    replaced_old_deps = collect(keys(dep_mapping))
    kept_old_deps = setdiff(DiffEqInput.deps, replaced_old_deps)

    final_deps = vcat(kept_old_deps, new_deps)

    indeps = unwrap.(DiffEqInput.indeps)
    old_dep_ops = [SymbolicUtils.operation(unwrap(dep)) for dep in DiffEqInput.deps]
    u_dep_exprs = unwrap.(dep_exprs)
    params = extract_parameters(Tuple(vcat(DiffEqInput.eqs, DiffEqInput.bcs, dep_exprs)), vcat(DiffEqInput.indeps, final_deps))
    dr = special_rewriter(params)

    transformed_eqs = Symbolics.Equation[]
    for eq in DiffEqInput.eqs
        # Move to LHS and unwrap
        lhs_expr = unwrap(eq.lhs - eq.rhs)

        # Traverse and forcefully substitute inside Differentials
        substituted_lhs = substitute_dependents(lhs_expr, old_dep_ops, u_dep_exprs, indeps)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(substituted_lhs))))

        push!(transformed_eqs, simplified_lhs ~ 0)
    end

    transformed_bcs = Symbolics.Equation[]
    for bc in DiffEqInput.bcs
        substituted_lhs = substitute_dependents(unwrap(bc.lhs), old_dep_ops, u_dep_exprs, indeps)
        simplified_lhs = simplify(dr(expand_derivatives(wrap(substituted_lhs))))

        substituted_rhs = substitute_dependents(unwrap(bc.rhs), old_dep_ops, u_dep_exprs, indeps)
        simplified_rhs = simplify(dr(expand_derivatives(wrap(substituted_rhs))))

        push!(transformed_bcs, simplified_lhs ~ simplified_rhs)
    end

    # Passing DiffEqInput.params assuming you want to retain the original params block manually
    return DiffEq(transformed_eqs, DiffEqInput.indeps, new_deps, DiffEqInput.params, transformed_bcs)
end

# helpers for simplify_and_group
function _is_target(e, deps::Vector{Symbolics.Num}, dep_ops)
    # If it is a leaf node, check if it matches any dependent variable directly
    if !SymbolicUtils.istree(e)
        return any(isequal(e, unwrap(d)) for d in deps)
    end

    op = SymbolicUtils.operation(e)

    # Check if the operation matches any of our base dependent operations
    if any(isequal(op, d_op) for d_op in dep_ops)
        return true
    end

    # Support mixed derivatives by recursively checking arguments
    if op isa Differential
        args = SymbolicUtils.arguments(e)
        return _is_target(args[1], deps, dep_ops)
    end

    return false
end

function _find_targets!(e, deps::Vector{Symbolics.Num}, dep_ops, targets::Set)
    # If we found a target, add it and stop recursing
    if _is_target(e, deps, dep_ops)
        push!(targets, e)
        return
    end

    # Otherwise, keep digging through the expression tree
    if SymbolicUtils.istree(e)
        for arg in SymbolicUtils.arguments(e)
            _find_targets!(arg, deps, dep_ops, targets)
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

# main function
function simplify_and_group(eq::Symbolics.Equation, deps::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))

    dep_ops = [SymbolicUtils.operation(unwrap(d)) for d in deps]
    targets = Set()

    # Pass the required state into the mutator function
    _find_targets!(expr, deps, dep_ops, targets)

    # Sort targets safely using the external helper
    sorted_targets = sort(collect(targets), by=_diff_depth, rev=true)

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