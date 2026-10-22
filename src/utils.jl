
_key_variables(key) = key isa Tuple ? key : (key,)

# Symbolic values may return symbolic expressions from `==`, so use `isequal`.
_contains_equal(values, target) = any(value -> isequal(value, target), values)

_additive_terms(expr) = collect(terms(unwrap(expr)))

_multiplicative_factors(expr) = collect(Symbolics.factors(unwrap(expr)))

_as_num(v) = v isa Symbolics.Num ? v : Symbolics.wrap(v)

function _vars_of(expr)::Vector{Symbolics.Num}
    u = Symbolics.unwrap(expr)
    u isa Number && return Symbolics.Num[]
    return unique(Symbolics.Num[_as_num(v) for v in Symbolics.get_variables(u)])
end

function _push_unique!(arr, new_vals)
    for new_val in new_vals
        _contains_equal(arr, new_val) ? nothing : push!(arr, new_val)
    end
    return arr
end

function _ordered_unique(values)
    result = Any[]
    return _push_unique!(result, values)
end

function D(vars...)
    # 1. Sort the provided variables alphabetically right away
    sorted_vars = sort(collect(vars), by=string)

    # 2. Return a custom operator that nests the Differentials from the inside out
    return expr -> foldr((v, ex) -> Differential(v)(ex), sorted_vars, init=expr)
end

# Does `expr` mention a dependent variable or a derivative?
function _has_depvar_or_diff(expr, sys::DESys)
    dvs = [Symbolics.unwrap(d) for d in sys.dvs]
    walk(e) = any(d -> isequal(d, e), dvs) ||
        (SU.iscall(e) && (SU.operation(e) isa Differential || any(walk, SU.arguments(e))))
    return walk(Symbolics.unwrap(expr))
end

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

function _const_value(expr)
    v = SU.unwrap_const(Symbolics.unwrap(expr))
    return v isa Real ? v : nothing
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

function get_base_op(expr)
    if SU.iscall(expr)
        op = SU.operation(expr)
        if op == getindex
            return get_base_op(SU.arguments(expr)[1])
        end
        return op
    end
    return expr
end

"""
    _connected_groups(constraints; key=_ckey)

Split constraints into connected groups: two constraints are in the same group
when they share a variable, directly or through other constraints. Constraints
with no variables each form their own group.

Duplicates (same `key`) are dropped. Within a group, constraints are ordered by
their key, and the groups themselves are ordered by their smallest key, so the
result is deterministic and independent of the input order.

Returns a vector of `(constraints, variables, keys)` named tuples, where
`variables` is the group's unique variables in order of first appearance and
`keys` are the constraint keys in the same order as `constraints`.
"""
function _connected_groups(constraints; key=_ckey)
    seen = Set{UInt64}()
    cs = Constraint[]
    ks = UInt64[]
    for c in constraints
        k = key(c)
        k in seen && continue
        push!(seen, k)
        push!(cs, c)
        push!(ks, k)
    end

    n = length(cs)
    parent = collect(1:n)
    function find(i)
        while parent[i] != i
            parent[i] = parent[parent[i]]
            i = parent[i]
        end
        return i
    end

    cvars = [_vars_of(c.relation.residual) for c in cs]
    owner = Dict{Symbolics.Num,Int}()
    for i in 1:n, v in cvars[i]
        j = get!(owner, v, i)
        j == i || (parent[find(i)] = find(j))
    end

    groups = Dict{Int,Vector{Int}}()
    for i in 1:n
        push!(get!(groups, find(i), Int[]), i)
    end

    result = NamedTuple{(:constraints, :variables, :keys),
        Tuple{Vector{Constraint},Vector{Symbolics.Num},Vector{UInt64}}}[]
    for idxs in values(groups)
        sort!(idxs, by=i -> ks[i])
        vars = Symbolics.Num[]
        varset = Set{Symbolics.Num}()
        for i in idxs, v in cvars[i]
            v in varset || (push!(varset, v); push!(vars, v))
        end
        push!(result, (constraints=cs[idxs], variables=vars, keys=ks[idxs]))
    end
    sort!(result, by=g -> first(g.keys))
    return result
end

function _count_nodes(node)
    count = 1

    if hasmethod(TermInterface.isexpr, Tuple{typeof(node)}) && TermInterface.isexpr(node)
        count += sum(_count_nodes(c) for c in TermInterface.children(node); init=0)
    elseif SU.iscall(node)
        count += sum(_count_nodes(c) for c in SU.arguments(node); init=0)
    end

    return count
end

robust_node_count(expr) = _count_nodes(Symbolics.unwrap(expr))

# ---------------------------------------------------------------------------
# 1. Relation utils
# ---------------------------------------------------------------------------

function _symbol_to_relation(sym::Symbol)
    sym === _LT && return (<)
    sym === _LE && return (<=)
    sym === _GT && return (>)
    sym === _GE && return (>=)
    sym === _EQ && return (==)
    sym === _NE && return (!=)
    throw(ArgumentError("unsupported relation symbol: $sym"))
end

_get_relation(rel::SymRelation) = _symbol_to_relation(rel.relation)

function _holds(rel::Symbol, val::Real)::Bool
    rel === _LT && return val < 0
    rel === _LE && return val <= 0
    rel === _GT && return val > 0
    rel === _GE && return val >= 0
    rel === _EQ && return val == 0
    rel === _NE && return val != 0
    throw(ArgumentError("unsupported relation: $rel"))
end

function _eq_from_rel(rel::SymRelation)
    _get_relation(rel) !== (==) && return nothing
    return Symbolics.Equation(rel.residual, 0)
end

Symbolics.simplify(rel::SymRelation) = SymRelation(simplify(rel.residual), rel.relation)
Symbolics.expand(rel::SymRelation) = SymRelation(expand(rel.residual), rel.relation)

function _relation_symbol(op; error_message="unsupported relation:")
    complete_error_message = "$(error_message) $op"
    if op isa Symbol
        op ∈ _RELATIONS || throw(ArgumentError(complete_error_message))
        return op
    end
    op === (!=) && return _NE
    op === (>) && return _GT
    op === (>=) && return _GE
    op === (<) && return _LT
    op === (<=) && return _LE
    op === (==) && return _EQ
    throw(ArgumentError(complete_error_message))
end

function _flip_relation(rel::Symbol)
    rel === _LT && return _GT
    rel === _LE && return _GE
    rel === _GT && return _LT
    rel === _GE && return _LE
    return rel
end

function _negate_relation(rel::Symbol)
    rel === _LT && return _GE
    rel === _LE && return _GT
    rel === _GT && return _LE
    rel === _GE && return _LT
    rel === _EQ && return _NE
    rel === _NE && return _EQ
    throw(ArgumentError("unsupported relation: $rel"))
end

# Bitmask of allowed signs for residual: bit 1 = (< 0), bit 2 = (== 0), bit 3 = (> 0)
function _rel_mask(s::Symbol)::UInt8
    s === _LT && return 0b001
    s === _LE && return 0b011
    s === _EQ && return 0b010
    s === _GE && return 0b110
    s === _GT && return 0b100
    s === _NE && return 0b101
    throw(ArgumentError("unsupported relation: $s"))
end

function _mask_to_rel(m::UInt8)::Symbol
    m == 0b001 && return _LT
    m == 0b011 && return _LE
    m == 0b010 && return _EQ
    m == 0b110 && return _GE
    m == 0b100 && return _GT
    m == 0b101 && return _NE
    throw(ArgumentError("invalid or trivial relation mask: $m"))
end

function _numeric_factor(term)
    u = Symbolics.unwrap(term)
    val = SU.unwrap_const(u)
    val isa Real && return val
    if SU.iscall(u) && SU.operation(u) === (*)
        for arg in SU.arguments(u)
            v = SU.unwrap_const(arg)
            v isa Real && return v
        end
    end
    return 1
end

# units

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


#------------------------------------------
# Paving & cache
#------------------------------------------

clear_cache!() = empty!(cache)
resize_cache!(n::Integer) = (cache_size[]=n; resize!(cache; maxsize=n))

# Anything derived with paving depends on these global settings.
_env() = (ROI[], tolerance[])

# Key constructors. Every block / context key in the file is built here only.
# Constraint key: content hash of residual + relation (no Ids, no printing).
_ckey(c::Constraint) = hash(Symbolics.unwrap(c.relation.residual), hash(c.relation.relation))
# Block key: hash of its constraint keys, which must already be in canonical order.
_comp_key(constraint_keys) = hash(Tuple(constraint_keys))
# Parameter key: the keys of its constraints (constraints are kept sorted by key).
_pkey(constraints) = Tuple(c.key for c in constraints)
# Context key: the keys of its blocks (blocks are kept sorted by key).
_ctx_key(comps, params) = Tuple((c.key for c in comps)..., _pkey(params))
# A context made of exactly one block.
_ctx_key(comp::Comp) = (comp.key,)


const _EMPTY_CTX = Ctx(Comp[], Constraint[], ())
