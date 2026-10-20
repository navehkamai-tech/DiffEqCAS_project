
function _get_relation(rel::SymRelation)
    relation = rel.relation
    relation === Symbol("!=") && return !=
    relation === :> && return >
    relation === Symbol(">=") && return >=
    relation === :< && return <
    relation === Symbol("<=") && return <=
    relation === Symbol("==") && return ==
end

function _eq_from_rel(rel::SymRelation)
    _get_relation(rel) !== (==) && return nothing
    return Symbolics.Equation(rel.residual, 0)
end

Symbolics.simplify(rel::SymRelation) = SymRelation(simplify(rel.residual), rel.relation)
Symbolics.expand(rel::SymRelation) = SymRelation(expand(rel.residual), rel.relation)

function _relation_symbol(op)
    op === (!=) && return Symbol("!=")
    op === (>) && return :>
    op === (>=) && return Symbol(">=")
    op === (<) && return :<
    op === (<=) && return Symbol("<=")
    op === (==) && return Symbol("==")
    throw(ArgumentError("unsupported domain relation: $op"))
end

# `x > 1`  ->  SymRelation(x - 1, :>)
function SymRelation(expr::Symbolics.Num)
    unwrapped = Symbolics.unwrap(expr)
    SU.iscall(unwrapped) ||
        throw(ArgumentError("must be an expression"))
    SU.operation(unwrapped) ∈ (<, >, ≤, ≥, ==, !=) ||
        throw(ArgumentError("a SymRelation must be a relation such as `x > 0`, got $expr"))
    lhs, rhs = SU.arguments(unwrapped)
    return SymRelation(wrap(lhs) - wrap(rhs), _relation_symbol(SU.operation(unwrapped)))
end

# ---------------------------------------------------------------------------
# 1. Relation Negation & Same-Residual Algebra
# ---------------------------------------------------------------------------

function _negate_relation(rel::SymRelation)
    s = rel.relation
    s === :> && return SymRelation(rel.residual, Symbol("<="))
    s === Symbol(">=") && return SymRelation(rel.residual, :<)
    s === :< && return SymRelation(rel.residual, Symbol(">="))
    s === Symbol("<=") && return SymRelation(rel.residual, :>)
    s === Symbol("!=") && return SymRelation(rel.residual, Symbol("=="))
    s === Symbol("==") && return SymRelation(rel.residual, Symbol("!="))
    throw(ArgumentError("unsupported relation: $s"))
end

# Bitmask of allowed signs for residual: bit 1 = (< 0), bit 2 = (== 0), bit 3 = (> 0)
function _rel_mask(s::Symbol)::UInt8
    s === :< && return 0b001
    s === Symbol("<=") && return 0b011
    s === Symbol("==") && return 0b010
    s === Symbol(">=") && return 0b110
    s === :> && return 0b100
    s === Symbol("!=") && return 0b101
    throw(ArgumentError("unsupported relation: $s"))
end

function _mask_to_rel(m::UInt8)::Symbol
    m == 0b001 && return :<
    m == 0b011 && return Symbol("<=")
    m == 0b010 && return Symbol("==")
    m == 0b110 && return Symbol(">=")
    m == 0b100 && return :>
    m == 0b101 && return Symbol("!=")
    throw(ArgumentError("invalid or trivial relation mask: $m"))
end

# helpers for SymRelation
function _flip_relation_symbol(rel::Symbol)
    rel === :< && return :>
    rel === :> && return :<
    rel === Symbol("<=") && return Symbol(">=")
    rel === Symbol(">=") && return Symbol("<=")
    return rel # == and != are symmetric
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

function _canonicalize_relation(residual, rel_sym::Symbol)
    expr = Symbolics.unwrap(simplify(expand(wrap(residual))))
    val = SU.unwrap_const(expr)
    val isa Real && return (wrap(sign(val)), rel_sym)

    vars = Symbolics.get_variables(expr)
    isempty(vars) && return (wrap(expr), rel_sym)

    # Prefer true independent variables over parameters/constants, sorted alphabetically
    ivs = filter(v -> !ModelingToolkit.isparameter(Symbolics.unwrap(v)) &&
        !ModelingToolkit.isconstant(Symbolics.unwrap(v)), vars)
    target_vars = isempty(ivs) ? vars : ivs
    sort!(target_vars, by=string)
    lead_var = Symbolics.unwrap(first(target_vars))

    # Extract coefficient of highest power of `lead_var`
    deg = Symbolics.degree(expr, lead_var)
    lead_term = deg > 0 ? Symbolics.coeff(expr, deg == 1 ? lead_var : lead_var^deg) : expr
    c = _numeric_factor(lead_term)

    if c isa Real && !iszero(c)
        # Normalize magnitude and force leading numeric coefficient to be positive
        expr = simplify(expand(wrap(expr) / abs(c)))
        if c < 0
            expr = simplify(expand(-expr))
            rel_sym = _flip_relation_symbol(rel_sym)
        end
    else
        expr = wrap(expr)
    end
    return (expr, rel_sym)
end
