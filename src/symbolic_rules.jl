
#defining sign metadata for symbols
@enum SignState positive negative undetermined
struct VariableSign end
Symbolics.option_to_metadata_type(::Val{:sign}) = VariableSign

function get_sign(var)
    var_unwrapped = Symbolics.unwrap(var)

    if var_unwrapped isa Real
        return var_unwrapped > 0 ? positive : (var_unwrapped < 0 ? negative : undetermined)
    end

    return Symbolics.getmetadata(var_unwrapped, VariableSign, undetermined)
end

#operator used for boundary conditions
@register_symbolic Restrict(expr, domain)
SymbolicUtils.promote_symtype(::typeof(Restrict), _...) = Real

#defining special functions
#Dirac Delta function
@register_symbolic Dirac(x::AbstractVector, n::Any)
@register_symbolic Dirac(x::AbstractVector)
@register_symbolic Dirac(x::Symbolics.Num, n::Int)
@register_symbolic Dirac(x::Symbolics.Num)
#@register_symbolic Dirac(x::Symbolics.Arr, n::Any)
#@register_symbolic Dirac(x::Symbolics.Arr)


#Heaviside step function
@register_symbolic Heaviside(x::AbstractVector)
@register_symbolic Heaviside(x::Symbolics.Num)
@register_symbolic Heaviside(x::Symbolics.Arr)
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
    @rule(Differential(~var, ~n)(Heaviside(~var - ~c::notavariable)) => Dirac(~var - ~c, ~n-1)),
    @rule(Integral(~vars, ~domain::DomainSets.Domain)(~f*Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(~f)),
    @rule(Integral(~vars, ~domain::DomainSets.Domain)(Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(1))
]

# 3. Create the single, compiled rewriter constant
const SPECIAL_REWRITER = SymbolicUtils.Postwalk(SymbolicUtils.Chain(vcat(diff_op_rules, dirac_rules, heaviside_rules)))
