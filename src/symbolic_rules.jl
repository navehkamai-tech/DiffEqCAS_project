# Rules are grouped by required assumptions and pipeline stage.  The
# simplification pipeline can later select a safe group without enabling
# branch-sensitive identities globally.
const EXP_LOG_RULES = [
    @rule(~x/exp(~y) => ~x*exp(-~y)),
    @rule(exp(~x)^~n => exp(~x*~n)),
    @rule(exp(log(~x::is_positive)) => ~x),
    @rule(log(exp(~x::is_real)) => ~x),
    @rule(log(~x)+log(~y) => log(~x * ~y)),
    @rule(log(~x)-log(~y) => log(~x/~y)),
    @rule(~n*log(~x) => log(~x^~n)),
]
const POWER_RULES = [
    @rule(~z/(~x::is_divisible)^(~y) => ~z*~x^(-~y)),
    @rule(((~x::is_positive)^(~y))^(~z) => (~x)^(~y*~z)),
    @rule(sqrt((~x::is_real)^2) => abs(~x)),
]
const ABSOLUTE_VALUE_RULES = [
    @rule(abs(~x*~y) => abs(~x)*abs(~y)),
    @rule(abs((~x::is_real)^2) => (~x)^2),
    @rule(abs((~x::is_real)^(2*~n)) => (~x)^(2*~n)),
    @rule((abs(~x))^2 => (~x)^2),
    @rule((abs(~x)^(2*~n)) => (~x)^(2*~n)),
    @rule(abs(~x::is_positive) => ~x),
    @rule(abs(~x::is_negative) => -~x),
]
const TRIGONOMETRIC_RULES = [
    @rule(sin(~x+2*π) => sin(~x)),
    @rule(sin(~x+2*π*~n::is_integer) => sin(~x)),
    @rule(cos(~x+2*π) => cos(~x)),
    @rule(cos(~x+2*π*~n::is_integer) => cos(~x)),
    @rule(sin(~x)^2 => 1//2-1//2*cos(2*~x)),
    @rule(cos(~x)^2 => 1//2+1//2*cos(2*~x)),
    @rule(tan(~x) => sin(~x)/cos(~x))
]
const SYMBOLIC_RULE_GROUPS = (
    function_arguments = vcat(EXP_LOG_RULES, TRIGONOMETRIC_RULES),
    positive_domain = vcat(POWER_RULES, ABSOLUTE_VALUE_RULES),
)

# TODO: Build stage-specific rewriters from SYMBOLIC_RULE_GROUPS.  Predicates
# must prove positivity, reality, or integrality before enabling a group.

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
    @acrule(Dirac(~a::notavariable*(~x - ~c::is_number), ~n) => Dirac(~x - ~c, ~n)/(abs(~a)*(~a)^(~n))),
    @rule(~x*Dirac(~x, 0) => 0),
    @rule(~x * Dirac(~x, ~n) => -(~n)*Dirac(~x, ~n-1)),
    @rule(Integral(~vars, ~domain::is_domain)(~f * Dirac(~vars - ~c)) =>
        ~c ∈ ~domain ? substitute(~f, Dict(Symbolics.unwrap.(~vars) .=> Symbolics.unwrap.(~c))) : 0),
    @rule(Integral(~vars, ~domain::is_domain)(Dirac(~vars - ~c)) =>
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
    @rule(Integral(~vars, ~domain::is_domain)(~f*Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(~f)),
    @rule(Integral(~vars, ~domain::is_domain)(Heaviside(~expr)) => Integral(~vars, intersect(~domain, expr_to_domain(~expr, ~vars)))(1))
]

# 3. Create the single, compiled rewriter constant
const SPECIAL_REWRITER = SymbolicUtils.Postwalk(SymbolicUtils.Chain(vcat(diff_op_rules, dirac_rules, heaviside_rules)))
