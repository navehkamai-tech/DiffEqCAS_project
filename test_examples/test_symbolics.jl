using Symbolics
@register_symbolic Dirac(x::AbstractVector, n::AbstractVector)
@variables x y
println(Dirac([x, y], [0, 0]))
