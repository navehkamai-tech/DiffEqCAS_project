using ModelingToolkit
using Symbolics
using SymbolicUtils
using DomainSets

include("my_functions.jl")

@parameters t x y
@variables u(t,x,y)[1:2]

v = Dirac(Symbolics.wrap(Symbolics.unwrap([x, y])))
println("Dirac: ", simplify(SPECIAL_REWRITER(v)))
