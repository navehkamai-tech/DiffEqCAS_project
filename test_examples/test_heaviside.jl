using ModelingToolkit
using Symbolics
using SymbolicUtils
using DomainSets

include("my_functions.jl")

@parameters t x y
@variables u(t,x,y)[1:2]

h = Heaviside([x, y])
println("Heaviside: ", simplify(SPECIAL_REWRITER(h)))
