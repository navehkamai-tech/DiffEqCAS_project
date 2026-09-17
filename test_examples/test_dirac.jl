using Symbolics
using SymbolicUtils
import SymbolicUtils: @rule, @acrule

include("my_functions.jl")

@variables x y

params = []
println(SymbolicUtils.istree(Symbolics.unwrap(x + 1)))
println(SymbolicUtils.operation(Symbolics.unwrap(x + 1)))
println(SymbolicUtils.operation(Symbolics.unwrap(x + 1)) === SymbolicUtils.array_literal)
println(SymbolicUtils.operation(Symbolics.unwrap([x, y])) === SymbolicUtils.array_literal)
