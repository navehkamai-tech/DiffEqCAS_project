module DiffEqCAS
"""
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, independent variables, dependent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
"""
using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets, ModelingToolkit, Unitful, IntervalArithmetic
import IntervalConstraintProgramming as ICP
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule
import ModelingToolkit: PDESystem

# 1. Foundational helpers
include("utils.jl")
include("domains.jl")

# 2. Core symbolic logic
include("symbolic_rules.jl")

# 3. Independent modules
include("display.jl")
include("simplification.jl")
include("units.jl")

# 4. High-level operations
include("transformations.jl")
include("special_algorithms.jl")

end