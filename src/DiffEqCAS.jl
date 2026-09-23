__precompile__(false)
module DiffEqCAS

#=
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, independent variables, dependent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
=#

using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets, ModelingToolkit, Unitful, IntervalArithmetic, IntervalBoxes, StaticArrays
import IntervalConstraintProgramming as ICP
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule
import ModelingToolkit: PDESystem

export change_dvs, change_ivs, change_parameters, simplify_and_group, custom_rewrite, get_base_op, get_sign, Dirac, Heaviside, Restrict, SPECIAL_REWRITER

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

#=
future additions: 
1) a good CAS shows the steps of how it found something. so I need to figure out how to do that
2) maybe use MathTeXEngine.jl or sympy.parsing.latex to turn latex into the right kind of expressions needed for input, which would allow to input latex into the system.
=#