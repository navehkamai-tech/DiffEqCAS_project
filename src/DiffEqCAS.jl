__precompile__(false)
module DiffEqCAS

#=
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, independent variables, dependent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
=#

using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets, ModelingToolkit, Unitful, IntervalArithmetic, IntervalBoxes, StaticArrays, LRUCache, DataStructures, Memoize, TermInterface
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule
import Base.MathConstants as MC
export SymbolicDomain, SymbolicRestriction, domain_variables, domain_components, DiffEqSystem, DiffEqBranch, push_branch!, complete_branch!, DerivationStep, DerivationHistory, CoordTransformStep, ParamTransformStep, DepVarTransformStep, FactorStep, change_dvs!, change_ivs!, change_parameters!, change_dvs, change_ivs, change_parameters, group_coefficients, common_divisors, factor_divisibility, custom_rewrite, get_base_op, get_sign, Dirac, Heaviside, Restrict, SPECIAL_REWRITER
export SimplificationStep, simplify_system

# 1. Foundational helpers
include("base.jl")
include("utils.jl")
include("domains.jl")
include("symbolic_rules.jl")
include("display.jl")
include("divisibility.jl")
include("units.jl")
include("simplification.jl")
include("transformations.jl")
include("special_algorithms.jl")

end
