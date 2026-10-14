module DiffEqCAS

#=
this is a CAS I'm building to handle and manipulate systems of Differential equations.
the goal is for it to be quite general and be able to handle all systems of any order, with any number of equations, independent variables, dependent variables, and so forth
in addition my aim is to have leave the possibility of numeric computation open for the future, so design choices must be made with that in mind
=#

using Symbolics, LinearAlgebra, DomainSets, ModelingToolkit, Unitful, IntervalArithmetic, IntervalBoxes, LRUCache, DataStructures, TermInterface, Base.MathConstants, StaticArrays
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils as SU
import SymbolicUtils: maketerm, @rule, @acrule
import Base.MathConstants as MC
export SymDomain, SymRelation, domain_variables, domain_components, DETree, DESys, push_branch!, complete_branch!, XStep, XChain, IvTransform, PsTransform, DvTransform, Factor, change_dvs!, change_ivs!, change_parameters!, change_dvs, change_ivs, change_parameters, group_coefficients, common_divisors, factor_divisibility, custom_rewrite, get_base_op, factor_sign, Dirac, Heaviside, Restrict, SPECIAL_REWRITER
export Simplification, simplify_system

# 0. Symbolic Constants submodule
include("constants.jl")
using .Constants

# 1. Foundational objects
include("domains.jl")
include("eqs_and_bcs.jl")
include("solutions.jl")
include("derivation_tree.jl")
include("units.jl")

include("utils.jl")
# 2. rule enforcing
include("symbolic_rules.jl")
include("display.jl")
include("divisibility.jl")

#. 3. derivation and transformation
include("simplification.jl")
include("transformations.jl")
include("special_algorithms.jl")

function __init__()
    Unitful.register(DiffEqCAS)
end

end
