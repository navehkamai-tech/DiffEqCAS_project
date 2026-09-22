__precompile__(false)
module DiffEqCAS

using Symbolics, LinearAlgebra, SymbolicUtils, DomainSets, ModelingToolkit, Unitful, IntervalArithmetic
import IntervalConstraintProgramming as ICP
import Symbolics: unwrap, wrap, jacobian, simplify, substitute
import SymbolicUtils: maketerm, @rule, @acrule
import ModelingToolkit: PDESystem

export change_dvs, get_base_op, custom_rewrite, get_units, get_sign

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
