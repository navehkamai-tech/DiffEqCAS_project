module DiffEqCAS

# this is a CAS I'm building to handle and manipulate systems of Differential equations.
# the goal is for it to be quite general and be able to handle all systems of any order,
# with any number of equations, independent variables, dependent variables, and so forth
# in addition my aim is to leave the possibility of numeric computation open for the future,
# so design choices must be made with that in mind

using Symbolics
using LinearAlgebra
using DomainSets
using ModelingToolkit
using DynamicQuantities
using IntervalArithmetic
using IntervalBoxes
using LRUCache
using DataStructures
using TermInterface
using Base.MathConstants
using StaticArrays
using Base.Threads

import Symbolics: unwrap, wrap, jacobian, simplify, substitute, get_variables
import SymbolicUtils as SU
import SymbolicUtils: maketerm, @rule, @acrule
import Base.MathConstants as MC
# ---------------------------------------------------------------------------
# Exports
# ---------------------------------------------------------------------------
# Core Types & IDs
export NodeId, ConstraintId, EqId
export SymRelation, Constraint, Paving, DomBlock, SymDomain
export SymEquation, SeriesTerm, SeriesSum
export Locus, Face, Explicit, Interior, Limit, ExhaustiveLimit, BoundaryCondition
export Transform, XStep, XChain, IvTransform, PsTransform, DvTransform
export SimplificationOptions, Simplification
export DESys, RootSys, SolutionForm, SolutionRole, SolutionFamily, SolvedLeaf
export Node, RootNode, ActiveNode, SolvedNode, SplitNode
export Interface, Split, DomainSplit, FactorSplit, GuardSplit, DETree
export SignState, DivisState, positive, negative, iszero, either, divisible, haszero, undetermined
export ConstraintEvidence, EvidenceDomain

# Domain Operations & Paving
export domain_variables, domain_components, all_constraints, constraint_ids
export find_constraint, constraints_of, block_of, domain_evidence, relation_status, same_domain
export domain_product, add_constraints, rewrite_constraints, domain_from_constraints
export subdomain, share_blocks, is_in_domain, constraints_satisfiable
export HC4Revise, compile_hc4

# System, Tree & Display Operations
export initialize_system, new_node!, split_node!, complete_node!
export display_pde, display_expr

# Rules, Divisibility & Simplification
export @expr, Dirac, Heaviside, SPECIAL_REWRITER, normalize_expr, D
export factor_evidence, factor_sign, factor_divisibility, common_divisors
export simplify_system

# Transformations & Special Algorithms
export change_dvs!, change_ivs!, change_parameters!
export change_dvs, change_ivs, change_parameters
export custom_rewrite, get_base_op, group_coefficients, nondimensionalize_pde

# ---------------------------------------------------------------------------
# Layer 1: Foundation (Constants, Pure Utils, & All Shared Structs)
# ---------------------------------------------------------------------------
include("constants.jl")
using .Constants

include("types.jl")
include("utils.jl")

# ---------------------------------------------------------------------------
# Layer 2: Domain & satisfiability (Symbolic Topology & Paving Engine)
# ---------------------------------------------------------------------------
include("paving.jl")
include("satisfiability.jl")
include("domains.jl")

# ---------------------------------------------------------------------------
# Layer 3: Independent modules (currently only dependent on types.jl)
# ---------------------------------------------------------------------------
include("system_ops.jl")
include("display.jl")

# ---------------------------------------------------------------------------
# Layer 4: Domain-Aware Inference & Symbolic Rules
# ---------------------------------------------------------------------------
include("symbolic_rules.jl") # as per the plan the rules will each go where they belong, there won't be a unified rules file

# ---------------------------------------------------------------------------
# Layer 5: Simplification, Transformations
# ---------------------------------------------------------------------------
include("simplification.jl")
include("transformations.jl")

# final part, governs the system as a whole
include("special_algorithms.jl")
include("derivation_tree.jl")

end # module DiffEqCAS
