# DiffEqCAS.jl

> **Disclaimer:** This is an amateur hobby project, and it is uncertain how far it will be developed. It is currently a work in progress and is still far from fully functional.

`DiffEqCAS` is a Computer Algebra System (CAS) built in Julia, specifically designed to handle and manipulate general systems of Differential Equations (ODEs and PDEs of any order, with arbitrary independent/dependent variables, parameters, domains, and boundary conditions).

## Goals and Design Philosophy

The primary goal of this package is to be highly general: it is built to handle differential equation systems of any order, with any number of equations, independent variables, dependent variables, and parameters.

Furthermore, `DiffEqCAS` is designed to be used in tandem with numerical methods and as part of a computational pipeline. The module itself aims to stay away from numerical computation as much as possible, but is built to interface nicely with numerical SciML differential equation solver packages (such as `ModelingToolkit.jl` and `Symbolics.jl`). Design choices in the symbolic representation and transformations have been made with this compatibility in mind, ensuring a seamless bridge between symbolic manipulation and numerical solvers.

## Core Features

Built on top of the robust Julia symbolic ecosystem (`Symbolics.jl`, `ModelingToolkit.jl`, `SymbolicUtils.jl`, `DomainSets.jl`, `IntervalBoxes.jl`, and `IntervalArithmetic.jl`), `DiffEqCAS` provides high-level tools to manipulate differential equation systems, track derivation trees, perform domain satisfiability analysis, and execute coordinate transformations.

- **Tree-Based Derivation Graph (`DETree`)**:
  - `DETree` encapsulates the overall solution derivation tree composed of nodes (`RootNode`, `ActiveNode`, `SolvedNode`, `SplitNode`) and an active node queue.
  - `DESys` stores active branch-specific context including independent variables (`ivs`), dependent variables (`dvs`), parameters (`ps`), equations (`eqs`), boundary conditions (`bcs`), domain (`domain`), parameter constraints (`ps_constraints`), and domain restrictions (`restrictions`).
  - `SolvedLeaf` encapsulates completed solution branches with `SolutionFamily` (supporting explicit, implicit, or parametric forms; general, particular, or singular roles; series solution representations via `SeriesSum`/`SeriesTerm`; and degrees of freedom `dofs`).
  - `SplitNode` tracks domain and factor case splits (`DomainSplit`, `FactorSplit`, `GuardSplit`) along with interface boundary conditions (`Interface`) matching solutions across split branches.
  - `XChain` and `XStep` record derivation histories and transformation chains (`IvTransform`, `PsTransform`, `DvTransform`, `Simplification`).
- **Symbolic Domains & Interval Paving Engine**:
  - `SymDomain` stores Cartesian-product domain blocks (`DomBlock`) coupling variables and constraints with stable constraint identifiers (`ConstraintId`).
  - `SymRelation` canonicalizes residuals (`residual ⋈ 0`) and relation types (`:d`, `:i`, `:p`, `:t`, `:f`).
  - Interval box paving engine (`Paving`) with contractor propagation (`HC4Revise`, `compile_hc4`) and interval arithmetic.
  - Satisfiability and sign inference engine (`satisfiability.jl`) checking constraint satisfiability (`constraints_satisfiable`, `is_in_domain`), computing sign and zero evidence (`domain_evidence`), and utilizing LRU context caching (`Ctx`, `Comp`).
- **Algebra & Divisibility Analysis**:
  - Bounded algebraic expansion (`bounded_expand` with `ExpansionLimits`) protecting against node explosion during expansion and simplification passes.
  - Divisibility and sign inference utilities (`factor_evidence`, `factor_sign`, `factor_divisibility`, `common_divisors`).
- **Transformations and Substitutions**:
  - Coordinate transformations and variable substitutions on PDE/ODE systems with both non-mutating (e.g., `change_ivs`, `change_dvs`, `change_parameters`) and in-place mutating (e.g., `change_ivs!`, `change_dvs!`, `change_parameters!`) versions.
- **Simplification and Specialized Algorithms**:
  - `simplify_system`: System-wide simplification pipeline configured via `SimplificationOptions`.
  - `nondimensionalize_pde`: Automated nondimensionalization of differential equation systems.
  - `group_coefficients`: Term grouping by derivatives or dependent variables.
  - `custom_rewrite`: Advanced expression tree rewriting.
- **Special Functions, Operators, and Boundary Conditions**:
  - Generalized function support (`Dirac`, `Heaviside`), derivative operator `D`, and `SPECIAL_REWRITER`.
  - Boundary conditions (`BoundaryCondition`) with formal loci representations (`Face`, `Explicit`, `Interior`, `Limit`, `ExhaustiveLimit`).

## Main Exports

```julia
using DiffEqCAS

# Core Types & Identifiers
NodeId, ConstraintId, EqId
SymRelation, Constraint, Paving, DomBlock, SymDomain
SymEquation, SeriesTerm, SeriesSum
Locus, Face, Explicit, Interior, Limit, ExhaustiveLimit, BoundaryCondition
Transform, XStep, XChain, IvTransform, PsTransform, DvTransform
SimplificationOptions, Simplification
DESys, RootSys, SolutionForm, SolutionRole, SolutionFamily, SolvedLeaf
Node, RootNode, ActiveNode, SolvedNode, SplitNode
Interface, Split, DomainSplit, FactorSplit, GuardSplit, DETree
SignState, DivisState, positive, negative, iszero, either, divisible, haszero, undetermined
ConstraintEvidence, EvidenceDomain

# Domain Operations, Satisfiability & Paving
domain_variables, domain_components, all_constraints, constraint_ids
find_constraint, constraints_of, block_of, domain_evidence, relation_status, same_domain
domain_product, add_constraints, rewrite_constraints, domain_from_constraints
subdomain, share_blocks, is_in_domain, constraints_satisfiable
HC4Revise, compile_hc4

# System, Tree & Display Operations
initialize_system, new_node!, split_node!, complete_node!
display_pde, display_expr

# Rules, Divisibility & Simplification
@expr, Dirac, Heaviside, SPECIAL_REWRITER, normalize_expr, D
factor_evidence, factor_sign, factor_divisibility, common_divisors
simplify_system

# Transformations & Specialized Algorithms
change_dvs!, change_ivs!, change_parameters!
change_dvs, change_ivs, change_parameters
custom_rewrite, get_base_op, group_coefficients, nondimensionalize_pde
```

## Structure

- `src/constants.jl`: System constants and mathematical definitions.
- `src/types.jl`: Core structs, type definitions, identifiers, relations, domains, derivation nodes, solution families, and evidence types.
- `src/utils.jl`: Helper utilities for symbolic expressions, AST manipulation, and tree operations.
- `src/paving.jl`: Interval arithmetic, box paving engine (`Paving`), and HC4 constraint propagation contractors (`HC4Revise`, `compile_hc4`).
- `src/satisfiability.jl`: Constraint satisfiability checker (`constraints_satisfiable`), context caching (`Ctx`, `Comp`), and domain evidence inference (`domain_evidence`).
- `src/domains.jl`: `SymDomain` management, Cartesian product operations, block factorizations, and constraint manipulations.
- `src/system_ops.jl`: System initialization (`initialize_system`) and tree node transitions (`new_node!`, `split_node!`, `complete_node!`).
- `src/display.jl`: Pretty-printing for PDEs, expressions, and derivation trees (`display_pde`, `display_expr`).
- `src/symbolic_rules.jl`: Special functions (`Dirac`, `Heaviside`), derivative operator `D`, and `SPECIAL_REWRITER`.
- `src/algebra.jl`: Bounded algebraic expansion (`bounded_expand`), factor evidence, sign inference (`factor_sign`), divisibility analysis (`factor_divisibility`), and common divisor extraction.
- `src/simplification.jl`: Pipeline for system and equation simplification (`simplify_system`).
- `src/transformations.jl`: High-level operations for coordinate transformations and variable substitutions (`change_ivs`, `change_dvs`, `change_parameters`).
- `src/special_algorithms.jl`: Nondimensionalization (`nondimensionalize_pde`), term grouping (`group_coefficients`), and custom expression rewrites.
- `src/derivation_tree.jl`: Tree structure navigation, parent-child branch management, node transitions, and derivation history tracking.

## Testing and Examples

Unit tests and verification examples are located in the `test/` directory. The test suite can be run using Julia's package manager:

```bash
julia --project=. -e 'using Pkg; Pkg.test()'
```

Individual test files can also be run directly:

```bash
julia --project=. test/test_satisfiability_paving.jl
```
