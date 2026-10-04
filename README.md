# DiffEqCAS.jl

> **Disclaimer:** This is an amateur hobby project, and it is uncertain how far it will be developed. It is currently a work in progress and is still far from fully functional.

`DiffEqCAS` is a Computer Algebra System (CAS) built in Julia, specifically designed to handle and manipulate general systems of Differential Equations.

## Goals and Design Philosophy

The primary goal of this package is to be highly general: it is built to handle differential equation systems of any order, with any number of equations, independent variables, dependent variables, and parameters.

Furthermore, `DiffEqCAS` is designed to be used in tandem with numerical methods and as part of a computational pipeline. The module itself aims to stay away from numerical computation as much as possible, but is built to interface nicely with numerical SciML differential equation solver packages. Design choices in the symbolic representation and transformations have been made with this compatibility in mind, ensuring a seamless bridge between symbolic manipulation and numerical solvers.

## Core Features

Built on top of the robust Julia symbolic ecosystem (`Symbolics.jl`, `ModelingToolkit.jl`, and `SymbolicUtils.jl`), `DiffEqCAS` provides high-level tools to manipulate its own custom `DiffEqSystem` representations, which are designed to support branching and derivation history.

- **System and Branch Tracking**:
  - `DiffEqSystem` encapsulates equations, domain, and dependent/independent variables across potentially multiple branches of solutions.
  - `DiffEqBranch` and `SymbolicRestriction` store branch-specific equations, domains, derivation history, and restrictions.
  - `DerivationHistory` meticulously records transformations, variable changes, and simplifications that led to a specific branch.
- **Transformations and Substitutions**: Easily perform coordinate transformations and variable substitutions on entire PDE systems. Both non-mutating (e.g., `change_ivs`) and in-place mutating (e.g., `change_ivs!`) versions are provided.
  - `change_ivs`: Transform independent variables (e.g., Cartesian to Polar coordinates).
  - `change_dvs`: Substitute or transform dependent variables.
  - `change_parameters`: Substitute parameters within systems.
- **Simplification, Manipulation, and Divisibility**:
  - `simplify_system`: Run a robust simplification pipeline on entire systems and branches.
  - `group_coefficients`: Group terms in equations by derivatives or dependent variables.
  - `custom_rewrite`: Advanced rewriting traversing expression trees.
  - `factor_divisibility` and `common_divisors`: Utilities for factor splitting and identifying divisibility amongst complex symbolic expressions.
- **Special Functions and Domains**:
  - Support for generalized functions in differential equations, such as `Dirac` and `Heaviside`.
  - `Restrict`: Handle domain restrictions.
- **Units and Dimensional Analysis**:
  - Foundational support for unit tracking and nondimensionalization of PDE systems.
- **Symbolic Domains**:
  - `SymbolicDomain` stores inspectable variable/constraint pairs for symbolic rules and transformations.
  - Connected components are preserved as domain components; numerical interval boxes remain a separate derived cache.

## Main Exports

```julia
using DiffEqCAS

# Core Structures
DiffEqSystem, DiffEqBranch, SymbolicDomain, SymbolicRestriction, domain_variables, domain_components, push_branch!, complete_branch!
DerivationStep, DerivationHistory, CoordTransformStep, ParamTransformStep, DepVarTransformStep, FactorStep, SimplificationStep

# Transformation functions
change_dvs!, change_ivs!, change_parameters!
change_dvs, change_ivs, change_parameters

# Simplification and Divisibility
simplify_system, group_coefficients, custom_rewrite, common_divisors, factor_divisibility

# Utilities
get_base_op, get_sign

# Special Functions
Dirac, Heaviside, Restrict, SPECIAL_REWRITER
```

## Structure

- `src/base.jl`: Core structures for `DiffEqSystem`, `DiffEqBranch`, `SymbolicDomain`, and history tracking.
- `src/utils.jl`, `src/domains.jl`: Foundational helpers and domain management.
- `src/symbolic_rules.jl`: Core symbolic logic and rewrite rules.
- `src/divisibility.jl`: Architectures for factor splitting and divisibility.
- `src/simplification.jl`, `src/units.jl`, `src/display.jl`: Modules for simplification pipelines, unit handling, and display.
- `src/transformations.jl`, `src/special_algorithms.jl`: High-level operations for transformations and specialized algorithms (currently essentially empty, but planned to employ advanced simplification methods relying on symmetry and integration techniques).

## Testing and Examples

Example usage and tests can be found in the `test_examples/` directory. These scripts can be run individually to see the various transformation and simplification capabilities in action:

```bash
julia --project=. test_examples/test_dirac.jl
```
