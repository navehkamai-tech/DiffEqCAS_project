# DiffEqCAS.jl

`DiffEqCAS` is a Computer Algebra System (CAS) built in Julia, specifically designed to handle and manipulate general systems of Differential Equations.

## Goals and Design Philosophy

The primary goal of this package is to be highly general: it is built to handle differential equation systems of any order, with any number of equations, independent variables, dependent variables, and parameters.

Furthermore, `DiffEqCAS` is designed with the possibility of numerical computation open for the future. Design choices in the symbolic representation and transformations have been made with this compatibility in mind, ensuring a seamless bridge between symbolic manipulation and eventual numerical solvers.

## Core Features

Built on top of the robust Julia symbolic ecosystem (`Symbolics.jl`, `ModelingToolkit.jl`, and `SymbolicUtils.jl`), `DiffEqCAS` provides high-level tools to manipulate `ModelingToolkit.PDESystem`s.

- **Transformations and Substitutions**: Easily perform coordinate transformations and variable substitutions on entire PDE systems.
  - `change_ivs`: Transform independent variables (e.g., Cartesian to Polar coordinates).
  - `change_dvs`: Substitute or transform dependent variables.
  - `change_parameters`: Substitute parameters within systems.
- **Simplification and Manipulation**:
  - `simplify_and_group`: Group terms in equations by derivatives or dependent variables.
  - `custom_rewrite`: Advanced rewriting traversing expression trees.
- **Special Functions and Domains**:
  - Support for generalized functions in differential equations, such as `Dirac` and `Heaviside`.
  - `Restrict`: Handle domain restrictions.
- **Units and Dimensional Analysis**:
  - Foundational support for unit tracking and nondimensionalization of PDE systems.

## Main Exports

```julia
using DiffEqCAS

# Transformation functions
change_dvs, change_ivs, change_parameters

# Simplification
simplify_and_group, custom_rewrite

# Utilities
get_base_op, get_sign

# Special Functions
Dirac, Heaviside, Restrict, SPECIAL_REWRITER
```

## Structure

- `src/utils.jl`, `src/domains.jl`: Foundational helpers and domain management.
- `src/symbolic_rules.jl`: Core symbolic logic and rewrite rules.
- `src/simplification.jl`, `src/units.jl`, `src/display.jl`: Modules for simplification, unit handling, and display.
- `src/transformations.jl`, `src/special_algorithms.jl`: High-level operations for PDESystem transformations and specialized algorithms (currently essentially empty, but planned to employ advanced simplification methods relying on symmetry and integration techniques).

## Testing and Examples

Example usage and tests can be found in the `test_examples/` directory. These scripts can be run individually to see the various transformation and simplification capabilities in action:

```bash
julia --project=. test_examples/test_dirac.jl
```
