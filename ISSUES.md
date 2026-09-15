# Open Issues in my_functions.jl

## 1. Mismatch in `DiffEq` struct `domain` vs `domains` field
- **Description:** The `DiffEq` struct definition declares `domain::DomainSets.Domain`, but the constructor assigns `new(eqs, indeps, deps, params, bcs, domains)` (where `domains` is a `Vector{Pair{Any,DomainSets.Domain}}`), and `addtodiffeq` tries to access `sys.domains`. This causes a type error/mismatch upon instantiation.
- **Location:** `struct DiffEq` definition (around line 14).

## 2. Generalize `Dirac` function sifting rules
- **Description:** The sifting rule for the Dirac Delta function (`@rule(Integral(...)(~f*Dirac(...)) => ...)`) needs to be generalized to handle Dirac functions of more than one variable.
- **Location:** `special_rewriter(params)` function, under `dirac_rules` (comment: `*needs to be generalized for Dirac functions of more than one variable later on`).

## 3. Rework integration rules to use `IntervalSets.jl`
- **Description:** The integration rules for `Heaviside` currently use `DomainSets.Interval`. There is a note that all integration rules need to be reworked using Intervals from `IntervalSets.jl`.
- **Location:** `special_rewriter(params)` function, under `heaviside_rules` (comment: `*all need to be reworked using Intervals from IntervalSets.jl`).

## 4. Update `change_independents` to use `transform_domains`
- **Description:** The `change_independents` function needs to be updated to utilize the `transform_domains` helper function to handle domain transformations correctly when changing independent variables.
- **Location:** `change_independents` function (comment: `*needs to be updated to use transform_domains`).

## 5. Ambiguity in `addtodiffeq` for domains
- **Description:** The `addtodiffeq` function throws an `ArgumentError("Domain additions are ambiguous. Use \`change_domain\` instead.")` when `field == :domain || field == :domains`. This behavior is a workaround, and a more robust way to handle domain modifications might be needed.
- **Location:** `addtodiffeq` function.
