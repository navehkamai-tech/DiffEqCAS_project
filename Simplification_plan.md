# DiffEqCAS Simplification Plan

This document is the implementation template for the simplification architecture
of `DiffEqCAS`. It describes three layers with increasing semantic power:

1. **Layer 1: local equation simplification**
2. **Layer 2: assumption-aware simplification**
3. **Layer 3: system reduction**

The layers are deliberately separate. A caller can request only safe local
normalization, while higher layers may use domain facts, branch creation, or
relationships between equations. Every higher layer may call the layers below
it, but lower layers must not silently inspect or modify sibling equations.

The target is not one universal "simplest" representation. The default
representation is a deterministic residual equation:

```text
canonical_residual ~ 0
```

with derivatives and polynomial differential generators collected where valid,
nonlinear differential subexpressions preserved as atoms, and all accepted
domain changes recorded explicitly.

## 1. Architecture and guarantees

### 1.1 Layer responsibilities

| Layer | Input context | Main result | Allowed semantic power |
| --- | --- | --- | --- |
| Local | One equation, its boundary condition, and branch metadata | Stable canonical residual | Algebraic rewrites that preserve the current equation on its current domain |
| Assumption-aware | One branch plus `SymbolicDomain` and restrictions | Simplified branch, side conditions, or split branches | Nonzero cancellation and branch-sensitive identities only after proof |
| System reduction | A complete `DiffEqSystem` | Equivalent reduced system or explicitly branched systems | Substitution, elimination, redundancy removal, and selected differential consequences |

The implementation should expose separate public or semi-public entry points:

```julia
simplify_equation(eq, context; options...)
simplify_branch(branch; options...)
simplify_system(sys; options...)
```

`SimplificationOptions` can remain the common configuration object, but options
should be grouped by capability rather than becoming unrelated boolean flags.
Suggested groups are `LocalOptions`, `AssumptionOptions`, and
`SystemReductionOptions`, with a convenience constructor for the normal profile.

### 1.2 Core invariants

Every transformation must satisfy these invariants:

1. **Residual invariant:** equations are internally represented as
   `lhs - rhs ~ 0`.
2. **Metadata invariant:** independent variables, dependent variables,
   parameters, boundary conditions, domains, restrictions, and history survive
   every transformation.
3. **Conservatism invariant:** unsupported expression structure is preserved,
   not guessed at or replaced by a success-shaped fallback.
4. **Domain invariant:** cancelling a factor or applying a branch-sensitive
   identity requires a proof or creates a recorded side condition.
5. **Termination invariant:** every loop has both a fixed-point test and a
   resource bound.
6. **Determinism invariant:** equivalent accepted inputs use stable ordering for
   terms, factors, generators, equations, and metadata.
7. **Traceability invariant:** transformations that change a branch or its
   assumptions produce a `DerivationStep`.

### 1.3 Shared data structures

The current `DiffEqBranch`, `DiffEqSystem`, `SymbolicDomain`,
`DerivationHistory`, and `SimplificationStep` are the foundation. The following
records should be added or refined as implementation proceeds.

```julia
struct SimplificationContext
    branch::DiffEqBranch
    generators::Vector{Symbolics.Num}
    assumptions::AssumptionSet
    atom_table::AtomTable
    complexity::ComplexityBudget
end

struct AssumptionSet
    domain::SymbolicDomain
    restrictions::Vector{Any}
    proven_facts::Vector{ProofFact}
end

struct ProofFact
    proposition::Any
    status::Symbol       # :proven, :disproven, or :unknown
    method::Symbol
    evidence::Any
end

struct FactorCandidate
    expression::Symbolics.Num
    multiplicity::Int
    source::Symbol       # :numeric, :polynomial, :common_divisor, ...
    proof::Union{Nothing,ProofFact}
end

struct DifferentialAtom
    expression::Symbolics.Num
    order::Int
    kind::Symbol         # :generator, :nonlinear, :opaque
end

struct ComplexityBudget
    max_nodes::Int
    max_derivative_expansion_nodes::Int
    max_local_passes::Int
    max_system_passes::Int
    max_branches::Int
end
```

`DifferentialAtom` is essential. A term such as `exp(u')` is not a polynomial
in `u'`; it must remain an opaque nonlinear differential atom unless a
specialized rule explicitly handles it.

### 1.4 Shared helper interfaces

The layers should share narrow helpers instead of duplicating symbolic logic:

```julia
_residual(eq) -> Symbolics.Num
_as_equation(residual) -> Symbolics.Equation
_collect_differential_generators(expr, generators)
_classify_differential_structure(expr, generators)
_normalize_equation_sides(eq, context)
_canonical_fingerprint(expr_or_branch)
_complexity(expr) -> Int
_preserves_residual(candidate, original, context) -> Bool
_prove_nonzero(expr, assumptions) -> ProofFact
_make_branch(branch; equations, assumptions, step)
```

Use `Symbolics.unwrap` and `Symbolics.wrap` at API boundaries consistently.
Use `SymbolicUtils.istree`, `operation`, and `arguments` for structural
inspection, while preserving existing domain-specific utilities such as
`expand_derivatives`, `SPECIAL_REWRITER`, `common_divisors`,
`factor_divisibility`, and `group_coefficients`.

## 2. Layer 1: local equation simplification

### 2.1 Role and contract

Layer 1 simplifies one equation without using other equations as facts and
without changing its domain. It is the safe default for every input.

Its contract is:

```text
simplify_equation(eq, context)
    -> one equivalent canonical equation, or a classified identity/contradiction
```

The target is a collected residual, not necessarily a solved equation and not
necessarily a permanently factored equation.

### 2.2 Local pipeline

```text
input equation or boundary condition
    |
    v
normalize to residual F = lhs - rhs
    |
    v
expand derivatives under a complexity budget
    |
    v
normalize arithmetic and distribute selected products
    |
    v
classify differential generators and nonlinear differential atoms
    |
    v
collect only valid polynomial generator occurrences
    |
    v
simplify coefficients and ordinary subexpressions
    |
    v
apply safe structural/special-function rewrites
    |
    v
recollect and canonicalize
    |
    v
classify identity, contradiction, or ordinary equation
```

Each stage must be independently callable and should return a result plus
diagnostic metadata:

```julia
struct LocalStageResult
    expression::Symbolics.Num
    changed::Bool
    warnings::Vector{Symbol}
    rejected::Vector{Any}
end
```

### 2.3 Stage A: residual normalization

Convert every equation to one residual before doing symbolic work:

```julia
function _normalize_residual(eq)
    simplify(unwrap(eq.lhs - eq.rhs))
end
```

Do not solve for the highest derivative here. Solving introduces denominator
conditions and is a representation choice for numerical or solver consumers,
not a universally safe simplification.

Normalize signs and sides only after the residual is formed. Boundary conditions
may use a left/right representation for display, but their internal comparison
should still use a residual fingerprint.

### 2.4 Stage B: derivative expansion

Use `Symbolics.expand_derivatives` to expose product and chain rules, but make
expansion targeted and budgeted:

```julia
function _expand_derivatives_bounded(expr, budget)
    candidate = expand_derivatives(wrap(expr))
    _complexity(candidate) <= budget.max_derivative_expansion_nodes ?
        unwrap(candidate) : expr
end
```

Focus on:

- product and chain rules;
- mixed and higher derivatives;
- registered derivative operators such as `Dirac` and `Heaviside`;
- consistent ordering of commuting derivatives.

Pitfalls:

- repeated chain rules can cause combinatorial growth;
- mixed derivative reordering requires a smoothness convention;
- distributional objects may not obey classical derivative identities;
- an unevaluated derivative may be preferable when expansion exceeds the budget.

### 2.5 Stage C: arithmetic expansion and normalization

Distribute multiplication only when it enables collection or cancellation.
`Symbolics.simplify` and `Symbolics.expand` should be used as targeted tools,
not as an unconditional expand/simplify loop.

```julia
expr = simplify(expr)
expr = expand(expr)              # only for selected algebraic regions
expr = simplify(expr)
```

Do not expand transcendental arguments by default. For example, expanding
`sin(a + b)` is usually a growth operation, not a simplification.

### 2.6 Stage D: differential structure classification

Find derivatives and dependent-variable generators structurally. Then classify
each expression:

```text
polynomial in selected generator
nonlinear differential atom
ordinary coefficient
unsupported opaque expression
```

Examples:

```text
a(x) * u''                 polynomial generator term
exp(u')                    nonlinear differential atom
sin(u') * u''              coefficient relative to u'', but not ordinary
a(x, u)                    coefficient if u is allowed as an algebraic atom
Integral(..., u')          opaque unless a rule handles it
```

A collector must never call polynomial `degree` or `coeff` on an expression
unless polynomiality in the selected atom set has been established.

### 2.7 Stage E: generator collection

Use `group_coefficients` as the starting implementation, but extend it with
classification and fallback behavior:

```julia
function collect_generators(expr, generators)
    polynomial_part, nonlinear_atoms, remainder =
        _classify_differential_structure(expr, generators)
    grouped = _collect_polynomial_part(polynomial_part, generators)
    _recombine(grouped, nonlinear_atoms, remainder)
end
```

Collection is relative to a generator. A coefficient of `u''` may contain
`exp(u')`; it is not necessarily free of all differential generators. Preserve
that distinction for later factorization and solving decisions.

### 2.8 Stage F: coefficient simplification

Simplify coefficients after collection and then collect once more. Coefficients
may contain rational functions, ordinary variables, parameters, dependent
variables, or nonlinear differential atoms.

Use:

- `Symbolics.simplify`;
- `SymbolicUtils` tree traversal;
- `Symbolics.cancel`/`factor` equivalents where available;
- `Nemo` only for explicitly classified polynomial regions.

Do not divide by a symbolic coefficient in Layer 1. Division is an
assumption-aware operation and belongs in Layer 2.

### 2.9 Stage G: structural rewrite rules

Apply only unconditional or structurally safe rules:

- derivative operator normalization;
- registered `Dirac` and `Heaviside` rules with valid local semantics;
- literal zero/one and constant arithmetic;
- sign normalization;
- safe function argument normalization.

The existing `SPECIAL_REWRITER` is the initial structural rewrite layer.
`SYMBOLIC_RULE_GROUPS` should be selected only after Layer 2 provides proofs.

### 2.10 Stage H: canonicalization and classification

The final local pass must produce a stable representation:

```text
residual ~ 0
```

Canonicalization should include:

- stable ordering of additive terms and multiplicative factors;
- stable ordering of differential generators by order and variable;
- normalized sign;
- removal of nonzero numeric content when it is unconditionally safe;
- canonical function argument forms;
- canonical equation-side placement.

Classify the result:

```julia
@enum EquationStatus ordinary identity contradiction parameter_condition

struct LocalEquationResult
    equation::Union{Nothing,Symbolics.Equation}
    status::EquationStatus
    residual::Symbolics.Num
    diagnostics::Vector{Any}
end
```

`0 ~ 0` is an identity. A provably nonzero constant residual is a
contradiction. A residual containing no dependent variables may be a branch
condition rather than a differential equation.

### 2.11 Layer 1 pseudocode

```julia
function simplify_equation(eq, context; options=LocalOptions())
    residual = _normalize_residual(eq)
    previous = nothing

    for pass in 1:options.max_passes
        previous = residual
        residual = _expand_derivatives_bounded(residual, options.budget)
        residual = _normalize_arithmetic(residual, options)
        residual = _collect_generators_safely(
            residual, context.generators, options)
        residual = _simplify_coefficients(residual, options)
        residual = _apply_structural_rules(residual, context)
        residual = _canonicalize_residual(residual, context)

        _complexity(residual) <= options.budget.max_nodes ||
            return _preserve_previous_result(previous, residual)
        isequal(residual, previous) && break
    end

    _classify_local_result(residual, context)
end
```

## 3. Layer 2: assumption-aware simplification

### 3.1 Role and contract

Layer 2 runs on one `DiffEqBranch` and may use its domain, parameters,
restrictions, and proven facts. It is responsible for transformations that can
change validity unless assumptions are checked.

Its contract is:

```text
simplify_branch(branch)
    -> one equivalent branch, or a finite set of explicitly annotated branches
```

The default mode should never silently discard points. Unknown propositions
must remain unknown, and the transformation must be skipped or branched.

### 3.2 Assumption-aware pipeline

```text
local fixed point
    |
    v
collect candidate factors and branch-sensitive identities
    |
    v
prove nonzero, sign, reality, integrality, or domain facts
    |
    +--> proven: apply transformation and record proof
    |
    +--> disproven: reject transformation
    |
    +--> unknown: preserve expression or split branch if enabled
    |
    v
re-run local simplification
    |
    v
repeat until branch fixed point or budget
```

### 3.3 Assumption representation and proof

`SymbolicDomain` stores the input constraints. Layer 2 should add a proof
service that combines:

- exact literal simplification;
- restrictions in `branch.restrictions`;
- parameter sign and equality facts;
- interval or box information;
- affine sign analysis;
- symbolic constraint satisfiability;
- optional polynomial root isolation.

The existing `factor_divisibility` and its component/cache helpers are the
foundation. Its result should be represented as a `ProofFact`, not merely a
boolean:

```julia
proof = _prove_nonzero(factor, assumptions)
proof.status === :proven || continue
```

Unknown is not false, and it must not be treated as permission to divide.

### 3.4 Candidate discovery and certified cancellation

Candidate discovery and proof must remain separate:

```julia
function certified_cancel(expr, assumptions)
    current = expr
    for candidate in common_factor_candidates(current)
        proof = _prove_nonzero(candidate, assumptions)
        proof.status === :proven || continue
        next = _cancel_one_factor(current, candidate)
        _equivalent_under_proof(next, current, proof) || continue
        current = next
        record_cancellation(candidate, proof)
    end
    current
end
```

Focus on:

- preserving factor multiplicity;
- distinguishing numerator cancellation from denominator clearing;
- recording excluded denominator zeros;
- allowing dependent-variable cancellation only when restrictions prove it;
- verifying the result by substitution or normalized residual equivalence.

Never convert a denominator cancellation into a globally equivalent equation
without retaining its nonzero condition.

### 3.5 Assumption-aware function rules

Rules must be grouped by their proof obligations:

```julia
const SAFE_FUNCTION_RULES = ...
const REAL_RULES = ...
const POSITIVE_RULES = ...
const INTEGER_EXPONENT_RULES = ...
const BRANCH_SENSITIVE_RULES = ...
```

Examples:

- `sqrt(x^2) -> abs(x)` is safe without a sign assumption;
- `abs(x) -> x` requires `x > 0` or a suitable nonnegative proof;
- `log(a) + log(b) -> log(a*b)` requires compatible real/complex domain facts;
- `(x^a)^b -> x^(a*b)` requires branch restrictions;
- trigonometric periodic reductions require integer hypotheses where variables
  occur in periods.

The rule engine should return proof obligations instead of applying a rule
whose predicate is unknown:

```julia
struct RewriteCandidate
    expression::Symbolics.Num
    rule::Symbol
    obligations::Vector{Any}
end
```

### 3.6 Branch splitting

Branch splitting is appropriate only when it is finite, explicit, and useful.
For a factor `g`, a permitted split is typically:

```text
branch A: g = 0
branch B: g != 0
```

The nonzero branch may cancel `g`; the zero branch must retain the original
equation and receive the new restriction. Every branch must receive a
`FactorStep` or a dedicated `AssumptionSplitStep`.

Use `DiffEqSystem` branch deduplication and fingerprints after each split.
Enforce `max_branches`; on overflow, preserve the unsplit expression and
return a diagnostic rather than silently truncating solutions.

### 3.7 Side conditions and denominator tracking

Every transformation that introduces or removes a denominator must maintain a
side-condition set:

```julia
struct SideCondition
    proposition::Any
    source::Symbol
    status::Symbol
end
```

Side conditions belong to the branch assumptions, not to an untracked comment.
They must participate in later proof queries and branch fingerprints.

### 3.8 Layer 2 pseudocode

```julia
function simplify_branch(branch; options=AssumptionOptions())
    branches = [branch]

    for system_pass in 1:options.max_passes
        next_branches = DiffEqBranch[]

        for current in branches
            local = _simplify_all_local(current, options.local)
            candidates = _discover_assumption_rewrites(local, options)
            outcomes = _apply_proven_rewrites_or_split(
                local, candidates, options)

            for outcome in outcomes
                normalized = _simplify_all_local(outcome.branch, options.local)
                push!(next_branches, normalized)
            end
        end

        next_branches = _deduplicate_branches(next_branches)
        _branch_set_fingerprint(next_branches) ==
            _branch_set_fingerprint(branches) && break
        length(next_branches) <= options.budget.max_branches ||
            return _return_unexpanded_branches(branches)
        branches = next_branches
    end

    branches
end
```

## 4. Layer 3: system reduction

### 4.1 Role and contract

Layer 3 uses relationships between equations. It is not merely another rewrite
pass. Its transformations may eliminate variables, derive compatibility
conditions, remove redundancy, or create branches.

Its contract is:

```text
simplify_system(sys)
    -> an equivalent system, represented as one or more explicit branches
```

The default system profile should begin with conservative algebraic reduction.
Differential elimination and integrability analysis should be opt-in until their
solution-class semantics are fully specified.

### 4.2 Interleaved system pipeline

System reduction must be interleaved with local and assumption-aware passes:

```text
local normalize every branch
    |
    v
assumption-aware branch normalization
    |
    v
system-wide candidate discovery
    |
    v
apply one safe reduction batch
    |
    v
local normalize changed equations
    |
    v
assumption-aware normalization
    |
    v
repeat until the whole branch set is stable
```

The local pass runs before system reduction so equations have comparable
residual forms. It runs after system reduction because substitution and
elimination create new expressions. The system pass runs again because local
cleanup may expose new relationships.

### 4.3 System-level data structures

```julia
struct SystemReductionOptions
    max_passes::Int
    enable_substitution::Bool
    enable_redundancy_removal::Bool
    enable_algebraic_elimination::Bool
    enable_differential_consequences::Bool
    ranking::Symbol
    budget::ComplexityBudget
end

struct EquationRelation
    kind::Symbol       # :duplicate, :multiple, :substitution, :elimination
    equations::Vector{Int}
    variable::Union{Nothing,Symbolics.Num}
    certificate::Any
end

struct SystemReductionStep <: DerivationStep
    relations::Vector{EquationRelation}
    method::Symbol
end
```

The system reducer should operate on immutable snapshots and return a
transformation result:

```julia
struct SystemReductionResult
    branches::Vector{DiffEqBranch}
    changed::Bool
    step::Union{Nothing,SystemReductionStep}
    diagnostics::Vector{Any}
end
```

### 4.4 System Stage A: local preparation

For each branch:

1. normalize every equation to a residual;
2. simplify boundary conditions locally;
3. classify identities, contradictions, and parameter conditions;
4. canonicalize equations and compute fingerprints;
5. preserve equation-to-source indices for diagnostics.

Remove identities only when they are redundant in the system representation.
Contradictions should mark a branch inconsistent and remove it from the
solution union with a recorded reason.

### 4.5 System Stage B: relation discovery

Discover relations in increasing order of semantic power:

1. exact duplicate equations;
2. nonzero scalar multiples;
3. algebraic substitutions with explicit pivot conditions;
4. linear elimination in selected generators;
5. polynomial elimination;
6. differential consequences and compatibility conditions.

The early relations can use residual fingerprints and `Nemo` polynomial
representations. Do not infer equivalence from string equality alone.

### 4.6 System Stage C: conservative substitutions

A substitution candidate should contain:

```text
pivot variable or generator
replacement expression
source equation
nonzero conditions
complexity estimate
```

Prefer substitutions that reduce a ranking measure:

```text
highest derivative order
number of differential generators
number of equations containing the pivot
expression node count
```

Do not substitute a nonlinear expression merely because it can be algebraically
solved if the solve introduces untracked roots, branches, or denominators.

After substitution:

```julia
for affected_eq in affected_equations
    replace(affected_eq, substitution)
    simplify_equation(affected_eq, new_context)
end
```

### 4.7 System Stage D: redundancy and consistency

Detect and remove only equations whose removal is certified:

- exact canonical duplicates;
- proven nonzero scalar multiples;
- equations reducible to zero by an accepted elimination basis;
- equations implied by recorded substitutions.

An equation that is merely numerically similar or heuristically smaller is not
redundant. Retain it unless an exact certificate exists.

### 4.8 System Stage E: algebraic elimination

For expressions classified as polynomial in selected atoms:

1. map Symbolics expressions to a `Nemo` polynomial ring;
2. choose a variable/generator ranking;
3. compute a conservative elimination or Groebner-style relation;
4. map results back through an atom table;
5. expand and locally normalize;
6. verify each accepted relation against the original system.

`Nemo.jl` is appropriate for exact polynomial arithmetic and Groebner bases.
Use `SymbolicUtils` to construct the atom map and `Symbolics` to restore
expressions. Transcendental and unsupported atoms must be treated as algebraic
indeterminates only when that abstraction is documented and does not claim
analytic identities.

### 4.9 Stage F: differential consequences

Differentiating equations can reveal compatibility conditions, but it is not a
routine simplification operation. It depends on the intended solution class and
regularity assumptions.

Enable it only when the context declares:

- the independent-variable derivative is valid;
- the required smoothness or distributional convention;
- the resulting consequence is used for elimination or consistency checking;
- no original equation is removed without a separate equivalence argument.

Differential consequences may be added as consequences without replacing the
original system. If replacing equations, the reducer must prove equivalence or
create the necessary branch/side conditions.

### 4.10 Stage G: post-reduction normalization

Every changed equation goes through Layer 1, then Layer 2. This is mandatory:

```text
system reduction
    -> local derivative/arithmetic normalization
    -> generator classification and collection
    -> assumption-aware cancellation
    -> canonicalization
```

The system reducer then reruns relation discovery on the normalized result.
This continues until the branch-set fingerprint is stable or a budget is
reached.

### 4.11 Layer 3 pseudocode

```julia
function simplify_system(sys; options=SystemReductionOptions())
    branches = _prepare_branches_locally(sys, options)

    for pass in 1:options.max_passes
        before = _branch_set_fingerprint(branches)

        branches = _run_assumption_layer(branches, options.assumptions)
        relations = _discover_system_relations(branches, options)
        reduced = _apply_safe_relation_batch(branches, relations, options)
        branches = _normalize_changed_branches(reduced.branches, options)
        branches = _deduplicate_and_classify(branches)

        after = _branch_set_fingerprint(branches)
        after == before && break
        _within_budget(branches, options.budget) ||
            return _return_last_stable_system(branches)
    end

    DiffEqSystem(branches)
end
```

Apply reductions in batches only when they are independent. Otherwise apply one
relation, normalize, and rediscover relations. This prevents stale pivots and
reduces the risk of cascading invalid substitutions.

## 5. Packages and implementation responsibilities

### Existing core packages

- **Symbolics.jl:** symbolic variables, equations, derivatives,
  `expand_derivatives`, `simplify`, substitution, and structural metadata.
- **SymbolicUtils.jl:** expression-tree traversal, rewrite rules, postwalk
  rewriters, structural matching, and atom inspection.
- **ModelingToolkit.jl:** differential variables, parameter metadata,
  registered symbolic functions, and system interoperability.
- **Nemo.jl:** exact polynomial rings, factorization, gcd/content operations,
  Groebner bases, and polynomial elimination for classified polynomial regions.
- **IntervalArithmetic.jl / IntervalBoxes.jl:** interval sign and nonzero
  reasoning where branch domains provide interval information.
- **DomainSets.jl:** domain construction and set operations when symbolic
  domain representations need a richer backend.

### Recommended use boundaries

Do not use `Nemo` on arbitrary Symbolics expressions. First classify an
expression as polynomial in a selected atom set and build a reversible atom
table. Do not use generic rewrite rules as proof of domain equivalence.
Use `Symbolics` for expression construction and `SymbolicUtils` for traversal,
but keep proof and branch metadata in DiffEqCAS-owned structures.

## 6. Testing and acceptance criteria

Each layer needs tests for both successful transformations and deliberate
non-transformations.

### Layer 1 tests

- product and chain-rule derivative expansion;
- higher and mixed derivatives;
- polynomial collection by dependent variables and differential generators;
- `exp(u')`, `sin(u'')`, and similar nonlinear differential atoms;
- coefficient expressions containing other differential generators;
- stable ordering and fixed-point behavior;
- identity and contradiction classification;
- expression-growth budget preservation.

### Layer 2 tests

- cancellation of numeric and parameter factors proven nonzero;
- refusal to cancel unknown or potentially zero factors;
- cancellation under explicit dependent-variable restrictions;
- denominator side-condition preservation;
- square-root, logarithm, power, and absolute-value rules with and without
  sufficient assumptions;
- branch splitting, deduplication, and maximum-branch handling;
- proof metadata in derivation history.

### Layer 3 tests

- duplicate and scalar-multiple equation removal;
- conservative algebraic substitution;
- substitution followed by local re-normalization;
- repeated local/system fixed points;
- elimination of polynomial atoms through a reversible `Nemo` map;
- inconsistent and redundant systems;
- preservation of boundary conditions and branch metadata;
- differential-consequence mode disabled by default and correctly gated when
  enabled.

Every accepted transformation should be tested by a semantic check appropriate
to its layer:

```text
local: normalized residual equivalence
assumption-aware: equivalence under proof facts and side conditions
system: solution-set preservation certificate or explicit branch decomposition
```

## 7. Implementation order

Implement in this order to keep every intermediate version useful:

1. Extract a reusable local residual/canonicalization pipeline.
2. Add differential-structure classification and nonlinear atom preservation.
3. Integrate safe generator collection and final coefficient normalization.
4. Add complexity budgets and stable fingerprints.
5. Refine `factor_divisibility` into proof-producing assumption queries.
6. Implement certified factor cancellation and side-condition tracking.
7. Wire `SYMBOLIC_RULE_GROUPS` through assumption-aware rule selection.
8. Implement duplicate/scalar-multiple system normalization.
9. Add conservative substitution and post-reduction local normalization.
10. Add polynomial atom maps and `Nemo`-backed elimination.
11. Add optional differential consequences only after regularity semantics are
    documented and tested.

The default public simplifier should initially enable Layers 1 and 2 in a
conservative profile. Layer 3 should be opt-in until its reduction certificates,
branch behavior, and performance limits are stable.
