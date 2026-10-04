# Simplification plan

This document is the implementation template for simplification in
`DiffEqCAS`. It is intentionally organized around the existing
`DiffEqSystem`/`DiffEqBranch` architecture rather than around independent
expression-processing utilities.

The planned simplifier has three layers:

1. **Local equation simplification:** normalize each equation without using
   sibling equations or changing its domain.
2. **Assumption-aware simplification:** use the selected branch's domain and
   restrictions to justify cancellations and branch-sensitive identities.
3. **System reduction:** use relationships between equations to remove
   redundancy, substitute, and eliminate.

The layers are not three unrelated modes. They are nested operations on one
`DiffEqSystem`:

```text
one DiffEqSystem
    |
    +-- for each branch:
    |       local simplification
    |       assumption-aware simplification
    |
    +-- system-wide relation discovery/reduction
            |
            +-- local simplification of changed equations
            +-- assumption-aware simplification of changed branches
            +-- repeat until the system is stable
```

The public operation remains:

```julia
simplify_system(sys::DiffEqSystem; options=SimplificationOptions())
```

It accepts one system and returns one new `DiffEqSystem`. A system may contain
multiple `DiffEqBranch` values because branches represent a union of solution
sets, but the simplifier does not create a second independent system context.

## 1. Existing architecture and design decisions

### 1.1 `DiffEqSystem` is the orchestration boundary

`DiffEqSystem` already owns:

- the current `branches`;
- pending and completed branch work;
- duplicate suppression through `seen`;
- iteration over branches;
- construction from equations or branches.

Simplification should use that model instead of introducing a separate
simplification context that duplicates system state. The system-level function
coordinates the run, while branch-local helpers receive a selected
`DiffEqBranch`.

The simplifier should not mutate the caller's system. It should construct
transformed branches, preserve branch metadata, and return a new
`DiffEqSystem`. This matches the current `_with_simplified_expressions` and
`_simplify_one_system` direction.

### 1.2 `DiffEqBranch` is the unit of assumptions and history

Each branch carries:

- equations and boundary conditions;
- independent variables, dependent variables, and parameters;
- a `SymbolicDomain`;
- interval/domain cache information;
- restrictions/trivial-solution metadata;
- a `DerivationHistory`.

Assumption-aware transformations must operate on one branch at a time because
nonzero facts and branch restrictions are branch-specific. System-wide
reduction may compare several equations in one branch, but it must not use facts
from one branch to rewrite another.

### 1.3 `SimplificationOptions` configures one complete run

`SimplificationOptions` should be the single configuration object for the
entire simplification run. It is stored in `SimplificationStep`, which is
appended to the history of every branch changed by that run. This connects:

```text
the requested behavior
    -> the transformations performed
    -> the branch history that records them
```

The options should describe policy and resource limits, not transient mutable
state:

```julia
Base.@kwdef struct SimplificationOptions
    max_passes::Int = 4
    max_system_passes::Int = 4
    max_branches::Int = 256
    max_nodes::Int = 100_000
    max_derivative_nodes::Int = 50_000

    expand_derivatives::Bool = true
    expand_products::Bool = true
    collect_generators::Bool = true
    enable_cancellation::Bool = true
    enable_factorization::Bool = false
    enable_function_rules::Bool = false
    enable_system_reduction::Bool = false
    enable_branch_splitting::Bool = false
    enable_differential_consequences::Bool = false

    normal_form::Symbol = :collected
    reduction_strategy::Symbol = :conservative
end

struct SimplificationStep <: DerivationStep
    options::SimplificationOptions
end
```

The exact field names can change during implementation, but the relationship
must remain: one options value describes one complete call to
`simplify_system`, and one `SimplificationStep` records that call. Stage-level
details belong in diagnostics or specialized derivation steps, not in a
second configuration object.

Resource limits are included here because simplification can increase
expression size or branch count. A limit is not a simplification result:
when reached, the implementation keeps the last stable result and records a
diagnostic rather than returning an incomplete success-shaped transformation.

### 1.4 Results and diagnostics

The normal public result is still `DiffEqSystem`. Internal helpers need
structured results so a rejected or budget-limited transformation is visible:

```julia
struct SimplificationDiagnostics
    warnings::Vector{Symbol}
    rejected_rules::Vector{Symbol}
    rejected_transformations::Vector{Any}
    node_counts::Vector{Int}
end

struct BranchSimplificationResult
    branch::DiffEqBranch
    changed::Bool
    diagnostics::SimplificationDiagnostics
end
```

Diagnostics should normally be internal until a public reporting API is
designed. They are still important: unsupported transcendental structure,
unknown nonzero facts, and budget refusals must not look like successful
rewrites.

## 2. Normal forms and shared concepts

### 2.1 Residual equations

Every differential equation is processed through the residual:

```julia
_simplification_expression(eq::Symbolics.Equation) =
    unwrap(eq.lhs - eq.rhs)
```

The internal target is:

```text
canonical residual ~ 0
```

This avoids arbitrary choices about which derivative to isolate and makes
comparison, collection, and system reduction consistent. Boundary conditions
remain left/right equations for metadata and display, but each side is locally
normalized and their residual can be used for fingerprints.

Do not make “solved for the highest derivative” the default. Solving can
introduce denominator conditions, fail for implicit or nonlinear equations, and
choose a representation that is useful to a solver but not universally simpler.

### 2.2 Differential generators and nonlinear differential atoms

A differential generator is a dependent variable or derivative selected for
collection, such as `u`, `D(u)`, or a mixed derivative. Not every expression
containing a generator is polynomial in that generator:

```text
a(x) * u''       polynomial generator term
exp(u')          nonlinear differential atom
sin(u') * u''    coefficient relative to u'', but not derivative-free
```

The collector therefore needs a small structural classification, not a
blind call to polynomial `degree` and `coeff`:

```julia
@enum DifferentialTermKind polynomial_term nonlinear_atom ordinary_term

struct DifferentialTerm
    expression::Symbolics.Num
    kind::DifferentialTermKind
    generators::Vector{Symbolics.Num}
end
```

`DifferentialTerm` is an analysis result for one expression, not an alternative
system representation. It tells the local collector what it is allowed to do:
collect polynomial occurrences and preserve nonlinear occurrences as opaque
terms. The original Symbolics expression remains the source of truth.

This is necessary for equations such as:

```text
u'' + exp(u') = 0
u_t + sin(u_x) = 0
```

The simplifier should collect `u''` or `u_t` without pretending that the whole
equation is a polynomial differential equation.

### 2.3 Atom maps for polynomial regions

Factorization and elimination need an explicit reversible mapping when a
Symbolics expression contains functions or derivatives that a polynomial
backend does not understand:

```julia
struct AtomTable
    atoms::Vector{Symbolics.Num}
    indices::Dict{Any,Int}
end
```

`AtomTable` belongs to one transformation attempt. It maps selected
expressions, such as `u''` or `exp(u')`, to temporary polynomial variables and
maps the result back. It must never cause the system to claim an analytic
identity that was only true after treating a transcendental expression as an
independent algebraic atom.

`Nemo.jl` is used only after this classification and mapping. Unsupported
subexpressions remain atoms or are left untouched.

## 3. Layer 1: local equation simplification

### 3.1 Role and contract

Local simplification transforms one equation using only:

- the equation itself;
- the selected branch's variable declarations;
- unconditional symbolic rules;
- the current local resource limits.

It does not use another equation as a substitution rule, and it does not
divide by a factor merely because the factor appears common. Its output is a
locally equivalent equation or a classification as identity, contradiction, or
parameter-only condition.

The branch-level caller applies this operation to every `eqs` entry and every
boundary-condition side.

### 3.2 Pipeline

```text
branch
  |
  v
normalize each equation to a residual
  |
  v
expand derivatives, subject to node budget
  |
  v
normalize arithmetic and selected products
  |
  v
classify differential generators and nonlinear atoms
  |
  v
collect valid generator powers
  |
  v
simplify coefficients and ordinary subexpressions
  |
  v
apply unconditional structural rules
  |
  v
recollect and canonicalize
  |
  v
classify identities and contradictions
```

The final recollection is intentional. Coefficient simplification can expose
new common terms, and structural rules can expose new generator powers.

### 3.3 Derivative expansion

The existing `expand_derivatives` operation is the foundation for this stage.
It exposes product and chain rules so later collection sees actual
derivatives:

```text
D(a(x)u') -> a(x)u'' + a'(x)u'
```

The stage must:

- expand only when `expand_derivatives` is enabled;
- measure the candidate node count before accepting it;
- preserve the previous expression if the derivative budget is exceeded;
- use the project's convention for commuting mixed derivatives;
- leave unsupported registered functions intact.

Derivative expansion is done before generator collection because collection of
an unexpanded derivative would miss terms produced by product and chain rules.
It is not repeated unconditionally at every substage; the local loop calls a
single stage and only repeats if a later rewrite created a new derivative
expression.

### 3.4 Arithmetic normalization

Use `simplify` for general local cleanup and `expand` for selected algebraic
regions when distribution is needed for collection:

```julia
expr = simplify(expr)
options.expand_products && (expr = expand(expr))
expr = simplify(expr)
```

The implementation should not expand transcendental arguments by default.
`sin(a + b)` and `exp(a + b)` are normally preserved because function
expansion can increase size and may not be a simplification for downstream
consumers.

The purpose of this stage is to expose additive terms and multiplicative
factors. It is not to select the final factored or expanded display form;
`normal_form` controls that final policy.

### 3.5 Generator collection

The current `group_coefficients` function is the starting point. It should be
refactored into a branch-independent expression helper and extended with the
classification above:

```julia
function _collect_generators(expr, branch, options)
    generators = _differential_generators(branch)
    terms = _classify_differential_terms(expr, generators)
    grouped = _collect_polynomial_terms(terms, generators)
    _recombine(grouped, terms)
end
```

The helper receives the branch because `branch.dvs` and `branch.ivs` define
which expressions count as dependent variables and independent variables.
It does not use sibling equations; that is the boundary between local
collection and system reduction.

The collector must preserve:

- powers of a generator;
- mixed derivative generators;
- coefficients that contain other differential generators;
- nonlinear atoms such as `exp(u')` and `sin(u'')`;
- unsupported terms in their original structural form.

### 3.6 Coefficient simplification

After collection, simplify the coefficient attached to each generator and the
remainder. This is where `Symbolics.simplify`, `SPECIAL_REWRITER`, and the
existing helper utilities do most of their work.

A coefficient relative to `u''` is not necessarily free of `u'`. The local
stage may simplify:

```text
(exp(u') + cos(u'))u''
```

but it must not treat that coefficient as an ordinary function of `x` when a
later stage decides whether solving or cancellation is safe.

No symbolic division by a potentially zero expression occurs here. That is the
responsibility of Layer 2.

### 3.7 Structural rules

The existing `SPECIAL_REWRITER` is the initial structural rule set. It
contains derivative ordering and registered special-function behavior. Layer 1
may use rules that are unconditional under the project's declared symbolic
semantics.

The rule groups in `symbolic_rules.jl` are not all Layer 1 rules. Rules for
logs, powers, absolute values, and trigonometric expressions can depend on
sign, reality, integrality, or branch assumptions and therefore belong in
Layer 2.

### 3.8 Canonicalization and classification

The final local pass should make equivalent accepted outputs deterministic:

- residual on the left and `0` on the right;
- stable additive-term order;
- stable factor order;
- stable differential-generator order;
- normalized sign;
- safe numeric content normalization;
- stable function argument representation.

The result must then be classified:

```text
0 ~ 0                 identity
provably nonzero ~ 0  contradiction
no dependent terms    parameter/domain condition
otherwise             ordinary differential equation
```

The system-level caller decides whether to remove an identity, discard an
inconsistent branch, or store a parameter/domain condition as a restriction.
The local helper only reports the classification.

### 3.9 Local pseudocode

```julia
function _simplify_equation_local(eq, branch, options)
    residual = _simplification_expression(eq)
    previous = nothing

    for _ in 1:options.max_passes
        previous = residual

        if options.expand_derivatives
            residual = _expand_derivatives_bounded(
                residual, options.max_derivative_nodes)
        end
        residual = _normalize_arithmetic(residual, options)

        if options.collect_generators
            residual = _collect_generators(residual, branch, options)
        end
        residual = _simplify_coefficients(residual, branch, options)
        residual = _apply_structural_rules(residual, branch, options)
        residual = _canonicalize_residual(residual, branch, options)

        _complexity(residual) <= options.max_nodes ||
            return _local_result(previous, :budget_exceeded)
        isequal(residual, previous) && break
    end

    _classify_local_result(residual, branch)
end
```

`_simplify_branch_local` calls this helper for every equation and boundary
condition, reconstructs a `DiffEqBranch` with the existing metadata, and
returns diagnostics. It does not append history by itself; the outer
`simplify_system` call appends one `SimplificationStep(options)` when the
complete requested run changes the branch.

## 4. Layer 2: assumption-aware simplification

### 4.1 Role and contract

Layer 2 is still branch-local, but it may use:

- `branch.domain`;
- `branch.restrictions`;
- parameter metadata;
- interval/domain caches;
- facts proven during this simplification run.

Its purpose is to perform transformations that are mathematically valid only
under facts that are not visible from the expression alone. Examples include
dividing by a factor, removing an absolute value, combining logarithms, and
using some power identities.

An unknown fact is not permission to rewrite. The result is either:

```text
proved transformation
rejected transformation
explicit branch split
```

### 4.2 Assumption state for one branch

The branch already stores the source of assumptions. A proof cache can be
introduced as an internal run-local object:

```julia
struct AssumptionState
    domain::SymbolicDomain
    restrictions::Vector{Any}
    facts::Dict{Any,ProofFact}
end

struct ProofFact
    proposition::Any
    status::Symbol       # :proven, :disproven, :unknown
    method::Symbol
    evidence::Any
end
```

`AssumptionState` is not stored in `DiffEqBranch` and is not a second system.
It is derived from one branch at the start of a branch pass and discarded or
merged into branch restrictions when the pass finishes. This keeps persistent
state in the existing branch architecture while allowing expensive proof
queries to be cached during one run.

The existing `factor_divisibility` pipeline supplies the first proof methods:
exact simplification, variable sign facts, affine reasoning, interval checks,
and later stronger polynomial or constraint methods.

### 4.3 Candidate discovery, proof, and application

These are three distinct operations:

```julia
struct RewriteCandidate
    expression::Symbolics.Num
    rule::Symbol
    obligations::Vector{Any}
end

function _apply_assumption_rule(expr, branch, options)
    candidates = _discover_candidates(expr, branch)
    for candidate in candidates
        proof = _prove_obligations(candidate.obligations, branch)
        proof.status === :proven || continue
        expr = _apply_candidate(expr, candidate)
    end
    expr
end
```

Separating these operations matters because candidate discovery is syntactic,
while proof is semantic. `common_divisors` can propose a common factor, but
`factor_divisibility` decides whether cancellation is valid on the branch.

### 4.4 Certified cancellation

The existing `_cancel_certified_residual` and `_cancel_system` should become
the implementation of this stage. They should be extended to preserve
multiplicity and proof information:

```julia
struct FactorCandidate
    expression::Symbolics.Num
    multiplicity::Int
    source::Symbol
    proof::Union{Nothing,ProofFact}
end
```

The intended flow is:

```text
common_divisors proposes numerator factors
    |
    v
prove each factor is nonzero on this branch
    |
    +-- proven: divide and locally normalize
    +-- disproven: do not divide
    +-- unknown: preserve, or split if enabled
```

Factors involving dependent variables are not categorically forbidden. They
are forbidden unless branch restrictions prove them nonzero. This allows
future restrictions such as `u(x) != 0` to be useful without weakening the
default safety policy.

Denominator cancellation and clearing are separate operations. Removing a
factor from a denominator can exclude its zero set, so the zero-set condition
must be retained as a branch restriction or used to create explicit branches.

### 4.5 Function rule groups

`SYMBOLIC_RULE_GROUPS` should be selected through the same proof mechanism:

```text
unconditional structural rules
real-valued rules
positive/negative rules
integer-exponent rules
branch-sensitive rules
```

Each rule group has a purpose:

- structural rules normalize syntax without assumptions;
- real-valued rules make identities such as square-root transformations
  precise;
- sign rules remove `abs` or select signs;
- integer rules enable periodic or exponent identities;
- branch-sensitive rules remain opt-in unless complex branch semantics are
  explicitly represented.

Function rules should be directional within one pass. If an expansion rule
creates a form that a contraction rule would immediately undo, the two rules
must be placed in separate phases or guarded by a normal-form measure.

### 4.6 Branch splitting

Branch splitting is a system operation because it changes the `branches`
vector, even though the reason for a split is found while processing one
branch. It should use the existing `push_branch!` and fingerprint logic.

For a factor `g`, a permitted split is:

```text
branch 1: g = 0
branch 2: g != 0
```

The nonzero branch may cancel `g`; the zero branch retains the pre-cancellation
equation. Both branches receive an appropriate `DerivationStep`, and both
retain all original metadata.

The split is enabled only when `enable_branch_splitting` is true and the
resulting branch count stays below `max_branches`. If the limit is reached,
the original unsplit branch is retained.

### 4.7 Assumption-aware pseudocode

```julia
function _simplify_branch_assumption_aware(branch, options)
    assumptions = _assumption_state(branch)
    current = _simplify_branch_local(branch, options)

    for _ in 1:options.max_passes
        before = _branch_fingerprint(current.branch)
        candidates = _discover_assumption_candidates(
            current.branch, assumptions, options)
        outcomes = _apply_proven_candidates_or_split(
            current.branch, candidates, assumptions, options)

        normalized = DiffEqBranch[]
        for outcome in outcomes
            result = _simplify_branch_local(outcome, options)
            push!(normalized, result.branch)
        end
        normalized = _deduplicate_branches(normalized)

        _branch_set_fingerprint(normalized) ==
            _branch_set_fingerprint([current.branch]) && break
        current = _select_or_return_branch_results(normalized)
    end

    current
end
```

The exact return type can be specialized during implementation, but the
important interaction is fixed: every accepted assumption-aware rewrite is
followed by local simplification because cancellation and function rewrites
can expose new generator or coefficient structure.

## 5. Layer 3: system reduction

### 5.1 Role and contract

System reduction is the only layer allowed to use one equation as information
about another. It operates on the complete `DiffEqSystem`, but applies
transformations branch by branch because each branch is a separate solution-set
component.

Its initial scope should be conservative:

- duplicate equation removal;
- proven scalar-multiple removal;
- algebraic substitutions with explicit pivot conditions;
- selected polynomial elimination.

Differential consequences, integrability conditions, and differential
elimination are later capabilities. They are not required for the basic
local/assumption-aware simplifier and must be opt-in.

### 5.2 Why system reduction is interleaved

The layers affect one another:

```text
local normalization
    -> exposes comparable equations and pivots
system reduction
    -> substitutes or eliminates and creates new expressions
local normalization
    -> expands, collects, and canonicalizes those expressions
assumption-aware simplification
    -> proves newly exposed cancellations
system reduction again
    -> discovers relations exposed by cleanup
```

Running system reduction only after all local work misses relations exposed by
substitution. Running it only before local work misses relations hidden by
different equation layouts. The system pass therefore runs after a local
fixed point and is followed by local and assumption-aware passes on changed
branches.

### 5.3 Relation records

Relation discovery should return records that explain why a system operation is
allowed:

```julia
struct EquationRelation
    kind::Symbol       # :duplicate, :multiple, :substitution, :elimination
    equation_indices::Vector{Int}
    pivot::Union{Nothing,Symbolics.Num}
    replacement::Union{Nothing,Symbolics.Num}
    conditions::Vector{Any}
    certificate::Any
end

struct SystemReductionStep <: DerivationStep
    relations::Vector{EquationRelation}
    method::Symbol
end
```

`EquationRelation` is a plan for one system operation. It is not persistent
system state. `SystemReductionStep` is the persistent history record when a
system reduction changes a branch.

### 5.4 Relation discovery order

Discover relations from least to most powerful:

1. exact canonical duplicates;
2. proven nonzero scalar multiples;
3. conservative substitutions;
4. linear elimination in selected generators;
5. polynomial elimination;
6. differential consequences.

This order reduces cost and risk. A duplicate does not need a polynomial
backend, while differential consequences require assumptions about regularity
and solution classes.

### 5.5 Duplicate and scalar-multiple removal

Local canonicalization makes exact duplicates detectable. Scalar multiples
require a proof that the scalar is nonzero on the branch. The operation should
remove only the redundant equation and preserve the equation that has the
preferred canonical form.

An equation that is merely numerically or heuristically similar is not
redundant. The relation must have a structural or symbolic certificate.

### 5.6 Conservative substitution

A substitution candidate must identify:

- source equation;
- pivot generator or algebraic variable;
- replacement expression;
- nonzero conditions;
- affected equations;
- a complexity/ranking improvement.

The reducer should prefer pivots that reduce the highest differential order or
the number of equations containing the pivot. It must reject substitutions
that introduce untracked roots, denominators, or branch choices.

After applying a substitution, only affected equations need to be rerun
through the local pipeline, but all equations must be reconsidered by relation
discovery afterward.

### 5.7 Polynomial elimination and `Nemo`

For a region classified as polynomial in selected generators:

1. build an `AtomTable` for derivatives and supported nonlinear atoms;
2. map the region to a `Nemo` polynomial ring;
3. choose a deterministic generator ranking;
4. perform exact factorization, gcd, or elimination;
5. map accepted results back through the atom table;
6. locally normalize the resulting equations;
7. verify the relation against the original branch before removing anything.

The atom map is necessary because Symbolics expressions may contain functions
that Nemo does not know. Treating `exp(u')` as a temporary indeterminate is
valid for algebraic manipulation of that expression, but it does not authorize
analytic rewrites involving the exponential.

### 5.8 Differential consequences

Differentiating one equation to derive another can reveal compatibility
conditions, but it changes the level of reasoning. It should be enabled only
when options and branch metadata declare the required regularity convention.

By default, a differential consequence may be added as a redundant equation
for consistency checking, but it must not replace the original equation.
Replacing equations requires an equivalence certificate or explicit branches.

### 5.9 System reduction pseudocode

```julia
function simplify_system(sys::DiffEqSystem;
    options=SimplificationOptions())

    current = _copy_system(sys)
    current = _simplify_all_branches_locally(current, options)
    current = _simplify_all_branches_assumption_aware(current, options)

    if options.enable_system_reduction
        for _ in 1:options.max_system_passes
            before = _system_fingerprint(current)
            relations = _discover_relations(current, options)
            isempty(relations) && break

            current = _apply_relation_batch(current, relations, options)
            current = _simplify_changed_branches_locally(current, options)
            current = _simplify_all_branches_assumption_aware(
                current, options)
            current = _classify_and_deduplicate(current, options)

            _system_fingerprint(current) == before && break
            _within_budget(current, options) || break
        end
    end

    _append_simplification_history_if_changed(current, sys, options)
end
```

The default implementation may call only the first two branch passes because
`enable_system_reduction` defaults to false. The architecture still supports
the system layer without making ordinary local simplification unexpectedly
expensive or semantically aggressive.

### 5.10 System classification

After each branch-local pass and each system-reduction pass:

- remove identity equations from a branch when they carry no needed metadata;
- discard branches containing a proven contradiction;
- preserve parameter/domain-only conditions as restrictions;
- deduplicate branches using canonical fingerprints;
- preserve `pending`, `completed`, and `seen` semantics through the returned
  `DiffEqSystem`.

The current `_branch_fingerprint` is the foundation, but it should eventually
fingerprint canonical equations and normalized domains so syntactically
different routes to the same branch merge reliably.

## 6. Complete interaction model

The following is the intended full pipeline for one call:

```text
input DiffEqSystem
    |
    v
copy system and preserve original histories
    |
    v
for every branch:
    local fixed point on equations and boundary conditions
    assumption-aware fixed point
    classify identity/contradiction/conditions
    |
    v
if system reduction is enabled:
    repeat until system fixed point:
        discover relations across equations in each branch
        apply one safe relation batch
        locally simplify changed equations
        assumption-aware simplify changed branches
        classify and deduplicate
    |
    v
append SimplificationStep(options) to each changed branch
return DiffEqSystem
```

The order is not merely procedural:

- local derivative expansion enables generator collection;
- generator collection exposes factors and pivots;
- assumptions decide which factors and function rules are legal;
- system substitution creates expressions that need local collection again;
- local cleanup exposes new system relations;
- canonicalization makes fixed-point and duplicate detection deterministic.

## 7. Package responsibilities

- **Symbolics.jl:** equations, symbolic variables, derivatives,
  `expand_derivatives`, substitution, and `simplify`.
- **SymbolicUtils.jl:** tree traversal, structural classification, rewrite
  matching, and `SPECIAL_REWRITER`.
- **ModelingToolkit.jl:** dependent-variable/parameter metadata and registered
  symbolic functions.
- **Nemo.jl:** exact polynomial factorization, gcd, and elimination after an
  `AtomTable` has classified a polynomial region.
- **IntervalArithmetic.jl / IntervalBoxes.jl:** interval nonzero and sign
  proofs for branch domains.
- **DomainSets.jl:** richer domain operations if `SymbolicDomain` needs them.

The packages should be used behind DiffEqCAS-owned helpers. A backend result
must be converted back into `Symbolics.Num` and verified before it changes a
branch.

## 8. Testing plan

Tests should follow the architecture and verify interactions, not only
individual rewrites.

### Local layer

- product and chain-rule derivative expansion;
- mixed and higher derivatives;
- polynomial generator collection;
- preservation of `exp(u')`, `sin(u'')`, and similar nonlinear atoms;
- coefficients containing other differential generators;
- deterministic canonical forms;
- identity, contradiction, and parameter-condition classification;
- derivative and expression node budgets.

### Assumption-aware layer

- cancellation of proven nonzero numeric and parameter factors;
- refusal to cancel unknown or potentially zero factors;
- cancellation using explicit branch restrictions;
- denominator side-condition preservation;
- function rules with sufficient and insufficient sign/reality assumptions;
- branch splitting, deduplication, and branch limits;
- `SimplificationStep(options)` in changed branch histories.

### System layer

- duplicate and scalar-multiple removal;
- substitution followed by local recollection;
- a local cleanup exposing a second system relation;
- polynomial elimination through a reversible `AtomTable`;
- inconsistent and redundant branch handling;
- preservation of boundary conditions and branch metadata;
- differential-consequence mode disabled by default and gated when enabled.

Each accepted transformation needs an appropriate check:

```text
local: residual canonicalization/equivalence
assumption-aware: equivalence under proven facts and side conditions
system: relation certificate or explicit branch decomposition
```

## 9. Implementation order

1. Keep `simplify_system` as the public orchestration entry point and refactor
   its current helpers into explicit local stages.
2. Implement residual canonicalization and identity/contradiction
   classification while preserving `DiffEqBranch` metadata.
3. Refactor `group_coefficients` into a safe collector with differential-term
   classification and nonlinear atom preservation.
4. Expand `SimplificationOptions` with shared budgets and layer switches;
   record the same options in `SimplificationStep`.
5. Add stable canonical fingerprints and ensure fixed-point checks use them.
6. Turn divisibility results into proof facts and implement certified
   cancellation with branch restrictions.
7. Wire assumption-aware `SYMBOLIC_RULE_GROUPS` into the branch pass.
8. Implement duplicate/scalar-multiple system relations using canonical
   residuals.
9. Implement conservative substitutions and mandatory post-substitution local
   and assumption-aware passes.
10. Add `AtomTable` and Nemo-backed polynomial operations for classified
    regions.
11. Add optional branch splitting and differential consequences only after
    their history, regularity, and solution-set semantics are tested.

This order produces useful behavior at every step and keeps the implementation
aligned with the existing architecture: one `DiffEqSystem` is simplified at a
time, branches carry assumptions and history, and `SimplificationOptions`
describes and records the complete run.
