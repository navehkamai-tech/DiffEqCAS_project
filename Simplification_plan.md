# Simplification plan

This document is the implementation template for simplification in
`DiffEqCAS`. It is intentionally organized around the existing
`DiffEqSystem`/`DiffEqBranch` architecture rather than around independent
expression-processing utilities.

The planned simplifier has two architectural levels:

1. **Branch simplification:** normalize equations while carrying the branch's
   domain, restrictions, proof state, and resource policy through every stage.
   There is no separate non-aware simplifier; local expression work and
   assumption-aware decisions are one integrated pipeline.
2. **System reduction:** use relationships between equations to remove
   redundancy, substitute, and eliminate, then send every changed branch back
   through the integrated branch pipeline.

These are not unrelated modes. They are nested operations on one
`DiffEqSystem`:

```text
one DiffEqSystem
    |
    +-- for each branch:
    |       integrated branch simplification
    |
    +-- system-wide relation discovery/reduction
            |
            +-- integrated simplification of changed branches
            +-- repeat until the system is stable
```

The public operation remains:

```julia
simplify_system(sys::DiffEqSystem; options=SimplificationOptions())
```

It accepts one system and returns one new `DiffEqSystem`. A system may contain
multiple `DiffEqBranch` values because branches represent a union of solution
sets, but the simplifier does not create a second independent system context.

### Task block: architecture and state

- [x] Add immutable `SimplificationRoot` snapshots to `DiffEqSystem`.
- [ ] Preserve the root when constructing transformed systems.
- [ ] Record the source of added domain restrictions in transformation history or diagnostics.

### Task block: integrated branch simplification

- [ ] Refactor `simplify_system` into explicit local stages while preserving the current public entry point.
- [ ] Implement residual canonicalization and identity/contradiction classification.
- [ ] Refactor `group_coefficients` into a generator-relative collector.
- [ ] Preserve transcendental, rational, algebraic, and opaque differential dependence when polynomial collection is not valid.
- [ ] Add derivative-expansion and expression-size budgets.
- [ ] Implement rollback and diagnostics for candidate, input, and temporary expression-size overflow.
- [ ] Add stable canonical fingerprints for local fixed-point checks.
- [ ] Turn divisibility results into proof facts with proven, disproven, and unknown outcomes.
- [ ] Implement certified cancellation using branch restrictions.
- [ ] Wire assumption-checked `SYMBOLIC_RULE_GROUPS` into the branch pass.
- [ ] Reject independent-variable rewrites when their validity condition cannot be proved or recorded as a domain restriction.
- [ ] Keep dependent-variable case splitting explicit and disabled by default.

### Task block: system reduction

- [ ] Implement duplicate and scalar-multiple relation detection using canonical residuals.
- [ ] Implement conservative substitutions with explicit pivot conditions.
- [ ] Re-run integrated branch simplification after every accepted substitution batch.
- [ ] Add the reversible `AtomTable` needed for classified polynomial regions.
- [ ] Add Nemo-backed factorization and elimination only for supported polynomial regions.
- [ ] Keep differential consequences opt-in and require documented regularity semantics.

### Task block: verification

- [ ] Test derivative expansion, mixed derivatives, and higher derivatives.
- [ ] Test nonlinear differential atoms such as `exp(u')` and `sin(u'')`.
- [ ] Test domain restrictions, provenance, and cache invalidation.
- [ ] Test dependent-variable branch splitting, deduplication, and branch limits.
- [ ] Test system substitutions followed by local recollection.
- [ ] Test preservation of `DiffEqSystem` metadata and `SimplificationStep(options)`.

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

### 1.3 Immutable input root

An input root is useful provenance, but it is not needed to execute
simplification. It allows callers and tests to answer "what did this result
come from?" without reconstructing the input from a later history.

The root should be an immutable snapshot owned by `DiffEqSystem`, not a
reference to a mutable `DiffEqSystem` and not a parent pointer. Storing the
mutable input object would not preserve the original state if that object were
later changed. Storing a whole `DiffEqSystem` would also copy work queues and
deduplication state that are execution details rather than input data.

Because one `DiffEqSystem` can contain several initial branches, the snapshot
should contain one immutable record per initial branch. It does not need to
reuse `DiffEqBranch`; its job is to preserve input values, not to participate
in branch processing:

```julia
struct SimplificationRoot
    branches::Tuple  # immutable named-tuple snapshots of initial branch data
end
```

Each element of `branches` should be constructed from immutable containers
(tuples for vectors, immutable domain/restriction snapshots, and copied
metadata). The implementation can use an internal immutable named tuple with
the fields `identifier`, `ivs`, `dvs`, `ps`, `eqs`, `bcs`, `original_domain`,
`restrictions`, and `name`; it should not store mutable
`DiffEqBranch` objects inside the root.

Conceptually, the `DiffEqSystem` proposal therefore becomes (preserving the
existing type parameters in the implementation):

```julia
mutable struct DiffEqSystem
    branches::Vector{DiffEqBranch}
    pending::Stack{DiffEqBranch}
    completed::Vector{DiffEqBranch}
    seen::Set{UInt}
    root::SimplificationRoot
end
```

The root is created when the system is constructed and copied unchanged into
results. `DerivationHistory` still records _how_ a branch changed, while
`root` records _what the complete input system was_. No DAG, parent links, or
copied intermediate systems are required.

### 1.4 `SimplificationOptions` configures one complete run

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
    max_expansion_nodes::Int = 50_000

    expand_derivatives::Bool = true
    expand_products::Bool = true
    collect_generators::Bool = true
    enable_cancellation::Bool = true
    enable_factorization::Bool = false
    enable_function_rules::Bool = false
    enable_system_reduction::Bool = false
    enable_branch_splitting::Bool = false # dependent-variable cases only
    enable_differential_consequences::Bool = false

    normal_form::Symbol = :collected
    reduction_strategy::Symbol = :conservative
end

struct SimplificationStep <: DerivationStep
    options::SimplificationOptions
end
```

The two pass limits have different scopes:

- `max_passes` limits the **local fixed-point loop** for one branch. A local
  pass runs the ordered equation stages (derivative expansion, arithmetic
  normalization, collection, coefficient simplification, structural rewrites,
  and canonicalization). The local loop repeats only when one of those stages
  changes an equation and the changed form could expose more local work.
- `max_system_passes` limits the **outer system-reduction loop**. One system
  pass discovers and applies relationships between equations in a branch, then
  reruns the integrated branch simplifier on the affected branches.
  A new system pass is needed only if that cleanup exposes another
  substitution, redundancy, or elimination relation.

They must not be combined into one counter. For example, a substitution can
create an expression that needs three local passes without requiring a second
system pass; conversely, a system pass can change several equations even when
each changed equation reaches its local fixed point in one pass. With
`enable_system_reduction=false`, `max_system_passes` has no effect. With
system reduction enabled, `max_passes` still applies to every local
normalization invoked before, during, and after each system pass.

The other limits have similarly different scopes:

- `max_nodes` is the maximum accepted expression size for ordinary local or
  post-reduction expressions.
- `max_derivative_nodes` is the stricter limit for the temporary result of
  derivative expansion, which is especially prone to combinatorial growth.
- `max_expansion_nodes` limits each accepted algebraic distribution result;
  it prevents one selected product-of-sums region from consuming the entire
  run's expression budget.
- `max_branches` limits the number of solution-set branches after optional
  dependent-variable case splitting. It does not control domain restriction,
  because this design does not create branches for independent-variable
  regions.

If a limit is reached, the current transformation is rejected or the last
stable result is returned. A limit must never cause equations, branches, or
history entries to be silently dropped.

### 1.4.1 Expression-size overflow policy

`max_nodes` is a hard admission limit for an accepted expression, not a
promise that every input expression is already below the limit. The
implementation must handle both cases explicitly:

1. **Candidate overflow:** if a rewrite, derivative expansion, distribution,
   coefficient simplification, or system substitution would produce more than
   the applicable limit, do not commit that rewrite. Restore the last accepted
   expression, record the stage, measured size, limit, and reason, and continue
   with later transformations that can operate on the retained form.
2. **Input overflow:** if an input equation already exceeds `max_nodes`,
   preserve it as the branch's starting expression and mark it
   `:over_budget_input`. The simplifier may attempt bounded
   size-reducing operations, such as removing a zero term or combining
   identical terms, but it must not apply an operation whose result is larger
   than the current expression or launch an unbounded expansion/factorization
   attempt. If no permitted reduction fits the budget, return the unchanged
   equation with a diagnostic.
3. **Temporary overflow:** derivative expansion and selected regional
   expansion are speculative. Their temporary results may be measured before
   installation, but they must never be stored in the branch, history, cache,
   or returned system when they exceed their temporary limit. This is why
   `max_derivative_nodes` and `max_expansion_nodes` are separate from
   `max_nodes`.

The size check must occur at every transformation boundary, not only at the
end of a pass. A transformation is accepted only if its resulting expression
is within `max_nodes` and the branch-wide total remains within the intended
resource policy. Use a cheap conservative node estimator before expensive
backend work, then recompute the exact estimator on the proposed result before
committing it. If the estimator is uncertain, reject the growth rather than
assuming it is safe.

Overflow is not an algebraic identity, contradiction, or solver result. It
must not be encoded as a successful simplification step. The branch remains
valid but carries a diagnostic such as:

```julia
(
    kind = :budget_exceeded,
    stage = :algebraic_expansion,
    expression_nodes = 125_000,
    limit = options.max_nodes,
    action = :kept_previous,
)
```

Diagnostics should identify whether the retained form is the last stable
candidate or the original over-budget input. They should be available to the
caller through the eventual reporting API, or at minimum to internal logging
and tests. `SimplificationStep(options)` records that the run was requested;
it must not claim that a rejected transformation occurred.

When system reduction is enabled, an over-budget equation cannot be used as a
pivot or as input to a backend operation that may increase it. The reducer may
still remove it as an exact duplicate if that comparison is bounded and
certified. Otherwise it skips the relation, records a diagnostic, and leaves
the equation in place. After a successful system transformation, every changed
branch goes through the same admission checks again; one oversized result
must not cause the whole system or unrelated branches to be discarded.

The exact field names can change during implementation, but the relationship
must remain: one options value describes one complete call to
`simplify_system`, and one `SimplificationStep` records that call. Stage-level
details belong in diagnostics or specialized derivation steps, not in a
second configuration object.

Resource limits are included here because simplification can increase
expression size or branch count. A limit is not a simplification result:
when reached, the implementation keeps the last stable result and records a
diagnostic rather than returning an incomplete success-shaped transformation.

### 1.5 Domain validity without duplicated state

This design does not fracture a system into branches for independent-variable
conditions. It does, however, retain enough domain information to distinguish
the original problem's domain from constraints added while simplifying.

Do not store both an original domain and a second copy of the fully intersected
domain. Instead, use:

```julia
mutable struct DiffEqBranch
    # existing fields
    original_domain::SymbolicDomain
    domain_restrictions::Vector{NamedTuple{(:condition, :source),Tuple{Any,Symbol}}}
    domain_set::Union{Nothing,Tuple{<:AbstractVector{<:IntervalBoxes.IntervalBox},
                                    <:AbstractVector{<:IntervalBoxes.IntervalBox}}}
    # remaining existing fields
end
```

The exact Julia type of the named tuple may be simplified during
implementation. The invariant is the important part:

- `original_domain` stores the domain supplied when this branch was created
  and is never rewritten;
- `domain_restrictions` stores only constraints added afterward, once each,
  with a source such as `:expression_domain`, `:rewrite_validity`, or
  `:user_restriction`;
- `domain_set` remains the existing derived interval cache and is invalidated
  when a new restriction is added.

The effective domain is computed by a helper when needed:

```julia
function _effective_domain(branch)
    add_constraints(
        branch.original_domain,
        [entry.condition for entry in branch.domain_restrictions],
        branch.ivs,
    )
end
```

The effective domain may be cached in the run-local `AssumptionState` and its
numeric interval result may use the existing `domain_set` mechanism, but it
should not be stored as another persistent symbolic copy. Proof routines and
solver adapters use `_effective_domain(branch)`; transformations append a
restriction rather than repeatedly rebuilding and storing a second full
constraint list. Repeated identical restrictions should be deduplicated by
canonical expression fingerprint.

This representation is more informative than an `undefined_domain` field.
The complement of the effective domain relative to the original domain is not
always “undefined”: it may be excluded because the original expression is
undefined there, because a particular rewrite requires a side condition, or
because the user supplied an additional restriction. The `source` records
which meaning applies without storing the complement set.

This also matches the usual assumption-oriented design of general-purpose
CASs: they retain assumptions or domain predicates needed to justify a
transformation, rather than eagerly materializing every complementary region
as another symbolic object. The simplifier follows that practice while
retaining more provenance than a bare assumption set through the `source`
field and the immutable root.

For example, a real equation containing `log(g(x))` adds:

```text
(g(x) > 0, :expression_domain)
```

to `domain_restrictions`. The equation is then solver-valid only on the
effective domain. Simplifying `(x^2 - 1)/(x - 1)` to `x + 1` adds
`(x != 1, :rewrite_validity)` only if the rewrite is explicitly allowed to
narrow the problem; otherwise the rewrite is rejected. No independent-variable
branch is created in either case.

The root snapshot retains the original domain for whole-system provenance.
The branch's `original_domain` is the branch-local base for descendants and
the restriction list records exactly how that branch narrowed. The root is not
passed through proof or transformation routines.

This policy is aligned with the project goal of producing systems that can be
passed to ModelingToolkit and numerical solvers. Those consumers receive one
effective valid domain per branch, while the implementation avoids duplicating
all original constraints in every transformed branch.

### 1.6 Results and diagnostics

The normal public result is still `DiffEqSystem`. Internal helpers need
structured results so a rejected or budget-limited transformation is visible:

Diagnostics should normally remain internal until a public reporting API is
designed. They can be returned by internal helpers as a named tuple or a
small result value, but they do not need new persistent structs: unsupported
transcendental structure, unknown nonzero facts, and budget refusals are
implementation diagnostics, not part of a branch's mathematical state.

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

### 2.2 Differential generators and dependence classes

A differential generator is a dependent variable or derivative selected for
collection, such as `u`, `D(u)`, or a mixed derivative. Classification must
always state **which generators are being considered**. An expression can be
linear in `u''` while still depending nonlinearly on `u'`, so “linear” and
“nonlinear” are not reliable global labels by themselves.

The useful question for the local collector is:

> How does this term depend on the selected differential generators, and what
> operations are safe for that dependence?

Use the following mutually exclusive primary classes relative to a selected
generator set:

| Class            | Meaning                                                                                       | Example                                         | Local treatment                                                      |
| ---------------- | --------------------------------------------------------------------------------------------- | ----------------------------------------------- | -------------------------------------------------------------------- |
| `free`           | Contains none of the selected generators                                                      | `a(x, u)` when only `u'` and `u''` are selected | Treat as a coefficient for those generators                          |
| `affine`         | Polynomial degree at most one in the selected generator(s)                                    | `a(x)u'' + b(x)`                                | Collect with polynomial coefficient extraction                       |
| `polynomial`     | Polynomial degree two or greater in a selected generator                                      | `(u'')^2 + u'u''`                               | Collect powers and monomials; do not call it linear                  |
| `rational`       | Contains selected generators in a quotient or negative power                                  | `u''/(1+u')`                                    | Preserve rational structure or use a rational-function routine       |
| `algebraic`      | Uses roots or other algebraic operations not represented as a polynomial                      | `sqrt(u')u''`                                   | Preserve as an algebraic atom unless an algebraic routine is enabled |
| `transcendental` | Uses selected generators inside`exp`, `log`, `sin`, `abs`, or another non-polynomial function | `exp(u')`, `sin(u'')`                           | Preserve the function application as a nonlinear differential atom   |
| `opaque`         | The traversal cannot safely classify the operation                                            | a custom symbolic function of`u'`               | Preserve it unchanged and report the unsupported structure           |

`affine` is the precise meaning of “linear” here: it includes a constant
remainder and coefficients that may depend on non-selected expressions. A
term can be affine in `u''` while its coefficient is transcendental in
`u'`. The classification must therefore also retain the set of differential
generators occurring anywhere in the term.

```julia
@enum DiffTermKind free affine polynomial rational \
    algebraic transcendental opaque

struct DiffTerm
    expression::Symbolics.Num
    dependence::DifferentialDependenceKind
    generators::Vector{Symbolics.Num}
    selected_generators::Vector{Symbolics.Num}
    degree::Union{Nothing,Int}
end
```

`degree` is populated only for `affine` and `polynomial` terms. It
is not an attempted approximation for transcendental, rational, algebraic, or
opaque terms.

This resolves the apparent conflict between earlier “linear/nonlinear/opaque”
language and the more detailed classification. “Linear” is now the
mathematical `affine` subclass of polynomial dependence; “nonlinear” is a
description that includes `polynomial_nonlinear`, `rational`,
`algebraic_nonpolynomial`, and `transcendental`; and “opaque” is reserved for
expressions whose operation is unsupported, not for every nonlinear term.

For example:

```text
u'' + exp(u') = 0
```

contains an affine `u''` term and a transcendental atom in `u'`. It is not a
polynomial differential equation as a whole, but the affine part can still be
collected. Likewise:

```text
sin(u') * u'' + (u'')^2 = 0
```

has a coefficient that is transcendental in `u'`, an affine occurrence of
`u''`, and a polynomial-nonlinear occurrence of `u''`. The collector may group
by `u''`, but must not claim that the resulting coefficient is free of all
differential generators.

`DifferentialTerm` is an analysis result for one expression, not an
alternative system representation. The original Symbolics expression remains
the source of truth. The classification tells the local collector whether it
may use polynomial `degree`/`coeff`, whether it needs a rational or algebraic
backend, or whether it must preserve the subexpression as an atom.

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

### 2.4 Which proposed structs persist

The design intentionally keeps the data model small. Persistent state belongs
in `DiffEqSystem`, `DiffEqBranch`, and `DerivationHistory`; the following
additional types have distinct roles:

| Type                  | Role                                                           | Why it is not another existing field                                   |
| --------------------- | -------------------------------------------------------------- | ---------------------------------------------------------------------- |
| `SimplificationRoot`  | Immutable snapshot of the complete input                       | Provenance of the whole system is different from branch history        |
| `ProofFact`           | Result and evidence of one semantic proof                      | A boolean cannot distinguish proven, disproven, and unknown            |
| `AssumptionState`     | Run-local cache of facts for one branch                        | It is temporary computation state, not persistent branch metadata      |
| `DifferentialTerm`    | Classification of expression dependence on selected generators | It guides local collection and is not an equation or branch field      |
| `AtomTable`           | Reversible map for one polynomial backend call                 | It is temporary translation state, not a symbolic variable declaration |
| `FactorCandidate`     | Factor multiplicity and proof attached to cancellation         | Factor discovery data is not the same as a branch restriction          |
| `EquationRelation`    | Proposed cross-equation operation and certificate              | It describes a reduction candidate, not a transformed equation         |
| `SystemReductionStep` | History record for accepted system reduction                   | It records a system operation distinct from local simplification       |

Do not add separate persistent structs for generic rewrite candidates,
diagnostics, solution pieces, guards, domain pieces, or complexity contexts.
Rewrite candidates and diagnostics are pass-local values. Independent-variable
conditions use `DiffEqBranch.original_domain` plus its
`domain_restrictions`; dependent-variable conditions use
`DiffEqBranch.restrictions`. Resource limits and policy use
`SimplificationOptions`. This prevents several objects from representing the
same concept under different names.

## 3. Integrated branch simplification

### 3.1 Role and contract

The branch simplifier transforms one branch using:

- the equation itself;
- the selected branch's variable declarations;
- the branch's effective domain and restrictions;
- proof facts established during this run;
- unconditional and assumption-checked symbolic rules;
- the current local resource limits.

It does not use another equation as a substitution rule. Every potentially
unsafe rewrite is checked in the same pipeline rather than deferred to a
second simplifier. Its output is an equivalent branch, a deliberately
restricted branch when an expression has a smaller valid domain, or a
classification as identity, contradiction, or parameter-only condition.

The branch-level caller applies this operation to every `eqs` entry and every
boundary-condition side.

### 3.2 Pipeline

```text
branch
  |
  v
create branch-local proof state and effective domain
  |
  v
normalize each equation to a residual
  |
  v
expand derivatives and selected algebraic regions
  |
  v
classify differential generators and nonlinear atoms
  |
  v
collect valid generator powers and simplify coefficients
  |
  v
discover assumption-sensitive candidates
  |
  v
prove obligations, add valid domain restrictions, and apply safe rules
|
v
recollect, canonicalize, and classify
```

The final recollection is intentional. Coefficient simplification can expose
new common terms, and structural rules can expose new generator powers.

### 3.3 Expansion policy

Expansion is not one operation on the whole expression. It is a controlled
rewrite used only when exposing additive terms or derivative generators will
enable a later stage. Unrestricted `expand(expr)` is unsafe as the default:
it can distribute across a large product, expand powers unnecessarily, and
expand function arguments without helping collection or solving.

The implementation should inspect the expression tree and divide it into
**algebraic regions**. A region is a maximal subexpression built from
addition, multiplication, integer powers, numeric constants, and expressions
that are being treated as atoms for the current operation. The following are
not algebraic regions for product expansion:

- arguments of `sin`, `cos`, `exp`, `log`, `abs`, and other registered
  functions;
- denominators and negative powers, unless a rational operation explicitly
  requests them;
- opaque or unsupported operations;
- a subexpression containing a derivative generator that the requested
  collector cannot represent polynomially.

For each candidate region, compute a reason and an estimated cost before
rewriting it. This can be a pass-local named tuple rather than another
persistent type:

```julia
candidate = (
    region = region,
    reason = :term_collection,
    estimated_nodes = estimated_nodes,
    required_generators = generators,
)
```

The candidate is accepted only when all of the following hold:

1. **Benefit:** the region contains an additive/multiplicative boundary that
   a later stage needs, such as a product of sums, or it hides a derivative
   generator needed for collection.
2. **Safety:** the rewrite is an unconditional algebraic identity under the
   current symbolic semantics. No denominator is cleared and no
   branch-sensitive function identity is used.
3. **Budget:** the estimated result is below both `max_nodes` and the
   expansion-specific `max_expansion_nodes` limit.
4. **Priority:** expanding this region is more useful than preserving its
   current compact form according to `normal_form` and the downstream
   collector/reducer.

A practical selection algorithm is:

```julia
function _expand_selected_regions(expr, branch, options)
    candidates = _find_expansion_candidates(expr, branch, options)
    candidates = filter(_beneficial_and_safe, candidates)
    candidates = sort(candidates; by = c -> _expansion_priority(c, options),
                      rev = true)

    current = expr
    for candidate in candidates
        proposed = _expand_region(current, candidate.region)
        _within_expansion_budget(proposed, current, options) || continue
        current = _replace_region(current, candidate.region, proposed)
    end
    current
end
```

The traversal must be bottom-up and must re-evaluate candidates after an
accepted replacement. A parent and child candidate must not both be expanded
from stale tree locations. Each accepted replacement is locally simplified
before the next candidate is considered, so the implementation can reject
growth that disappears after coefficient normalization.

Use these expansion targets in order:

1. **Derivative visibility:** use `expand_derivatives` on derivative
   applications whose product/chain rule result exposes generators relevant to
   this branch. For example, expose the terms in
   `D(a(x)u') -> a(x)u'' + a'(x)u'` before collection.
2. **Term collection:** distribute only products of sums that contain
   relevant differential generators or that prevent additive residual
   canonicalization.
3. **Factor access:** expand a small polynomial region only when certified
   factorization, gcd, or system-reduction logic explicitly requests the
   expanded representation.

Do not expand merely because an expression is algebraically expandable. In
particular, preserve `sin(a + b)`, `exp(a + b)`, powers of large sums, and
products whose estimated distribution would multiply term counts without
exposing a needed generator. Function expansion rules belong to the
assumption-checked rewrite stage and must be selected by their own proof and
cost policy, not by this algebraic expansion pass.

Derivative expansion and algebraic distribution have separate budgets:
`max_derivative_nodes` limits temporary derivative expansion, while
`max_expansion_nodes` limits each selected algebraic distribution result.
Derivative expansion runs first because it can reveal the regions that matter;
the selected algebraic pass then works on the resulting tree. If either
candidate exceeds its budget, retain the previous expression and continue
with collection on the compact form. This is a deliberate graceful fallback:
an opaque or unexpanded term can still be preserved as an atom.

### 3.4 Arithmetic normalization

Use `simplify` for local cleanup before candidate discovery and after every
accepted regional expansion. Do not write `simplify(expr); expand(expr)` as the
pipeline, because that loses the reason for expansion and makes the cost
unbounded:

```julia
expr = simplify(expr)
expr = _expand_selected_regions(expr, branch, options)
expr = simplify(expr)
```

The purpose of this stage is to expose only the additive terms and
multiplicative factors required by collection. It is not to select the final
factored or expanded display form; `normal_form` controls that final policy.

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

No symbolic division by a potentially zero expression occurs here. The next
assumption-checked stage in this same branch pipeline is responsible for
proving such a factor nonzero.

### 3.7 Structural rules

The existing `SPECIAL_REWRITER` is the initial structural rule set. It
contains derivative ordering and registered special-function behavior. The
integrated branch pipeline may use a rule immediately when it is unconditional
or after its obligations are proven from the branch.

The rule groups in `symbolic_rules.jl` therefore do not define separate
architectural layers. Rules for logs, powers, absolute values, and
trigonometric expressions are simply candidates whose sign, reality,
integrality, or branch obligations must be checked before application.

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
    diagnostics = Any[]
    previous = nothing

    if _complexity(residual) > options.max_nodes
        push!(diagnostics, (
            kind = :budget_exceeded,
            stage = :input,
            action = :size_reducing_only,
        ))
    end

    for _ in 1:options.max_passes
        previous = residual

        if options.expand_derivatives
            candidate = _expand_derivatives_bounded(
                residual, options.max_derivative_nodes)
            _complexity(candidate) <= options.max_derivative_nodes &&
                (residual = candidate)
        end
        residual = _normalize_arithmetic(residual, options)

        if options.collect_generators
            residual = _collect_generators(residual, branch, options)
        end
        residual = _simplify_coefficients(residual, branch, options)
        residual = _apply_structural_rules(residual, branch, options)
        residual = _canonicalize_residual(residual, branch, options)

        if _complexity(residual) > options.max_nodes
            push!(diagnostics, (
                kind = :budget_exceeded,
                stage = :local_pass,
                action = :kept_previous,
            ))
            residual = previous
        end
        isequal(residual, previous) && break
    end

    _classify_local_result(residual, branch; diagnostics)
end
```

`_run_unconditional_branch_stages` calls this helper for every equation and
boundary condition, reconstructs a `DiffEqBranch` with the existing metadata,
and returns diagnostics to the integrated branch pass. It does not append
history by itself; the outer `simplify_system` call appends one
`SimplificationStep(options)` when the complete requested run changes the
branch.

## 4. Proof and restriction stages within branch simplification

### 4.1 Role and contract

These stages are part of the integrated branch simplifier, not a second
simplification layer. They may use:

- `_effective_domain(branch)`;
- `branch.restrictions`;
- parameter metadata;
- interval/domain caches;
- facts proven during this simplification run.

Their purpose is to perform transformations that are mathematically valid only
under facts that are not visible from the expression alone. Examples include
dividing by a factor, removing an absolute value, combining logarithms, and
using some power identities. They run after candidate expressions have been
normalized enough to expose these opportunities, and any accepted rewrite
returns to collection and canonicalization before the branch pass continues.

An unknown fact is not permission to rewrite. The result is either:

```text
proved transformation
rejected transformation
dependent-variable case split, when explicitly enabled
domain restriction, when the expression is undefined outside the valid domain
```

### 4.2 Assumption state for one branch

The branch already stores the source of assumptions. A proof cache can be
introduced as an internal run-local object:

```julia
struct AssumptionState
    effective_domain::SymbolicDomain
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

### 4.2.1 Domain validity is restriction, not splitting

When a recognized operation is undefined outside a part of the independent
variable domain, add a restriction to the current branch. Do not create a
second `DiffEqBranch` or a second fully intersected domain field for the
discarded region. It is not a second solution family of the original equation.

```julia
function _add_domain_restriction!(branch, condition, source)
    push!(branch.domain_restrictions,
        (condition=condition, source=source))
    branch.domain_set = nothing
    branch
end
```

For a real `log(g(x))`, this means adding `(g(x) > 0, :expression_domain)`.
The invalid region must not be passed to ModelingToolkit or a
numerical solver as another equation system. If the valid domain is unknown,
the operation is not applied. The immutable root remains available if
provenance code later needs to compare the original and current domains.

This is deliberately narrower than general piecewise-domain analysis. Domain
fracturing, interface matching, and region-wise solution reconstruction are
outside the simplifier's goal of producing solver-ready algebraic systems.

### 4.3 Candidate discovery, proof, and application

Candidate discovery, proof, and application are three distinct operations.
Candidate discovery does not need a persistent struct: it can return a
collection of named tuples or another internal value local to one pass. This
keeps the public/persistent data model small:

```julia
candidate = (expression=expr, rule=:log_product, obligations=conditions)

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
    +-- unknown: preserve, or dependent-variable split if enabled
```

Factors involving dependent variables are not categorically forbidden. They
are forbidden unless branch restrictions prove them nonzero. This allows
future restrictions such as `u(x) != 0` to be useful without weakening the
default safety policy.

Denominator cancellation and clearing are separate operations. Removing a
factor from a denominator can exclude its zero set. For an
independent-variable factor, the default is to retain the original expression
unless the current domain already excludes the zero set; do not create domain
branches. For a dependent-variable factor, optional case-analysis mode may
create disjoint solution branches with the appropriate restriction.

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

### 4.6 Dependent-variable branch splitting

Only dependent-variable case splitting is part of this plan. It is a system
operation because it changes the `branches` vector, even though the reason for
a split is found while processing one branch. It should use the existing
`push_branch!` and fingerprint logic. Independent-variable conditions update
the single current `domain` on the branch; they never create
branches.

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
the original unsplit branch is retained. Ordinary simplification should leave
factorized equations unsplit; splitting is an explicit case-analysis feature
because every child must eventually be solved and the solution sets unioned.

### 4.7 Assumption-aware pseudocode

```julia
function _simplify_branch(branch, options)
    current = [branch]

    for _ in 1:options.max_passes
        next = DiffEqBranch[]
        for current_branch in current
            assumptions = _assumption_state(current_branch)
            normalized = _run_unconditional_branch_stages(
                current_branch, assumptions, options)
            candidates = _discover_assumption_candidates(
                normalized.branch, assumptions, options)
            outcomes = _apply_proven_candidates_or_split(
                normalized.branch, candidates, assumptions, options)

            for outcome in outcomes
                outcome_assumptions = _assumption_state(outcome)
                result = _run_unconditional_branch_stages(
                    outcome, outcome_assumptions, options)
                push!(next, result.branch)
            end
        end
        next = _deduplicate_branches(next)

        _branch_set_fingerprint(next) ==
            _branch_set_fingerprint(current) && break
        current = next
    end

    current
end
```

The exact return type can be specialized during implementation, but the
important interaction is fixed: every accepted proof-dependent rewrite is
followed by recollection and canonicalization in the same branch pass because
cancellation and function rewrites can expose new generator or coefficient
structure. This helper is not a second simplifier; it is the
assumption/proof portion of the integrated branch pipeline.

## 5. System reduction

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
integrated branch simplifier and must be opt-in.

### 5.2 Why system reduction is interleaved

The layers affect one another:

```text
branch normalization
    -> exposes comparable equations and pivots
system reduction
    -> substitutes or eliminates and creates new expressions
integrated branch normalization
    -> expands, collects, and canonicalizes those expressions
proof and restriction checks
    -> proves newly exposed cancellations
system reduction again
    -> discovers relations exposed by cleanup
```

Running system reduction only after all branch work misses relations exposed
by substitution. Running it only before branch work misses relations hidden by
different equation layouts. The system pass therefore runs after a branch
fixed point and is followed by the integrated branch simplifier on changed
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
    branch simplification fixed point on equations and boundary conditions
    proof/restriction checks interleaved with each pass
    classify identity/contradiction/conditions
    |
    v
if system reduction is enabled:
    repeat until system fixed point:
        discover relations across equations in each branch
        apply one safe relation batch
        run integrated branch simplification on changed branches
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

### Integrated branch simplification

- product and chain-rule derivative expansion;
- mixed and higher derivatives;
- polynomial generator collection;
- preservation of `exp(u')`, `sin(u'')`, and similar nonlinear atoms;
- coefficients containing other differential generators;
- deterministic canonical forms;
- identity, contradiction, and parameter-condition classification;
- derivative and expression node budgets.
- candidate rewrites rejected at the node limit;
- initially over-budget input expressions and size-reducing cleanup;
- temporary derivative/expansion overflow with rollback and diagnostics;
- over-budget equations skipped safely by system reduction.

### Proof, restriction, and branch behavior

- cancellation of proven nonzero numeric and parameter factors;
- refusal to cancel unknown or potentially zero factors;
- cancellation using explicit branch restrictions;
- denominator side-condition preservation;
- valid-domain restriction through `original_domain` plus
  `domain_restrictions`;
- function rules with sufficient and insufficient sign/reality assumptions;
- branch splitting, deduplication, and branch limits;
- immutable root preservation through branch transformations;
- `SimplificationStep(options)` in changed branch histories.

### System layer

- duplicate and scalar-multiple removal;
- substitution followed by local recollection;
- a local cleanup exposing a second system relation;
- polynomial elimination through a reversible `AtomTable`;
- inconsistent and redundant branch handling;
- preservation of boundary conditions and branch metadata;
- preservation of `root` and the current branch domain;
- differential-consequence mode disabled by default and gated when enabled.

Each accepted transformation needs an appropriate check:

```text
branch: residual canonicalization/equivalence under the branch's proven facts and side conditions
system: relation certificate or explicit branch decomposition
```

Domain restriction is checked separately: the new effective domain must be
`original_domain` plus the accepted `domain_restrictions`. The removed part is
not a solution-set decomposition and is therefore not stored or passed to a
solver. The immutable root remains available for optional provenance
comparisons, and the restriction source can be recorded in transformation
history or diagnostics if that explanation is needed.

## 9. Implementation order

1. Keep `simplify_system` as the public orchestration entry point and refactor
   its current helpers into explicit integrated branch stages.
2. Add immutable `SimplificationRoot` snapshots to `DiffEqSystem` construction
   and copying before transformations are implemented.
3. Implement residual canonicalization and identity/contradiction
   classification while preserving `DiffEqBranch` metadata.
4. Refactor `group_coefficients` into a safe collector with differential-term
   classification and nonlinear atom preservation.
5. Expand `SimplificationOptions` with shared budgets and branch/system policy
   switches;
   record the same options in `SimplificationStep`.
6. Implement valid-domain restriction through
   `DiffEqBranch.domain_restrictions` without independent-variable branch
   creation.
7. Add stable canonical fingerprints and ensure fixed-point checks use them.
8. Turn divisibility results into proof facts and implement certified
   cancellation with branch restrictions.
9. Wire assumption-checked `SYMBOLIC_RULE_GROUPS` into the integrated branch
   pass.
10. Implement duplicate/scalar-multiple system relations using canonical
    residuals.
11. Implement conservative substitutions and mandatory post-substitution
    integrated branch passes.
12. Add `AtomTable` and Nemo-backed polynomial operations for classified
    regions.
13. Add optional dependent-variable branch splitting and differential
    consequences only after
    their history, regularity, and solution-set semantics are tested.

This order produces useful behavior at every step and keeps the implementation
aligned with the existing architecture: one `DiffEqSystem` is simplified at a
time, branches carry assumptions and history, and `SimplificationOptions`
describes and records the complete run.

## Archive

Todo+ moves completed task lines here when `Todo: Archive` is run. Keep this
section at the end of the document so archived work remains separate from the
active task blocks and the design reference.
