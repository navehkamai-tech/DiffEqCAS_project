"""
Configuration for the system simplifier.

The limits are deliberately explicit.  Simplification can increase expression
size or branch count, so an unresolved result must be returned rather than
silently spending unbounded time trying to reach a smaller expression.
"""
Base.@kwdef struct SimplificationOptions
    max_passes::Int = 4
    max_branches::Int = 128
    max_steps::Int = 1024
    expand_mode::Symbol = :targeted
    enable_cancellation::Bool = true
    enable_factorization::Bool = false
    enable_branching::Bool = false
end

struct SimplificationStep <: DerivationStep
    stage::Symbol
    before::Any
    after::Any
    detail::Any
end

struct SimplificationResult
    system::DiffEqSystem
    trace::Vector{SimplificationStep}
    status::Symbol
end

function Base.getproperty(result::SimplificationResult, name::Symbol)
    name === :systems && return getfield(result, :system).branches
    getfield(result, name)
end

"""
State owned by one call to `simplify_system`.

`pending` is a depth-first worklist.  `completed` contains terminal systems.
The global `working_systems` in `base.jl` remains available for compatibility
and debugging, but the pipeline itself owns a fresh run object so nested or
independent system operations cannot consume another run's work.
"""
mutable struct SimplificationRun
    system::DiffEqSystem
    trace::Vector{SimplificationStep}
    options::SimplificationOptions
    steps::Int
end

function SimplificationRun(system::DiffEqSystem,
                            options::SimplificationOptions=SimplificationOptions())
    run = DiffEqSystem()
    foreach(branch -> push_branch!(run, branch), system.branches)
    SimplificationRun(run, SimplificationStep[], options, 0)
end

_simplification_expression(eq::Symbolics.Equation) = unwrap(eq.lhs - eq.rhs)

"""
Build a system from transformed residual expressions while preserving all
system metadata.  Boundary conditions are normalized by the same expression
normalizer but are never subjected to equation splitting in this pass.
"""
function _with_simplified_expressions(sys::DiffEqBranch, eqs, bcs)
    DiffEqBranch(
        identifier=sys.identifier,
        eqs=eqs,
        ivs=sys.ivs,
        dvs=sys.dvs,
        ps=sys.ps,
        bcs=bcs,
        domain=sys.domain,
        name=sys.name,
        domain_set=sys.domain_set,
        trivial_solutions=sys.trivial_sols,
        history=sys.history,
    )
end

"""
Stage-specific canonicalization.

The normal forms are intentionally local:
* `:structural` exposes derivatives and arithmetic without distributing all
  products;
* `:grouping` distributes multiplication over addition so differential
  generators can be collected;
* `:functions` recursively normalizes function arguments;
* `:factorization` exposes a polynomial-like expression in algebraic atoms.

Each mode is a hook for a more precise normalizer.  Keeping the policy here
prevents every later stage from independently expanding the same expression.
"""
function _stage_normalize(expr, mode::Symbol)
    normalized = expand_derivatives(wrap(expr))
    mode === :structural && return unwrap(simplify(normalized))

    if mode in (:grouping, :factorization)
        normalized = expand(normalized)
    end

    # TODO: Add a recursive argument normalizer for exp/log/trigonometric
    # functions.  It should collect additive arguments and normalize signs
    # without expanding unrelated subexpressions.
    unwrap(simplify(normalized))
end

function _stage_normalize_relation(eq::Symbolics.Equation, mode)
    _stage_normalize(_simplification_expression(eq), mode) ~ 0
end

function _stage_normalize_boundary(bc::Symbolics.Equation, mode)
    wrap(_stage_normalize(unwrap(bc.lhs), mode)) ~
        wrap(_stage_normalize(unwrap(bc.rhs), mode))
end

"""
Apply the currently safe symbolic rewrite layer.

`SPECIAL_REWRITER` contains structural derivative and registered special-
function rules.  The semantic rule groups in `simplification.jl` are organized
by required assumptions and stage (`SYMBOLIC_RULE_GROUPS`), but are not all
enabled here yet: several require domain or branch assumptions.
`_apply_function_rules` is the explicit hook where that assumption-aware rule
selection will be added.
"""
function _apply_function_rules(expr)
    rewritten = SPECIAL_REWRITER(wrap(expr))
    simplify(rewritten)
end

function _apply_symbolic_stage(sys::DiffEqBranch, mode::Symbol)
    eqs = Symbolics.Equation[]
    bcs = Symbolics.Equation[]
    for eq in sys.eqs
        normalized = _stage_normalize_relation(eq, mode)
        push!(eqs, _apply_function_rules(normalized.lhs) ~ 0)
    end
    for bc in sys.bcs
        normalized = _stage_normalize_boundary(bc, mode)
        push!(bcs, _apply_function_rules(normalized.lhs) ~
            _apply_function_rules(normalized.rhs))
    end
    _with_simplified_expressions(sys, eqs, bcs)
end

"""
Cancel only domain-certified common factors.

Candidate discovery and semantic cancellation are deliberately separate:
`common_divisors` proposes factors, while `factor_divisibility` decides
whether each factor is nonzero throughout the current system domain.

TODO: preserve factor multiplicities and provenance in a FactorCandidate
record.  The current hook uses the existing candidate API and cancels one
factor at a time; a failed or unresolved candidate is left untouched.
"""
function _cancel_certified_residual(residual, sys::DiffEqBranch)
    current = wrap(residual)
    cancelled = Any[]
    for candidate in common_divisors(current, sys)
        candidate_num = wrap(candidate)
        _can_divide_by(candidate_num, sys) || continue
        next = simplify(current / candidate_num)
        isequal(unwrap(next), unwrap(current)) && continue
        current = next
        push!(cancelled, candidate)
    end
    current, cancelled
end

function _cancel_system(sys::DiffEqBranch)
    eqs = Symbolics.Equation[]
    details = Any[]
    for eq in sys.eqs
        residual, cancelled = _cancel_certified_residual(
            _simplification_expression(eq), sys)
        push!(eqs, simplify(residual) ~ 0)
        push!(details, cancelled)
    end
    _with_simplified_expressions(sys, eqs, sys.bcs), details
end

"""
Run the factorization hook.

The first implementation intentionally does not factor differential operators.
The future Nemo bridge should map dependent variables and derivative
expressions to reversible algebraic atoms, factor only polynomial residuals,
and expand the result again to verify equivalence.
"""
function _factorization_stage(sys::DiffEqBranch)
    # TODO: classify each residual as polynomial in selected differential atoms.
    # TODO: construct a reversible Symbolics <-> Nemo atom map.
    # TODO: reject unsupported transcendental coefficients conservatively.
    # TODO: round-trip the factored residual through expansion before accepting.
    sys, :not_implemented
end

"""
Run the branch-generation hook.

A future implementation will turn a certified factorization `A * B = 0`
into two systems, both inheriting the current domain and boundary conditions.
Any branch-specific nonzero assumptions must be added to that branch's domain
before it is pushed.  No branch is created by this placeholder.
"""
function _branch_stage(sys::DiffEqBranch)
    # TODO: remove constant nonzero factors and reject impossible factors.
    # TODO: create one copied system per dependent-variable factor.
    # TODO: deduplicate equivalent branches and enforce max_branches.
    [sys], :not_implemented
end

function _record!(run, stage, before, after, detail=nothing)
    push!(run.trace, SimplificationStep(stage, before, after, detail))
end

function _simplify_one_system!(run::SimplificationRun, sys::DiffEqBranch)
    current = sys

    # Each pass returns to a stable structural form before the next concern.
    for _ in 1:run.options.max_passes
        before = current
        current = _apply_symbolic_stage(current, :structural)
        _record!(run, :derivative_normalization, before, current)

        before = current
        current = _apply_symbolic_stage(current, :grouping)
        _record!(run, :grouping_normalization, before, current)

        if run.options.enable_cancellation
            before = current
            current, detail = _cancel_system(current)
            _record!(run, :certified_cancellation, before, current, detail)
        end

        before = current
        current = _apply_symbolic_stage(current, :functions)
        _record!(run, :function_simplification, before, current)

        if run.options.enable_factorization
            before = current
            current, detail = _factorization_stage(current)
            _record!(run, :factorization, before, current, detail)
        end

        before = current
        current = _apply_symbolic_stage(current, :structural)
        _record!(run, :recollection, before, current)

        isequal(current.eqs, before.eqs) && isequal(current.bcs, before.bcs) &&
            return current
    end

    if !isequal(current.eqs, sys.eqs) || !isequal(current.bcs, sys.bcs)
        current = DiffEqBranch(
            identifier=sys.identifier,
            eqs=current.eqs, ivs=current.ivs, dvs=current.dvs, ps=current.ps,
            bcs=current.bcs, domain=current.domain, name=current.name,
            domain_set=current.domain_set, trivial_solutions=current.trivial_sols,
            history=append_derivation(sys.history,
                SimplificationStep(:pipeline, sys, current, nothing)),
        )
    end
    current
end

"""
    simplify_system(sys; options...)

Simplify one system through the staged pipeline.  The result always contains
the terminal systems, including systems produced by future factor splitting.
The current implementation has one branch; the worklist and branch hook are
already wired so adding decomposition does not change this public contract.
"""
function simplify_system(sys::DiffEqSystem;
                         options=SimplificationOptions())
    run = SimplificationRun(sys, options)
    while !isempty(run.system.pending)
        run.steps += 1
        if run.steps > options.max_steps
            return SimplificationResult(run.system, run.trace, :max_steps)
        end

        current = pop!(run.system.pending)
        simplified = _simplify_one_system!(run, current)
        branches, branch_status = options.enable_branching ?
            _branch_stage(simplified) : ([simplified], :not_requested)

        if length(run.system.completed) + length(run.system.pending) +
            length(branches) >
            options.max_branches
            return SimplificationResult(run.system, run.trace, :max_branches)
        end

        # A real split returns branches to the worklist so every child gets
        # the same normalization/cancellation/finalization treatment.  The
        # placeholder hook is terminal and therefore records the current
        # system exactly once.
        if branch_status === :split
            foreach(branch -> push_branch!(run.system, branch), branches)
        else
            foreach(branch -> complete_branch!(run.system, branch), branches)
        end
    end

    run.system.branches = run.system.completed
    SimplificationResult(run.system, run.trace, :fixed_point)
end
