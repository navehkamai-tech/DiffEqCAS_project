"""
Configuration for the system simplifier.

The pass limit is deliberately explicit. Simplification can increase
expression size, so the number of fixed-point passes is bounded.
"""
Base.@kwdef struct SimplificationOptions
    max_passes::Int = 4
    expand_mode::Symbol = :targeted
    enable_cancellation::Bool = true
    enable_factorization::Bool = false
end

struct SimplificationStep <: DerivationStep
    options::SimplificationOptions
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
        trivial_solutions=sys.restrictions,
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

I want to add in a step that is used only if there is more than one equation in sys.eqs, with an algorithm that simplifies the whole system rather than each equation separately. 
I don't know any more details, so for now this is all I'm adding

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

function _simplify_one_system(sys::DiffEqBranch, options::SimplificationOptions)
    current = sys

    # Each pass returns to a stable structural form before the next concern.
    for _ in 1:options.max_passes
        pass_start = current
        current = _apply_symbolic_stage(current, :structural)

        current = _apply_symbolic_stage(current, :grouping)

        if options.enable_cancellation
            current, _ = _cancel_system(current)
        end

        current = _apply_symbolic_stage(current, :functions)

        if options.enable_factorization
            current, _ = _factorization_stage(current)
        end

        current = _apply_symbolic_stage(current, :structural)

        isequal(current.eqs, pass_start.eqs) &&
            isequal(current.bcs, pass_start.bcs) &&
            break
    end

    if !isequal(current.eqs, sys.eqs) || !isequal(current.bcs, sys.bcs)
        current = DiffEqBranch(
            identifier=sys.identifier,
            eqs=current.eqs, ivs=current.ivs, dvs=current.dvs, ps=current.ps,
            bcs=current.bcs, domain=current.domain, name=current.name,
            domain_set=current.domain_set, trivial_solutions=current.restrictions,
            history=append_derivation(sys.history,
                SimplificationStep(options)),
        )
    end
    current
end

"""
    simplify_system(sys; options...)

Simplify every branch in a system through the staged pipeline and return the
resulting `DiffEqSystem`.

Factorization remains an optional canonicalization stage controlled by
`SimplificationOptions.enable_factorization`. It does not split branches;
solution-set decomposition belongs to the separate factorization/derivation
pipeline.

The input is not mutated. A changed branch receives one aggregate
`SimplificationStep`; internal passes are deliberately not recorded as
separate derivation steps.
"""
function simplify_system(sys::DiffEqSystem;
    options=SimplificationOptions())
    DiffEqSystem([
        _simplify_one_system(branch, options)
        for branch in sys.branches
    ])
end

function _canonicalize_branch!(branch::DiffEqBranch)
    # TODO: add the logic that canonicalizes a DiffEqBranch, meaning the order of the vector fields eqs, bcs, ivs, dvs, ps, and that within eqs and bcs the objects themselves are normalized 
    for eq in branch.ps
        eq = eq.lhs-eq.rhs~0
    end
    sorted_eqs = sort(branch.eqs.lhs-branch.eqs.rhs, by=string)
    sorted_bcs = sort(branch.bcs, by=string)
    sorted_ivs = sort(branch.ivs, by=string)
    sorted_dvs = sort(branch.dvs, by=string)
    sorted_ps = sort(branch.ps, by=string)

    _replace_branch!(branch, sorted_eqs, sorted_ivs, sorted_dvs, sorted_ps, sorted_bcs, branch.domain, branch.history)
end
