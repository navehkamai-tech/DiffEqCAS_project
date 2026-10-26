# paving specific utils
_box_contains(x, box) = all(k -> in_interval(x[k], _bi(box[k])), eachindex(x))
# True iff every coordinate is a nonempty degenerate interval [a, a].
function _is_point(box)
    for k in 1:length(box)
        iv = _bi(box[k])
        (isempty_interval(iv) || inf(iv) != sup(iv)) && return false
    end
    return true
end

const _MAX_MASKED = 64               # constraints tracked by the UInt64 mask
# ===========================================================================
# Flat Tape-Compiled HC4Revise Engine
# ===========================================================================

@enum _OpCode::UInt8 begin
    OP_ADD
    OP_SUB
    OP_NEG
    OP_MUL
    OP_DIV
    OP_POW_INT
    OP_POW
    OP_ABS
    OP_SIGN
    OP_EXP
    OP_EXP2
    OP_EXP10
    OP_LOG
    OP_LOG2
    OP_LOG10
    OP_SIN
    OP_COS
    OP_TAN
    OP_ASIN
    OP_ACOS
    OP_ATAN
    OP_SINH
    OP_COSH
    OP_TANH
    OP_ASINH
    OP_ACOSH
    OP_ATANH
end

struct _TapeInstruction
    op::_OpCode
    out_idx::Int
    arg1::Int      # For n-ary (+, *), start index in `nary_args`
    arg2::Int      # For n-ary (+, *), end index in `nary_args`; for OP_POW_INT, integer exponent
end

"""
    MVFPlan
 
Per-tape mean-value state. `multi` is static. `vars`/`dtapes` (parallel; the
variables the form is applied to, cheapest derivative first) are filled lazily by
`_mvf_build!`. `state`: 0 not built, 1 ready, -1 unusable. `fails`/`skip` drive
the back-off; `tries`/`hits` are diagnostics (see `_mvf_report`).
The counters are plain fields: sharing one prepared system across threads can
make them inexact, which only affects the heuristic, never soundness.
"""
mutable struct MVFPlan <: _AbstractMVFPlan
    residual::Symbolics.Num
    variables::Vector
    multi::Vector{Int}
    lock::ReentrantLock
    state::Threads.Atomic{Int}
    vars::Vector{Int}
    dtapes::Vector{CompiledHC4}
    need_len::Int
    fails::Int
    skip::Int
    tries::Int
    hits::Int
end

"""
    CompiledHC4

A flat, zero-allocation Wengert tape representation of a `SymRelation` for a fixed variable ordering.
- Indices `1:num_vars` in the tape workspace correspond to the input `variables`.
- Indices `num_vars+1 : num_vars+length(constants)` hold literal constants.
- Subsequent indices hold intermediate call nodes up to `root_idx`.
"""
struct CompiledHC4
    num_vars::Int
    constants::Vector{_BI}
    instructions::Vector{_TapeInstruction}
    nary_args::Vector{Int}
    root_idx::Int
    confine::_BI
    rel::Symbol
    tape_len::Int
    mvf::Union{Nothing,MVFPlan}
end

struct _Prepared
    tapes::Vector{CompiledHC4}
    dropped::Bool            # some constraint was NOT compiled -> `:sat` is off the table
    max_len::Int             # workspace length needed
end

const _NO_TAPES = _Prepared(CompiledHC4[], false, 0)

_workspaces(p::_Prepared) = (Vector{_BI}(undef, p.max_len), Vector{_DI}(undef, p.max_len))
Vector{_DI}


const MVF_MAX_COST_RATIO = 6.0   # total derivative tape length / tape length
const MVF_ABORT_RATIO = 1.0      # abort when width(Σ terms) >= ratio * width(F_nat)
const MVF_MIN_GAIN = 0.05        # fraction of the relevant width that counts as a gain
const MVF_MAX_BACKOFF_EXP = 6    # skip at most 2^6 - 1 = 63 calls after repeated failures

MVFPlan(residual, variables, multi) =
    MVFPlan(residual, collect(variables), multi, ReentrantLock(), Threads.Atomic{Int}(0),
        Int[], CompiledHC4[], 0, 0, 0, 0, 0)

function _give_confine(rel)
    if rel === _LT || rel === _LE
        return _bi(-Inf, 0.0)
    elseif rel === _GT || rel === _GE
        return _bi(0.0, Inf)
    elseif rel === _EQ
        return _bi(0.0, 0.0)
    elseif rel === _NE
        return _entire_bi()
    end
    throw(ArgumentError("Argument must be a supported relation, got $rel"))
end

function _map_opcode(op, arity::Int, arg2_is_int::Bool)
    op === (+) && return OP_ADD
    op === (-) && return arity == 1 ? OP_NEG : OP_SUB
    op === (*) && return OP_MUL
    op === (/) && return OP_DIV
    op === (^) && return arg2_is_int ? OP_POW_INT : OP_POW
    op === abs && return OP_ABS
    op === sign && return OP_SIGN
    op === exp && return OP_EXP
    op === exp2 && return OP_EXP2
    op === exp10 && return OP_EXP10
    op === log && return OP_LOG
    op === log2 && return OP_LOG2
    op === log10 && return OP_LOG10
    op === sin && return OP_SIN
    op === cos && return OP_COS
    op === tan && return OP_TAN
    op === asin && return OP_ASIN
    op === acos && return OP_ACOS
    op === atan && return OP_ATAN
    op === sinh && return OP_SINH
    op === cosh && return OP_COSH
    op === tanh && return OP_TANH
    op === asinh && return OP_ASINH
    op === acosh && return OP_ACOSH
    op === atanh && return OP_ATANH
    throw(ArgumentError("Unsupported operation in HC4Revise: $op"))
end

function _const_interval(v::Real)
    if v isa AbstractFloat || (v isa Integer && abs(v) <= 2^53)
        return _bi(v)
    end
    x = Float64(v)
    return _bi(prevfloat(x), nextfloat(x))
end

"""
    compile_hc4(relation::SymRelation, variables; mvf=false) -> CompiledHC4
 
Compile a symbolic relation into a flat `CompiledHC4` tape once before paving.
 
With `mvf=true` the tape additionally gets a mean-value plan (`MVFPlan`) when the
expression could profit from one: it must be differentiable (no `abs`/`sign`) and
some variable must occur more than once (dependency problem). Otherwise `tape.mvf`
is `nothing`. Derivative tapes themselves are compiled lazily, on first use.
"""
function compile_hc4(relation::SymRelation, variables; mvf::Bool=false)
    base = _compile_hc4_residual(relation.residual, relation.relation, variables)
    mvf || return base
    plan = _build_mvf_plan(base, relation, variables)
    return plan === nothing ? base : _with_mvf(base, plan)
end

# Same tape, with a mean-value plan attached.
_with_mvf(t::CompiledHC4, plan::_AbstractMVFPlan) =
    CompiledHC4(t.num_vars, t.constants, t.instructions, t.nary_args, t.root_idx,
        t.confine, t.rel, t.tape_len, plan)


# Internal compiler for raw residuals, especially symbolic derivatives that must
# not be rescaled or negated by SymRelation canonicalization.
function _compile_hc4_residual(root_residual, rel::Symbol, variables)
    num_vars = length(variables)
    unwrapped_vars = [Symbolics.unwrap(v) for v in variables]

    # Map AST nodes to tape indices (handles DAG common subexpressions automatically)
    node_to_idx = Dict{Any,Int}()
    for (i, uv) in enumerate(unwrapped_vars)
        node_to_idx[uv] = i
    end

    constants = _BI[]
    call_nodes = Any[]

    function _collect_postorder!(expr)
        haskey(node_to_idx, expr) && return
        if !SU.iscall(expr)
            val = SU.unwrap_const(expr)
            if val isa Real
                push!(constants, _const_interval(val))
                node_to_idx[expr] = num_vars + length(constants)
                return
            else
                throw(ArgumentError("Unrecognized symbolic leaf in constraint: $expr"))
            end
        end

        for arg in SU.arguments(expr)
            _collect_postorder!(arg)
        end

        push!(call_nodes, expr)
        # Placeholder negative index; shifted once total constant count is known
        node_to_idx[expr] = -length(call_nodes)
    end

    root_expr = Symbolics.unwrap(root_residual)
    _collect_postorder!(root_expr)

    num_consts = length(constants)
    for (k, v) in node_to_idx
        if v < 0
            node_to_idx[k] = num_vars + num_consts + (-v)
        end
    end

    instructions = Vector{_TapeInstruction}(undef, length(call_nodes))
    nary_args = Int[]

    for (idx, expr) in enumerate(call_nodes)
        out_idx = num_vars + num_consts + idx
        op = SU.operation(expr)
        args = SU.arguments(expr)
        arity = length(args)

        if op === (+) || op === (*)
            opcode = op === (+) ? OP_ADD : OP_MUL
            start_pos = length(nary_args) + 1
            for a in args
                push!(nary_args, node_to_idx[a])
            end
            end_pos = length(nary_args)
            instructions[idx] = _TapeInstruction(opcode, out_idx, start_pos, end_pos)
        elseif op === (^)
            exp_val = SU.unwrap_const(args[2])
            if exp_val isa Integer
                instructions[idx] = _TapeInstruction(OP_POW_INT, out_idx, node_to_idx[args[1]], Int(exp_val))
            else
                instructions[idx] = _TapeInstruction(OP_POW, out_idx, node_to_idx[args[1]], node_to_idx[args[2]])
            end
        elseif arity == 1
            opcode = _map_opcode(op, 1, false)
            instructions[idx] = _TapeInstruction(opcode, out_idx, node_to_idx[args[1]], 0)
        elseif arity == 2
            opcode = _map_opcode(op, 2, false)
            instructions[idx] = _TapeInstruction(opcode, out_idx, node_to_idx[args[1]], node_to_idx[args[2]])
        else
            throw(ArgumentError("Unsupported arity $arity for operation $op"))
        end
    end

    root_idx = node_to_idx[root_expr]
    confine = _give_confine(rel)
    tape_len = num_vars + num_consts + length(call_nodes)

    return CompiledHC4(num_vars, constants, instructions, nary_args, root_idx, confine, rel, tape_len)
end

"""
Compile `constraints` over `variables`. Constraints that cannot be compiled
(unsupported operation, symbol outside `variables` such as a parameter) and those
beyond the 64 the bitmask can track are dropped. Dropping is sound for `:unsat`
and for contraction, never for `:sat`, hence the `dropped` flag. Put the most
valuable constraint (the probe) first.
"""
function _prepare(constraints, variables)::_Prepared
    N = length(variables)
    tapes = CompiledHC4[]
    dropped = false
    for c in constraints
        if length(tapes) >= _MAX_MASKED
            dropped = true
            break
        end
        try
            push!(tapes, compile_hc4(c.relation, variables))
        catch e
            e isa ArgumentError || rethrow()
            dropped = true
        end
    end
    max_len = maximum((t.tape_len for t in tapes); init=N)
    return _Prepared(tapes, dropped, max_len)
end

#---------------------------------------------------------------------------------
# Mean Valued Forms
#---------------------------------------------------------------------------------

# Call `f(idx)` for every operand index of `inst`. (`arg2` is an exponent, not an
# index, for OP_POW_INT, and unused for other unary ops.)
@inline function _foreach_operand(f::F, tape::CompiledHC4, inst::_TapeInstruction) where {F}
    op = inst.op
    if op == OP_ADD || op == OP_MUL
        for k in inst.arg1:inst.arg2
            f(tape.nary_args[k])
        end
    elseif op == OP_SUB || op == OP_DIV || op == OP_POW
        f(inst.arg1)
        f(inst.arg2)
    else
        f(inst.arg1)
    end
    return nothing
end

# Gate 1. `abs`/`sign` are not differentiable everywhere, so the theorem fails.
function _mvf_differentiable(tape::CompiledHC4)
    for inst in tape.instructions
        (inst.op == OP_ABS || inst.op == OP_SIGN) && return false
    end
    return true
end

# Gate 2. Indices of variables with >= 2 occurrences, counted over root-to-leaf
# paths of the DAG (saturating at 2). Instructions are in post-order, so one reverse
# sweep propagates path counts from the root to the leaves.
function _mvf_multi_occurrence(tape::CompiledHC4)::Vector{Int}
    paths = zeros(Int, tape.tape_len)
    paths[tape.root_idx] = 1
    for n in length(tape.instructions):-1:1
        inst = tape.instructions[n]
        p = paths[inst.out_idx]
        p == 0 && continue
        _foreach_operand(tape, inst) do a
            paths[a] = min(paths[a] + p, 2)
        end
    end
    return Int[i for i in 1:tape.num_vars if paths[i] >= 2]
end

function _build_mvf_plan(tape::CompiledHC4, relation::SymRelation, variables)
    _mvf_differentiable(tape) || return nothing
    multi = _mvf_multi_occurrence(tape)
    isempty(multi) && return nothing
    return MVFPlan(relation.residual, variables, multi)
end

# Symbolic ∂residual/∂variable compiled to a tape; `nothing` if it cannot be.
function _compile_partial(residual, variable, variables)
    try
        derivative = Symbolics.derivative(residual, variable; simplify=true)
        return _compile_hc4_residual(derivative, _EQ, variables)
    catch err
        (err isa InterruptException || err isa OutOfMemoryError) && rethrow()
        return nothing
    end
end

function _is_zero_tape(t::CompiledHC4)
    isempty(t.instructions) && t.root_idx > t.num_vars || return false
    c = t.constants[t.root_idx-t.num_vars]
    return inf(c) == 0.0 && sup(c) == 0.0
end

# Gates 3-4. Compile the derivatives (once) and pick the variables within budget.
# Returns the new state.
function _mvf_build!(plan::MVFPlan, tape::CompiledHC4)::Int
    return lock(plan.lock) do
        s = plan.state[]
        s != 0 && return s
        cand = Tuple{Int,CompiledHC4}[]
        for i in plan.multi
            dt = _compile_partial(plan.residual, plan.variables[i], plan.variables)
            (dt === nothing || _is_zero_tape(dt)) && continue
            push!(cand, (i, dt))
        end
        sort!(cand; by=c -> c[2].tape_len)
        budget = MVF_MAX_COST_RATIO * tape.tape_len
        spent = 0
        vars = Int[]
        dtapes = CompiledHC4[]
        need = tape.tape_len
        for (i, dt) in cand
            spent + dt.tape_len > budget && break
            spent += dt.tape_len
            push!(vars, i)
            push!(dtapes, dt)
            need = max(need, dt.tape_len)
        end
        plan.vars = vars
        plan.dtapes = dtapes
        plan.need_len = need
        plan.state[] = isempty(vars) ? -1 : 1     # published last
        return plan.state[]
    end
end

@inline _mvf_active(x::_BI) = (d=diam(x); 0.0 < d < Inf)

function _mvf_fail!(plan::MVFPlan)
    plan.fails += 1
    plan.skip = (1 << min(plan.fails, MVF_MAX_BACKOFF_EXP)) - 1
    return nothing
end

"""
    _mvf_refine!(tape, plan, ws, dws, F_nat) -> Union{Nothing,_BI}
 
Called by `HC4Revise` after the bare forward pass, when the status is `:unknown`.
`ws[1:N]` holds the box. Returns an enclosure of f(box) contained in `F_nat`, or
`nothing` when the form was not applicable or not worth finishing (the caller
then proceeds with `F_nat`). Only `dws` is used as scratch; `ws` is never touched,
so the reverse pass is unaffected. The returned interval, when `:inside`, is backed by
a decorated whole-box check, so the caller may return `:inside` without a second
definedness pass.
"""
function _mvf_refine!(tape::CompiledHC4, plan::MVFPlan, ws::Vector{_BI}, dws::Vector{_DI},
    F_nat::_BI)::Union{Nothing,_BI}

    plan.state[] < 0 && return nothing

    # (6) free gates
    w_nat = diam(F_nat)
    w_nat > 0.0 || return nothing
    any_active = false
    @inbounds for k in plan.multi
        if _mvf_active(ws[k])
            any_active = true
            break
        end
    end
    any_active || return nothing

    # (7) back-off throttles only work that would otherwise be paid for
    if plan.skip > 0
        plan.skip -= 1
        return nothing
    end

    # (4) lazy compile
    plan.state[] == 0 && _mvf_build!(plan, tape)
    plan.state[] < 0 && return nothing
    length(dws) < plan.need_len && resize!(dws, plan.need_len)
    plan.tries += 1
    N = tape.num_vars
    vars = plan.vars

    # (8) f defined and continuous on the whole box
    @inbounds for i in 1:N
        dws[i] = interval(ws[i])
    end
    decoration(_execute_forward!(tape, dws)) >= dac || return _mvf_fail!(plan)

    # base = f(X_R, c_S): S-variables with a usable term go to their midpoint
    nact = 0
    @inbounds for k in vars
        if _mvf_active(ws[k])
            dws[k] = interval(_bi(mid(ws[k])))
            nact += 1
        end
    end
    nact == 0 && return nothing
    base = bareinterval(_execute_forward!(tape, dws))
    isempty_interval(base) && return _mvf_fail!(plan)

    # Σ D_k (X_k - c_k), Hansen order: dws[k] widens to X_k just before D_k is
    # evaluated, so earlier variables are at X and later ones still at c.
    acc = _bi(0.0, 0.0)
    @inbounds for j in eachindex(vars)
        k = vars[j]
        Xk = ws[k]
        _mvf_active(Xk) || continue
        dws[k] = interval(Xk)
        D = _execute_forward!(plan.dtapes[j], dws)
        decoration(D) >= dac || return _mvf_fail!(plan)           # (9)
        acc = acc + bareinterval(D) * (Xk - _bi(mid(Xk)))
        diam(acc) >= MVF_ABORT_RATIO * w_nat && return _mvf_fail!(plan)  # (10)
    end

    F = intersect_interval(F_nat, base + acc)
    isempty_interval(F) && return _mvf_fail!(plan)   # impossible for sound enclosures

    # success bookkeeping, measured on what the reverse pass actually sees
    decided = _eval_relation_status(tape.rel, F) !== :unknown
    gained = decided || _significant_reduction(
        intersect_interval(F_nat, tape.confine), intersect_interval(F, tape.confine), MVF_MIN_GAIN)
    if gained
        plan.hits += 1
        plan.fails = 0
    else
        plan.fails += 1
        plan.skip = (1 << min(plan.fails, MVF_MAX_BACKOFF_EXP)) - 1
    end
    return F      # sound and no wider than F_nat, so usable even without a "gain"
end

"""
    _mvf_report(prep::_Prepared) -> Vector{NamedTuple}
 
Per-constraint diagnostics: whether it has a plan, how many times it was fully
evaluated (`tries`), how often it paid off (`hits`), and the variables used.
"""
_mvf_report(prep::_Prepared) = [
    tape.mvf === nothing ? (plan=false, tries=0, hits=0, vars=Int[]) :
    (plan=true, tries=(tape.mvf::MVFPlan).tries, hits=(tape.mvf::MVFPlan).hits,
        vars=copy((tape.mvf::MVFPlan).vars))
    for tape in prep.tapes]

# ---------------------------------------------------------------------------
# Elemental Reverse Contractors & Helpers
# ---------------------------------------------------------------------------

function _widen_periodic(X_orig::_BI, period::Float64, branches::_BI...)
    isempty_interval(X_orig) && return _empty_bi()
    result = _empty_bi()
    inf_X, sup_X = inf(X_orig), sup(X_orig)

    for branch in branches
        isempty_interval(branch) && continue
        k_min_f = floor((inf_X - sup(branch)) / period)
        k_max_f = ceil((sup_X - inf(branch)) / period)
        # Guard against unbounded domains [-Inf, Inf] causing infinite loops
        if !isfinite(k_min_f) || !isfinite(k_max_f) || (k_max_f - k_min_f) > 1.0e6
            return X_orig
        end
        k_min = Int(k_min_f)
        k_max = Int(k_max_f)
        p_bi = _bi(period)
        for k in k_min:k_max
            shifted_branch = branch + _bi(k) * p_bi
            result = hull(result, intersect_interval(shifted_branch, X_orig))
        end
    end
    return result
end

# Safe reverse multiplication: solves `a * b ∈ c` for `a`, intersecting with `a_orig`
@inline function _rev_mul(c::_BI, b::_BI, a_orig::_BI)
    isempty_interval(c) && return _empty_bi()
    isempty_interval(b) && return _empty_bi()

    # If 0 ∈ b
    if inf(b) <= 0.0 <= sup(b)
        # If 0 ∈ c as well, 0 * a = 0 satisfies the constraint for any a!
        (inf(c) <= 0.0 <= sup(c)) && return a_orig

        # If 0 ∉ c, split b into negative and positive rays to avoid losing bounds
        res = _empty_bi()
        if inf(b) < 0.0
            b_neg = _bi(inf(b), -0.0)
            res = hull(res, intersect_interval(c / b_neg, a_orig))
        end
        if sup(b) > 0.0
            b_pos = _bi(0.0, sup(b))
            res = hull(res, intersect_interval(c / b_pos, a_orig))
        end
        return res
    end
    return intersect_interval(c / b, a_orig)
end

# Safe reverse integer power: solves `x^n ∈ c` for `x`, intersecting with `x_orig`
@inline function _rev_pow_int(c::_BI, n::Int, x_orig::_BI)
    isempty_interval(c) && return _empty_bi()
    if n == 0
        return (inf(c) <= 1.0 <= sup(c)) ? x_orig : _empty_bi()
    elseif n < 0
        # x^(-k) = (1/x)^k ∈ c  =>  x^k ∈ 1 / c
        inv_c = _rev_mul(_bi(1.0), c, _entire_bi())
        return _rev_pow_int(inv_c, -n, x_orig)
    end

    if iseven(n)
        sup(c) < 0.0 && return _empty_bi()
        low = max(0.0, inf(c))
        root_iv = _bi(low, sup(c)) ^ _bi(1.0 / n)
        pos_branch = intersect_interval(root_iv, x_orig)
        neg_branch = intersect_interval(-root_iv, x_orig)
        return hull(pos_branch, neg_branch)
    else
        # Odd power: monotonic over ℝ
        inf_c, sup_c = inf(c), sup(c)
        inv_n = _bi(1.0 / n)
        r_low = inf_c >= 0.0 ? inf(_bi(inf_c)^inv_n) : -sup(_bi(-inf_c)^inv_n)
        r_high = sup_c >= 0.0 ? sup(_bi(sup_c)^inv_n) : -inf(_bi(-sup_c)^inv_n)
        return intersect_interval(_bi(r_low, r_high), x_orig)
    end
end

# --- forward pass (generic over bare / decorated workspace) -----------------
@inline _forward_pow_int(x::_BI, n::Int) = pow(x, n)
@inline _forward_pow_int(x::_DI, n::Int) = x^n

# ---------------------------------------------------------------------------
# Fast Tape Forward & Reverse Execution
# ---------------------------------------------------------------------------

function _execute_forward!(tape::CompiledHC4, workspace::Vector{W}) where {W}
    @inbounds begin
        for i in 1:length(tape.constants)
            workspace[tape.num_vars+i] = _lift(W, tape.constants[i])
        end

        nary = tape.nary_args
        for inst in tape.instructions
            op = inst.op
            out = inst.out_idx
            a1 = inst.arg1
            a2 = inst.arg2

            if op == OP_ADD
                acc = workspace[nary[a1]]
                for k in (a1+1):a2
                    acc = acc + workspace[nary[k]]
                end
                workspace[out] = acc
            elseif op == OP_MUL
                acc = workspace[nary[a1]]
                for k in (a1+1):a2
                    acc = acc * workspace[nary[k]]
                end
                workspace[out] = acc
            elseif op == OP_SUB
                workspace[out] = workspace[a1] - workspace[a2]
            elseif op == OP_NEG
                workspace[out] = -workspace[a1]
            elseif op == OP_DIV
                workspace[out] = workspace[a1] / workspace[a2]
            elseif op == OP_POW_INT
                workspace[out] = _forward_pow_int(workspace[a1], a2)
            elseif op == OP_POW
                workspace[out] = workspace[a1] ^ workspace[a2]
            elseif op == OP_ABS
                workspace[out] = abs(workspace[a1])
            elseif op == OP_SIGN
                workspace[out] = sign(workspace[a1])
            elseif op == OP_EXP
                workspace[out] = exp(workspace[a1])
            elseif op == OP_EXP2
                workspace[out] = exp2(workspace[a1])
            elseif op == OP_EXP10
                workspace[out] = exp10(workspace[a1])
            elseif op == OP_LOG
                workspace[out] = log(workspace[a1])
            elseif op == OP_LOG2
                workspace[out] = log2(workspace[a1])
            elseif op == OP_LOG10
                workspace[out] = log10(workspace[a1])
            elseif op == OP_SIN
                workspace[out] = sin(workspace[a1])
            elseif op == OP_COS
                workspace[out] = cos(workspace[a1])
            elseif op == OP_TAN
                workspace[out] = tan(workspace[a1])
            elseif op == OP_ASIN
                workspace[out] = asin(workspace[a1])
            elseif op == OP_ACOS
                workspace[out] = acos(workspace[a1])
            elseif op == OP_ATAN
                workspace[out] = atan(workspace[a1])
            elseif op == OP_SINH
                workspace[out] = sinh(workspace[a1])
            elseif op == OP_COSH
                workspace[out] = cosh(workspace[a1])
            elseif op == OP_TANH
                workspace[out] = tanh(workspace[a1])
            elseif op == OP_ASINH
                workspace[out] = asinh(workspace[a1])
            elseif op == OP_ACOSH
                workspace[out] = acosh(workspace[a1])
            elseif op == OP_ATANH
                workspace[out] = atanh(workspace[a1])
            end
        end
        return workspace[tape.root_idx]
    end
end

"""
    _execute_reverse!(tape::CompiledHC4, workspace::Vector{_BI}) -> Bool

Run the reverse contraction pass in-place on `workspace`.
Returns `false` immediately if any interval becomes empty (infeasible box).
"""
function _execute_reverse!(tape::CompiledHC4, workspace::Vector{_BI})
    @inbounds begin
        root_confine = intersect_interval(workspace[tape.root_idx], tape.confine)
        isempty_interval(root_confine) && return false
        workspace[tape.root_idx] = root_confine

        nary = tape.nary_args
        insts = tape.instructions

        for idx in length(insts):-1:1
            inst = insts[idx]
            op = inst.op
            confine = workspace[inst.out_idx]
            isempty_interval(confine) && return false
            a1 = inst.arg1
            a2 = inst.arg2

            if op == OP_ADD
                for i in a1:a2
                    rem_sum = _bi(0.0, 0.0)
                    for j in a1:a2
                        i == j && continue
                        rem_sum = rem_sum + workspace[nary[j]]
                    end
                    target = nary[i]
                    new_iv = intersect_interval(confine - rem_sum, workspace[target])
                    isempty_interval(new_iv) && return false
                    workspace[target] = new_iv
                end
            elseif op == OP_MUL
                for i in a1:a2
                    rem_prod = _bi(1.0, 1.0)
                    for j in a1:a2
                        i == j && continue
                        rem_prod = rem_prod * workspace[nary[j]]
                    end
                    target = nary[i]
                    new_iv = _rev_mul(confine, rem_prod, workspace[target])
                    isempty_interval(new_iv) && return false
                    workspace[target] = new_iv
                end
            elseif op == OP_SUB
                iv1 = intersect_interval(confine + workspace[a2], workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1

                iv2 = intersect_interval(workspace[a1] - confine, workspace[a2])
                isempty_interval(iv2) && return false
                workspace[a2] = iv2
            elseif op == OP_NEG
                iv1 = intersect_interval(-confine, workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_DIV
                iv1 = intersect_interval(confine * workspace[a2], workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1

                iv2 = _rev_mul(workspace[a1], confine, workspace[a2])
                isempty_interval(iv2) && return false
                workspace[a2] = iv2
            elseif op == OP_POW_INT
                iv1 = _rev_pow_int(confine, a2, workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_POW
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty_interval(c_pos) && return false
                iv1 = intersect_interval(exp(log(c_pos) / workspace[a2]), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1

                a1_pos = intersect_interval(workspace[a1], _bi(0.0, Inf))
                isempty_interval(a1_pos) && return false
                iv2 = intersect_interval(log(c_pos) / log(a1_pos), workspace[a2])
                isempty_interval(iv2) && return false
                workspace[a2] = iv2
            elseif op == OP_ABS
                sup(confine) < 0.0 && return false
                iv1 = intersect_interval(_bi(-sup(confine), sup(confine)), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_SIGN
                inf_C, sup_C = inf(confine), sup(confine)
                (sup_C < -1.0 || inf_C > 1.0) && return false
                new_inf = inf_C <= -1.0 ? -Inf : (inf_C <= 0.0 ? 0.0 : nextfloat(0.0))
                new_sup = sup_C >= 1.0 ? Inf : (sup_C >= 0.0 ? 0.0 : prevfloat(0.0))
                new_inf > new_sup && return false
                iv1 = intersect_interval(_bi(new_inf, new_sup), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_EXP
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty_interval(c_pos) && return false
                iv1 = intersect_interval(log(c_pos), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_EXP2
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty_interval(c_pos) && return false
                iv1 = intersect_interval(log2(c_pos), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_EXP10
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty_interval(c_pos) && return false
                iv1 = intersect_interval(log10(c_pos), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_LOG
                iv1 = intersect_interval(exp(confine), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_LOG2
                iv1 = intersect_interval(exp2(confine), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_LOG10
                iv1 = intersect_interval(exp10(confine), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_SIN
                C_int = intersect_interval(confine, _bi(-1.0, 1.0))
                isempty_interval(C_int) && return false
                asin_C = asin(C_int)
                pi_bi = _bi(pi)
                iv1 = _widen_periodic(workspace[a1], 2.0 * Float64(pi), asin_C, pi_bi - asin_C)
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_COS
                C_int = intersect_interval(confine, _bi(-1.0, 1.0))
                isempty_interval(C_int) && return false
                acos_C = acos(C_int)
                iv1 = _widen_periodic(workspace[a1], 2.0 * Float64(pi), acos_C, -acos_C)
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_TAN
                atan_C = atan(confine)
                iv1 = _widen_periodic(workspace[a1], Float64(pi), atan_C)
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ASIN
                C_int = intersect_interval(confine, _bi(-pi / 2, pi / 2))
                isempty_interval(C_int) && return false
                iv1 = intersect_interval(sin(C_int), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ACOS
                C_int = intersect_interval(confine, _bi(0.0, pi))
                isempty_interval(C_int) && return false
                iv1 = intersect_interval(cos(C_int), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ATAN
                C_int = intersect_interval(confine, _bi(-pi / 2, pi / 2))
                isempty_interval(C_int) && return false
                iv1 = intersect_interval(tan(C_int), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_SINH
                iv1 = intersect_interval(asinh(confine), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_COSH
                C_int = intersect_interval(confine, _bi(1.0, Inf))
                isempty_interval(C_int) && return false
                acosh_conf = acosh(C_int)
                iv1 = intersect_interval(hull(acosh_conf, -acosh_conf), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_TANH
                C_int = intersect_interval(confine, _bi(-1.0, 1.0))
                isempty_interval(C_int) && return false
                iv1 = intersect_interval(atanh(C_int), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ASINH
                iv1 = intersect_interval(sinh(confine), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ACOSH
                C_int = intersect_interval(confine, _bi(0.0, Inf))
                isempty_interval(C_int) && return false
                iv1 = intersect_interval(cosh(C_int), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ATANH
                iv1 = intersect_interval(tanh(confine), workspace[a1])
                isempty_interval(iv1) && return false
                workspace[a1] = iv1
            end
        end
        return true
    end
end

@inline function _eval_relation_status(rel::Symbol, value::_BI)
    isempty_interval(value) && return :outside
    lower, upper = inf(value), sup(value)
    if rel === _LT
        return upper < 0.0 ? :inside : lower >= 0.0 ? :outside : :unknown
    elseif rel === _LE
        return upper <= 0.0 ? :inside : lower > 0.0 ? :outside : :unknown
    elseif rel === _GT
        return lower > 0.0 ? :inside : upper <= 0.0 ? :outside : :unknown
    elseif rel === _GE
        return lower >= 0.0 ? :inside : upper < 0.0 ? :outside : :unknown
    elseif rel === _EQ
        return (lower == 0.0 && upper == 0.0) ? :inside :
               (upper < 0.0 || lower > 0.0) ? :outside : :unknown
    end
    # _NE
    return (upper < 0.0 || lower > 0.0) ? :inside :
           (lower == 0.0 && upper == 0.0) ? :outside : :unknown
end

"""
    _inside_and_defined(tape, box, dws) -> Bool
 
Decorated re-evaluation of one constraint on `box`. True only if the relation
holds on the whole enclosure AND the expression is defined at every point of
the box. Bare intervals silently clip `log(x)`, `1/x`, `sqrt(x)` ... to their
natural domain, so a bare `:inside` only speaks for the points where the
expression happens to be defined; two constraints can then be "inside" on
disjoint parts of the box, and the box would wrongly count as satisfying both.
Only called when the bare pass already says `:inside`, so the extra cost is
paid on the rare candidate boxes, not on every revise.
"""
function _inside_and_defined(tape::CompiledHC4, box::IntervalBox{N,T}, dws::Vector{_DI}) where {N,T}
    @inbounds for i in 1:N
        dws[i] = interval(_bi(box[i]))
    end
    v = _execute_forward!(tape, dws)
    _is_defined(v) || return false
    return _eval_relation_status(tape.rel, bareinterval(v)) === :inside
end

"""
    HC4Revise(box, tape, workspace, dws) -> (Symbol, IntervalBox)
 
Returns `(:inside | :outside | :unknown, box)`. `:inside` is only returned when
the decorated check confirms the constraint is defined and satisfied on the
entire box. If the bare enclosure says inside but definedness cannot be
confirmed, the call falls through to the reverse pass and returns `:unknown`.
 
If the natural enclosure is inconclusive and `tape.mvf` is set, the root is first
intersected with a mean-value enclosure (see `_mvf_refine!`), which can decide the
constraint or tighten what the reverse pass starts from.
"""
function HC4Revise(box::IntervalBox{N,T}, tape::CompiledHC4,
    workspace::Vector{_BI}, dws::Vector{_DI}) where {N,T}
    @inbounds for i in 1:N
        workspace[i] = _bi(box[i])
    end

    F_nat = _execute_forward!(tape, workspace)
    status = _eval_relation_status(tape.rel, F_nat)
    status === :outside && return :outside, box
    if status === :inside && _inside_and_defined(tape, box, dws)
        return :inside, box
    end

    # Mean-value refinement of the root. Only when the natural enclosure could not
    # decide, and only for tapes that passed the static dependency/differentiability
    # gates. `workspace` is untouched by `_mvf_refine!` except for the root below.
    if status === :unknown && tape.mvf !== nothing
        F = _mvf_refine!(tape, tape.mvf::MVFPlan, workspace, dws, F_nat)
        if F !== nothing
            mstatus = _eval_relation_status(tape.rel, F)
            mstatus === :outside && return :outside, box
            mstatus === :inside && return :inside, box   # f is dac on the box (checked in _mvf_refine!)
            workspace[tape.root_idx] = F
        end
    end

    _execute_reverse!(tape, workspace) || return :outside, box
    contracted = IntervalBox(ntuple(i -> T === _BI ? workspace[i] : interval(workspace[i]), Val(N)))
    return :unknown, contracted
end

# Standalone convenience API (compiles on the fly)
function HC4Revise(box::IntervalBox, variables::Union{AbstractVector,Tuple}, relation::SymRelation)
    tape = compile_hc4(relation, variables)
    workspace = Vector{_BI}(undef, tape.tape_len)
    dws = Vector{_DI}(undef, tape.tape_len)
    status, contracted = HC4Revise(box, tape, workspace, dws)
    if status === :outside
        return IntervalBox(ntuple(_ -> emptyinterval(eltype(box)), length(variables)))
    end
    return contracted
end

"""
    _significant_reduction(old::_BI, new::_BI, ratio) -> Bool

IBEX's stopping test: a contraction only counts if it removes more than
`ratio * diam(old)` from the domain.  Unbounded domains have no usable diameter,
so any tightening of a bound counts as significant.
"""
@inline function _significant_reduction(old::_BI, new::_BI, ratio::Float64)
    isempty_interval(new) && return true
    isempty_interval(old) && return false
    lo_o, hi_o = inf(old), sup(old)
    lo_n, hi_n = inf(new), sup(new)
    if !isfinite(lo_o) || !isfinite(hi_o)
        return lo_n > lo_o || hi_n < hi_o
    end
    w_old = hi_o - lo_o
    w_old <= 0.0 && return false
    return (w_old - (hi_n - lo_n)) > ratio * w_old
end

# ---------------------------------------------------------------------------
# HC4Revise iterated to an (approximate) fixpoint
# ---------------------------------------------------------------------------

# IBEX's default fixpoint ratio for HC4 / propagation (CtcHC4, CtcPropag).
# (CtcFixpoint's own default is 0.1, but 0.01 is what HC4 uses.)
const HC4_DEFAULT_RATIO = 0.01

"""
    _hc4_propagate(box, tapes, active_mask, ws, dws; ratio, max_pass)
        -> (:unsat | :unknown, box, mask)
 
Sweeps the active constraints until a full sweep gives no significant reduction.
Bits of constraints proven inside-and-defined are cleared; such a constraint
stays inside-and-defined on every sub-box.
"""
function _hc4_propagate(box::IntervalBox{N,T}, tapes::Vector{CompiledHC4}, active_mask::UInt64,
    ws::Vector{_BI}, dws::Vector{_DI};
    ratio::Float64=HC4_DEFAULT_RATIO, max_pass::Int=100) where {N,T}

    _box_empty(box) && return :unsat, box, active_mask
    current = box
    mask = active_mask
    for _ in 1:max_pass
        significant = false
        for i in eachindex(tapes)
            bit = UInt64(1) << (i - 1)
            (mask & bit) == 0 && continue

            status, next = HC4Revise(current, tapes[i], ws, dws)
            status === :outside && return :unsat, next, mask
            if status === :inside
                mask &= ~bit
                continue
            end
            _box_empty(next) && return :unsat, next, mask

            if !significant
                for k in 1:N
                    if _significant_reduction(_bi(current[k]), _bi(next[k]), ratio)
                        significant = true
                        break
                    end
                end
            end
            current = next
        end
        (significant && mask != 0) || break
    end

    if mask != 0 && _is_point(current)
        for i in eachindex(tapes)
            bit = UInt64(1) << (i - 1)
            (mask & bit) == 0 && continue
            status, next = HC4Revise(current, tapes[i], ws, dws)
            status === :outside && return :unsat, next, mask
            if status === :inside
                mask &= ~bit
                continue
            end
            _box_empty(next) && return :unsat, next, mask
            current = next
        end
    end
    return :unknown, current, mask
end

"""
    _Contracted
 
Outcome of contracting a system. `box` is stored as a plain vector of bare
intervals (cache friendly); `_make_box` turns it back into an `IntervalBox`.
  status  :unsat    no point satisfies the compiled constraints
          :sat      every constraint inside-and-defined on `box`, nothing dropped
          :unknown  otherwise
  mask    constraints not yet proven inside (needed to continue paving)
"""
struct _Contracted
    status::Symbol
    box::Vector{_BI}
    mask::UInt64
    prep::_Prepared
end

_infeasible(n::Int) = _Contracted(:unsat, _BI[_empty_bi() for _ in 1:n], UInt64(0), _NO_TAPES)

# ---------------------------------------------------------------------------
# Certificates that prove a real zero exists in a candidate box
# ---------------------------------------------------------------------------
"""
    _ZeroCertificate(residual, variables, tape)

Callable paving certificate for the probe `residual == 0`. It accepts a box only
when all non-probe constraints have already been proved inside-and-defined and
one of the existence tests (IVT or one-coordinate interval Newton) succeeds.
The private decorated workspace is sized for derivative tapes too, since those
can be longer than the original constraint tapes.
"""
struct _ZeroCertificate
    tape::CompiledHC4
    dtapes::Vector{Union{Nothing,CompiledHC4}}
    scratch::Vector{_DI}
end

function _compile_zero_derivative(residual, variable, variables)
    try
        derivative = Symbolics.derivative(residual, variable; simplify=true)
        return _compile_hc4_residual(derivative, _EQ, variables)
    catch err
        # Unsupported or nondifferentiable symbolic operations merely disable
        # Newton for this coordinate. They must not disable the IVT certificate.
        (err isa InterruptException || err isa OutOfMemoryError) && rethrow()
        return nothing
    end
end

function _ZeroCertificate(residual, variables, tape::CompiledHC4)
    dtapes = Union{Nothing,CompiledHC4}[
        _compile_zero_derivative(residual, variable, variables) for variable in variables
    ]
    max_len = maximum((t.tape_len for t in dtapes if t !== nothing); init=tape.tape_len)
    max_len = max(max_len, tape.tape_len)
    return _ZeroCertificate(tape, dtapes, Vector{_DI}(undef, max_len))
end

# Evaluate a tape over bare input intervals using decorated interval arithmetic.
# `nothing` is a defensive fallback for a mismatched tape/workspace.
function _zero_eval(tape::CompiledHC4, ivs::Vector{_BI}, scratch::Vector{_DI})
    length(ivs) == tape.num_vars || return nothing
    length(scratch) >= tape.tape_len || return nothing
    @inbounds for i in 1:tape.num_vars
        scratch[i] = interval(ivs[i])
    end
    return _execute_forward!(tape, scratch)
end

# Return -1 / +1 only when the point value is rigorously negative / positive.
function _zero_point_sign(cert::_ZeroCertificate, point::Vector{_BI})::Int
    value = _zero_eval(cert.tape, point, cert.scratch)
    value === nothing && return 0
    decoration(value) >= dac || return 0
    enclosure = bareinterval(value)
    return sup(enclosure) < 0.0 ? -1 : inf(enclosure) > 0.0 ? 1 : 0
end

# Try the midpoint and the 2N points obtained by moving one coordinate to an
# endpoint. Opposite certified signs imply a zero by continuity and convexity.
function _zero_ivt(cert::_ZeroCertificate, boxivs::Vector{_BI})::Bool
    point = _BI[_bi(mid(iv)) for iv in boxivs]
    seen_neg = false
    seen_pos = false

    s = _zero_point_sign(cert, point)
    seen_neg |= s < 0
    seen_pos |= s > 0
    seen_neg && seen_pos && return true

    for k in eachindex(boxivs)
        point[k] = _bi(inf(boxivs[k]))
        s = _zero_point_sign(cert, point)
        seen_neg |= s < 0
        seen_pos |= s > 0
        seen_neg && seen_pos && return true

        point[k] = _bi(sup(boxivs[k]))
        s = _zero_point_sign(cert, point)
        seen_neg |= s < 0
        seen_pos |= s > 0
        seen_neg && seen_pos && return true

        point[k] = _bi(mid(boxivs[k]))
    end
    return false
end

# One-dimensional interval Newton along a coordinate, with all other
# coordinates fixed at their midpoints. Coordinates are tried widest first.
function _zero_newton(cert::_ZeroCertificate, boxivs::Vector{_BI})::Bool
    isempty(boxivs) && return false
    order = sortperm([diam(iv) for iv in boxivs]; rev=true)
    mids = _BI[_bi(mid(iv)) for iv in boxivs]

    for k in order
        dtape = cert.dtapes[k]
        dtape === nothing && continue
        X = boxivs[k]
        inf(X) < sup(X) || continue

        fc = _zero_eval(cert.tape, mids, cert.scratch)
        fc === nothing && continue
        decoration(fc) >= dac || continue

        line = copy(mids)
        line[k] = X
        D = _zero_eval(dtape, line, cert.scratch)
        D === nothing && continue
        decoration(D) >= dac || continue
        Db = bareinterval(D)
        # The derivative enclosure must exclude zero.
        (sup(Db) < 0.0 || inf(Db) > 0.0) || continue

        c = interval(_bi(mid(X)))
        N = c - fc / D
        decoration(N) >= dac || continue
        Nb = bareinterval(N)
        isempty_interval(Nb) && continue
        # Strict inclusion in the interior is the interval-Newton existence test.
        if inf(Nb) > inf(X) && sup(Nb) < sup(X)
            return true
        end
    end
    return false
end

# Callable hook accepted by _pave_core. Bit zero is the equality probe; every
# other active constraint must already be inside-and-defined on the whole box.
function (cert::_ZeroCertificate)(box, mask::UInt64, _ws::Vector{_BI}, _dws::Vector{_DI})::Bool
    mask == 0 && return true
    (mask & ~UInt64(1)) == 0 || return false
    boxivs = _BI[_bi(box[i]) for i in 1:length(box)]

    # A decorated enclosure with decoration >= dac certifies definedness and
    # continuity of the residual on the entire box (def alone is insufficient).
    whole = _zero_eval(cert.tape, boxivs, cert.scratch)
    whole === nothing && return false
    decoration(whole) >= dac || return false

    _zero_ivt(cert, boxivs) && return true
    return _zero_newton(cert, boxivs)
end

"""
    _contract(box, constraints, variables; ratio) -> _Contracted
 
The single place that compiles a system and contracts it with HC4.
"""
function _contract(box::IntervalBox, constraints, variables; ratio::Float64=HC4_DEFAULT_RATIO)
    prep = _prepare(constraints, variables)
    ws, dws = _workspaces(prep)
    status, contracted, mask = _hc4_propagate(box, prep.tapes, _full_mask(length(prep.tapes)),
        ws, dws; ratio=ratio)
    n = length(box)
    status === :unsat && return _Contracted(:unsat, _BI[_empty_bi() for _ in 1:n], mask, prep)
    out = _BI[_bi(contracted[k]) for k in 1:n]
    return _Contracted((mask == 0 && !prep.dropped) ? :sat : :unknown, out, mask, prep)
end

const _DEFAULT_PAVE_CERTIFY = (box, mask, ws, dws) -> mask == 0
"""
    _pave_core(root, prep, ws, dws, mask0, epsilon, ratio) -> :sat | :unsat | :unknown
 
`root` must already be contracted (HC4 fixpoint under `mask0`) and BOUNDED.
Only children are propagated here. Stops with `:sat` the moment one box has every
constraint inside-and-defined; `:unsat` only if every box was pruned; a surviving
box of width < epsilon makes the answer `:unknown`.
"""
function _pave_core(root::IntervalBox{N,T}, prep::_Prepared, ws::Vector{_BI}, dws::Vector{_DI},
    mask0::UInt64, epsilon::Float64, ratio::Float64;
    certify=_DEFAULT_PAVE_CERTIFY, max_boxes::Int=5000) where {N,T}

    max_boxes >= 1 || throw(ArgumentError("max_boxes must be positive"))
    working = Tuple{IntervalBox{N,T},UInt64}[(root, mask0)]
    unresolved = false
    examined = 0
    while !isempty(working)
        current, mask = pop!(working)
        examined += 1
        examined > max_boxes && return :unknown

        if certify(current, mask, ws, dws)
            # With dropped constraints a surviving candidate cannot prove sat.
            return prep.dropped ? :unknown : :sat
        end
        if diam(current) < epsilon
            unresolved = true
            continue
        end

        b1, b2 = bisect(current)
        for b in (b1, b2)
            status, child, child_mask = _hc4_propagate(b, prep.tapes, mask, ws, dws; ratio=ratio)
            status === :unsat && continue

            if child_mask != 0 && _is_point(child)
                unresolved = true
                continue
            end
            push!(working, (child, child_mask))
        end
    end
    return unresolved ? :unknown : :unsat
end

"""
    _pave_contracted(c::_Contracted; epsilon, ratio) -> :sat | :unsat | :unknown
 
Decide from an already contracted system: take what contraction decided, return
`:unknown` if the box is still unbounded (it cannot be bisected), otherwise
branch and prune from `c.box` with the mask contraction left behind.
"""
function _pave_contracted(c::_Contracted; epsilon::Float64=tolerance[],
    ratio::Float64=HC4_DEFAULT_RATIO, certify=_DEFAULT_PAVE_CERTIFY,
    max_boxes::Int=5000)::Symbol
    c.status === :unsat && return :unsat
    c.status === :sat && return :sat
    c.mask == 0 && return :unknown              # all inside, but constraints were dropped
    box = _make_box(c.box)
    _bounded(box) || return :unknown
    _is_point(box) && return :unknown
    ws, dws = _workspaces(c.prep)
    return _pave_core(box, c.prep, ws, dws, c.mask, epsilon, ratio;
        certify=certify, max_boxes=max_boxes)
end
