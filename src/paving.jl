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
    rel_op::Function
    tape_len::Int
end

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

"""
    compile_hc4(relation::SymRelation, variables) -> CompiledHC4

Compile a symbolic relation into a flat `CompiledHC4` tape once before paving.
"""
function compile_hc4(relation::SymRelation, variables)
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
                push!(constants, _bi(val))
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

    root_expr = Symbolics.unwrap(relation.residual)
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
    confine = _give_confine(relation.relation)
    tape_len = num_vars + num_consts + length(call_nodes)

    return CompiledHC4(num_vars, constants, instructions, nary_args, root_idx, confine, rel_op, tape_len)
end

# `compile_hc4` rejects operations the tape does not know; such constraints are
# dropped. Dropping is sound for contraction and for `No`, never for `Yes`.
function _compilable(rel::SymRelation)::Bool
    key = (:compilable, Symbolics.unwrap(rel.residual), rel.relation)
    hit = get(cache, key, nothing)
    hit === nothing || return hit
    ok = true
    try
        compile_hc4(rel, _vars_of(rel.residual))
    catch e
        e isa ArgumentError || rethrow()
        ok = false
    end
    cache[key] = ok
    return ok
end
# ---------------------------------------------------------------------------
# Elemental Reverse Contractors & Helpers
# ---------------------------------------------------------------------------

function _widen_periodic(X_orig::_BI, period::Float64, branches::_BI...)
    isempty(X_orig) && return _empty_bi()
    result = _empty_bi()
    inf_X, sup_X = inf(X_orig), sup(X_orig)

    for branch in branches
        isempty(branch) && continue
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
    isempty(c) && return _empty_bi()
    isempty(b) && return _empty_bi()

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
    isempty(c) && return _empty_bi()
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

@inline function _forward_pow_int(x::_BI, n::Int)
    return x ^ n
end

# ---------------------------------------------------------------------------
# Fast Tape Forward & Reverse Execution
# ---------------------------------------------------------------------------

function _execute_forward!(tape::CompiledHC4, workspace::Vector{_BI})
    @inbounds begin
        for i in 1:length(tape.constants)
            workspace[tape.num_vars+i] = tape.constants[i]
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
        isempty(root_confine) && return false
        workspace[tape.root_idx] = root_confine

        nary = tape.nary_args
        insts = tape.instructions

        for idx in length(insts):-1:1
            inst = insts[idx]
            op = inst.op
            confine = workspace[inst.out_idx]
            isempty(confine) && return false
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
                    isempty(new_iv) && return false
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
                    isempty(new_iv) && return false
                    workspace[target] = new_iv
                end
            elseif op == OP_SUB
                iv1 = intersect_interval(confine + workspace[a2], workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1

                iv2 = intersect_interval(workspace[a1] - confine, workspace[a2])
                isempty(iv2) && return false
                workspace[a2] = iv2
            elseif op == OP_NEG
                iv1 = intersect_interval(-confine, workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_DIV
                iv1 = intersect_interval(confine * workspace[a2], workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1

                iv2 = _rev_mul(workspace[a1], confine, workspace[a2])
                isempty(iv2) && return false
                workspace[a2] = iv2
            elseif op == OP_POW_INT
                iv1 = _rev_pow_int(confine, a2, workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_POW
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty(c_pos) && return false
                iv1 = intersect_interval(exp(log(c_pos) / workspace[a2]), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1

                a1_pos = intersect_interval(workspace[a1], _bi(0.0, Inf))
                isempty(a1_pos) && return false
                iv2 = intersect_interval(log(c_pos) / log(a1_pos), workspace[a2])
                isempty(iv2) && return false
                workspace[a2] = iv2
            elseif op == OP_ABS
                sup(confine) < 0.0 && return false
                iv1 = intersect_interval(_bi(-sup(confine), sup(confine)), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_SIGN
                inf_C, sup_C = inf(confine), sup(confine)
                (sup_C < -1.0 || inf_C > 1.0) && return false
                new_inf = inf_C <= -1.0 ? -Inf : (inf_C <= 0.0 ? 0.0 : nextfloat(0.0))
                new_sup = sup_C >= 1.0 ? Inf : (sup_C >= 0.0 ? 0.0 : prevfloat(0.0))
                new_inf > new_sup && return false
                iv1 = intersect_interval(_bi(new_inf, new_sup), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_EXP
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty(c_pos) && return false
                iv1 = intersect_interval(log(c_pos), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_EXP2
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty(c_pos) && return false
                iv1 = intersect_interval(log2(c_pos), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_EXP10
                c_pos = intersect_interval(confine, _bi(0.0, Inf))
                isempty(c_pos) && return false
                iv1 = intersect_interval(log10(c_pos), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_LOG
                iv1 = intersect_interval(exp(confine), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_LOG2
                iv1 = intersect_interval(exp2(confine), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_LOG10
                iv1 = intersect_interval(exp10(confine), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_SIN
                C_int = intersect_interval(confine, _bi(-1.0, 1.0))
                isempty(C_int) && return false
                asin_C = asin(C_int)
                pi_bi = _bi(pi)
                iv1 = _widen_periodic(workspace[a1], 2.0 * Float64(pi), asin_C, pi_bi - asin_C)
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_COS
                C_int = intersect_interval(confine, _bi(-1.0, 1.0))
                isempty(C_int) && return false
                acos_C = acos(C_int)
                iv1 = _widen_periodic(workspace[a1], 2.0 * Float64(pi), acos_C, -acos_C)
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_TAN
                atan_C = atan(confine)
                iv1 = _widen_periodic(workspace[a1], Float64(pi), atan_C)
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ASIN
                C_int = intersect_interval(confine, _bi(-pi / 2, pi / 2))
                isempty(C_int) && return false
                iv1 = intersect_interval(sin(C_int), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ACOS
                C_int = intersect_interval(confine, _bi(0.0, pi))
                isempty(C_int) && return false
                iv1 = intersect_interval(cos(C_int), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ATAN
                C_int = intersect_interval(confine, _bi(-pi / 2, pi / 2))
                isempty(C_int) && return false
                iv1 = intersect_interval(tan(C_int), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_SINH
                iv1 = intersect_interval(asinh(confine), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_COSH
                C_int = intersect_interval(confine, _bi(1.0, Inf))
                isempty(C_int) && return false
                acosh_conf = acosh(C_int)
                iv1 = intersect_interval(hull(acosh_conf, -acosh_conf), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_TANH
                C_int = intersect_interval(confine, _bi(-1.0, 1.0))
                isempty(C_int) && return false
                iv1 = intersect_interval(atanh(C_int), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ASINH
                iv1 = intersect_interval(sinh(confine), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ACOSH
                C_int = intersect_interval(confine, _bi(0.0, Inf))
                isempty(C_int) && return false
                iv1 = intersect_interval(cosh(C_int), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            elseif op == OP_ATANH
                iv1 = intersect_interval(tanh(confine), workspace[a1])
                isempty(iv1) && return false
                workspace[a1] = iv1
            end
        end
        return true
    end
end

@inline function _eval_relation_status(op, value::_BI)
    isempty(value) && return :outside
    lower, upper = inf(value), sup(value)
    if op === (<)
        return upper < 0.0 ? :inside : lower >= 0.0 ? :outside : :unknown
    elseif op === (<=)
        return upper <= 0.0 ? :inside : lower > 0.0 ? :outside : :unknown
    elseif op === (>)
        return lower > 0.0 ? :inside : upper <= 0.0 ? :outside : :unknown
    elseif op === (>=)
        return lower >= 0.0 ? :inside : upper < 0.0 ? :outside : :unknown
    elseif op === (==)
        return (lower == 0.0 && upper == 0.0) ? :inside :
               (upper < 0.0 || lower > 0.0) ? :outside : :unknown
    end
    return (upper < 0.0 || lower > 0.0) ? :inside :
           (lower == 0.0 && upper == 0.0) ? :outside : :unknown
end

"""
    HC4Revise(box::IntervalBox, tape::CompiledHC4, workspace::Vector{_BI}) -> (Symbol, IntervalBox)

Fast, allocation-free HC4Revise on a pre-compiled tape.
Returns `(status, contracted_box)` where `status` is `:inside`, `:outside`, or `:unknown`.
"""
function HC4Revise(box::IntervalBox{N,T}, tape::CompiledHC4, workspace::Vector{_BI}) where {N,T}
    @inbounds for i in 1:N
        workspace[i] = _bi(box[i])
    end

    forward_val = _execute_forward!(tape, workspace)
    status = _eval_relation_status(tape.rel_op, forward_val)

    # If the entire box is strictly inside or strictly outside, no contraction is needed
    if status === :inside || status === :outside
        return status, box
    end

    # Status is :unknown (boundary); run reverse pass to contract the box
    feasible = _execute_reverse!(tape, workspace)
    if !feasible
        return :outside, box
    end

    contracted = IntervalBox(ntuple(i -> T === _BI ? workspace[i] : Interval(workspace[i]), Val(N)))
    return :unknown, contracted
end

# Standalone convenience API (compiles tape on the fly if called outside _pave_constraints)
function HC4Revise(box::IntervalBox, variables::Union{AbstractVector,Tuple}, relation::SymRelation)
    tape = compile_hc4(relation, variables)
    workspace = Vector{_BI}(undef, tape.tape_len)
    status, contracted = HC4Revise(box, tape, workspace)
    if status === :outside
        return IntervalBox(ntuple(_ -> emptyinterval(eltype(box)), length(variables)))
    end
    return contracted
end

# helper for constraints_to_domain
function shrink_bounds!(bounds, constraint::Constraint)
    vars = constraint_variables(constraint)
    if !(length(vars) == 1)
        return bounds
    end
    var = vars[1]
    expr = simplify(Symbolics.unwrap(constraint.relation.residual))
    if !isequal(Symbolics.degree(expr, var), 1)
        return bounds
    end
    op = _get_relation(constraint.relation)
    coeff = Symbolics.coeff(expr, var)
    coeff_value = SU.unwrap_const(Symbolics.unwrap(coeff))
    coeff_value isa Real || return bounds
    num = SU.unwrap_const(Symbolics.unwrap(substitute(expr, var => 0) / coeff))
    num isa Real || return bounds
    if (((op === <) || (op === <=)) && (coeff_value > 0)) ||
        (((op === >) || (op === >=)) && (coeff_value < 0))
        bounds[var][2] = min(-num, bounds[var][2])
    elseif (((op === <) || (op === <=)) && (coeff_value < 0)) ||
        (((op === >) || (op === >=)) && (coeff_value > 0))
        bounds[var][1] = max(-num, bounds[var][1])
    end
    return bounds
end

"""
Custom implementation of IntervalBox branch-and-prune paving using compiled HC4Revise constraint propagation.
"""
function _pave_constraints(box::IntervalBox{N,T}, constraints, variables, epsilon) where {N,T}
    tapes = CompiledHC4[compile_hc4(c.relation, variables) for c in constraints]
    max_len = isempty(tapes) ? N : maximum(t.tape_len for t in tapes)
    workspace = Vector{_BI}(undef, max_len)

    # Track active constraints per box using a UInt64 bitmask (supports up to 64 constraints per factor;
    # once a constraint is :inside on a parent box, it is guaranteed :inside on all child sub-boxes!)
    num_c = length(tapes)
    all_active_mask = num_c <= 64 ? ((UInt64(1) << num_c) - UInt64(1)) : UInt64(0)
    use_mask = num_c <= 64
    use_mask || throw(ArgumentError("Too many constraints ($num_c) for bitmasking; maximum supported is 64."))

    working = Tuple{IntervalBox{N,T},UInt64}[(box, all_active_mask)]
    inner = IntervalBox{N,T}[]
    boundary = IntervalBox{N,T}[]

    while !isempty(working)
        current, active_mask = pop!(working)
        isempty(current) && continue

        is_outside = false
        next_mask = active_mask

        for i in 1:num_c
            if use_mask
                bit = UInt64(1) << (i - 1)
                (active_mask & bit) == 0 && continue
            end
            status, current = HC4Revise(current, tapes[i], workspace)
            if status === :outside || isempty(current)
                is_outside = true
                break
            elseif status === :inside && use_mask
                next_mask &= ~(UInt64(1) << (i - 1))
            end
        end

        is_outside && continue

        if use_mask ? (next_mask == 0) : false
            push!(inner, current)
        elseif num_c == 0
            push!(inner, current)
        elseif diam(current) < epsilon
            push!(boundary, current)
        else
            b1, b2 = bisect(current)
            push!(working, (b1, next_mask))
            push!(working, (b2, next_mask))
        end
    end

    return inner, boundary
end

# `coord` is ordered like `domain.variables`; each block sees only its slice.
function _in_pavings(coord, domain::SymDomain, pavings, include_boundary::Bool)
    length(coord) == length(domain.variables) ||
        throw(DimensionMismatch("coords must have the same dimension as domain"))
    offset = 0
    for (block, paving) in zip(domain.blocks, pavings)
        n = length(block.variables)
        sub = StaticArrays.SVector{n}(ntuple(i -> coord[offset+i], n))
        offset += n
        any(sub ∈ box for box in paving.interior) && continue
        include_boundary && any(sub ∈ box for box in paving.boundary) && continue
        return false
    end
    return true
end

#------------------------------------------------------------------------------
# Paving API for satisfiability
#------------------------------------------------------------------------------

"Run HC4Revise over all constraints to a fixed point. -> (feasible, intervals)"
function _contract(cons, vars, bounds::Vector{_BI}; maxpass::Int=6)
    usable = [c for c in cons if _compilable(c.relation)]
    isempty(usable) && return true, bounds
    tapes = CompiledHC4[compile_hc4(c.relation, vars) for c in usable]
    ws = Vector{_BI}(undef, maximum(t.tape_len for t in tapes))
    n = length(vars)
    cur = copy(bounds)
    for _ in 1:maxpass
        changed = false
        for tape in tapes
            status, nb = HC4Revise(IntervalBox(Tuple(cur)), tape, ws)
            status === :outside && return false, cur
            for i in 1:n
                new = _bi(nb[i])
                if !isequal(new, cur[i])
                    changed = true
                    cur[i] = new
                end
            end
        end
        changed || break
    end
    return true, cur
end

# Keep paving boxes finite: unbounded sides get a window of size ROI.
function _window(iv::_BI)::_BI
    isempty(iv) && return iv
    lo, hi = inf(iv), sup(iv)
    r = ROI[]
    lo2 = isfinite(lo) ? lo : min(-r, isfinite(hi) ? hi - r : -r)
    hi2 = isfinite(hi) ? hi : max(r, isfinite(lo) ? lo + r : r)
    return _bi(lo2, hi2)
end

# The one place that paves. -> (feasible, inner, boundary, dropped)
# `feasible=false` is a proof that nothing satisfies `cons` in the box (sound even
# when constraints were dropped); `dropped` forbids certifying anything.
function _pave_boxes(cons, vars, ivs::Vector{_BI})
    any(isempty, ivs) && return false, Any[], Any[], false
    usable = Constraint[c for c in cons if _compilable(c.relation)]
    dropped = length(usable) < length(cons)
    ok, ivs = _contract(usable, vars, ivs)
    ok || return false, Any[], Any[], dropped
    if length(usable) > 64
        usable = usable[1:64]
        dropped=true
    end
    inner, boundary = _pave_constraints(IntervalBox(Tuple(ivs)), usable, vars, tolerance[])
    return !(isempty(inner) && isempty(boundary)), inner, boundary, dropped
end
