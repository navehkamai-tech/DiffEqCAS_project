using Symbolics
using BenchmarkTools

import Symbolics: unwrap, wrap
import SymbolicUtils
import ModelingToolkit

# Define _is_target original version
function _is_target_orig(e, dvs::Vector{Symbolics.Num}, dv_ops)
    if !SymbolicUtils.istree(e)
        return any(isequal(e, unwrap(d)) for d in dvs)
    end

    op = SymbolicUtils.operation(e)

    if any(isequal(op, d_op) for d_op in dv_ops)
        return true
    end

    if op isa Differential
        args = SymbolicUtils.arguments(e)
        return _is_target_orig(args[1], dvs, dv_ops)
    end

    return false
end

function _find_targets_orig!(e, dvs::Vector{Symbolics.Num}, dv_ops, targets::Set)
    if _is_target_orig(e, dvs, dv_ops)
        push!(targets, e)
        return
    end

    if SymbolicUtils.istree(e)
        for arg in SymbolicUtils.arguments(e)
            _find_targets_orig!(arg, dvs, dv_ops, targets)
        end
    end
end

function _diff_depth(e)
    if !SymbolicUtils.istree(e)
        return 0
    end

    if SymbolicUtils.operation(e) isa Differential
        return 1 + _diff_depth(SymbolicUtils.arguments(e)[1])
    end

    return 0
end

function simplify_and_group_orig(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))

    dv_ops = [SymbolicUtils.operation(unwrap(d)) for d in dvs]
    targets = Set()

    _find_targets_orig!(expr, dvs, dv_ops, targets)

    sorted_targets = sort(collect(targets), by=_diff_depth, rev=true)

    grouped_expr = 0
    remainder = expr

    for target in sorted_targets
        coeff = simplify(expand_derivatives(Differential(target)(remainder)))

        if !isequal(coeff, 0)
            grouped_expr += coeff * wrap(target)
            remainder = simplify(remainder - coeff * target)
        end
    end

    grouped_expr += simplify(remainder)

    return grouped_expr ~ 0
end

# Define optimized version
function _is_target_opt(e, unwrapped_dvs::Set, dv_ops)
    if !SymbolicUtils.istree(e)
        return e in unwrapped_dvs
    end

    op = SymbolicUtils.operation(e)

    if any(isequal(op, d_op) for d_op in dv_ops)
        return true
    end

    if op isa Differential
        args = SymbolicUtils.arguments(e)
        return _is_target_opt(args[1], unwrapped_dvs, dv_ops)
    end

    return false
end

function _find_targets_opt!(e, unwrapped_dvs::Set, dv_ops, targets::Set)
    if _is_target_opt(e, unwrapped_dvs, dv_ops)
        push!(targets, e)
        return
    end

    if SymbolicUtils.istree(e)
        for arg in SymbolicUtils.arguments(e)
            _find_targets_opt!(arg, unwrapped_dvs, dv_ops, targets)
        end
    end
end

function simplify_and_group_opt(eq::Symbolics.Equation, dvs::Vector{Symbolics.Num})
    expr = expand_derivatives(unwrap(eq.lhs - eq.rhs))

    unwrapped_dvs = Set([unwrap(d) for d in dvs])
    dv_ops = [SymbolicUtils.operation(unwrap(d)) for d in dvs]
    targets = Set()

    _find_targets_opt!(expr, unwrapped_dvs, dv_ops, targets)

    sorted_targets = sort(collect(targets), by=_diff_depth, rev=true)

    grouped_expr = 0
    remainder = expr

    for target in sorted_targets
        coeff = simplify(expand_derivatives(Differential(target)(remainder)))

        if !isequal(coeff, 0)
            grouped_expr += coeff * wrap(target)
            remainder = simplify(remainder - coeff * target)
        end
    end

    grouped_expr += simplify(remainder)

    return grouped_expr ~ 0
end

@variables t x
@variables u1(..) u2(..) u3(..) u4(..) u5(..) u6(..) u7(..) u8(..) u9(..) u10(..)
@variables v1(..) v2(..) v3(..) v4(..) v5(..) v6(..) v7(..) v8(..) v9(..) v10(..)

dvs = [u1(t, x), u2(t, x), u3(t, x), u4(t, x), u5(t, x), u6(t, x), u7(t, x), u8(t, x), u9(t, x), u10(t, x),
       v1(t, x), v2(t, x), v3(t, x), v4(t, x), v5(t, x), v6(t, x), v7(t, x), v8(t, x), v9(t, x), v10(t, x)]

global expr = (t + x)^2 + sin(t) + t^2 + x^3
for i in 1:6
    global expr = (expr + t^2 + x^3)^2 + sin(expr + t)
end

eq = expr ~ 0

println("Benchmarking simplify_and_group_orig (worst case leaf heavy tree):")
@btime simplify_and_group_orig($eq, $dvs)

println("Benchmarking simplify_and_group_opt (worst case leaf heavy tree):")
@btime simplify_and_group_opt($eq, $dvs)
