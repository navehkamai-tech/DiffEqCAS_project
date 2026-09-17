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
@variables u(..) v(..)

dvs = [u(t, x), v(t, x)]

global expr = (u(t, x) + v(t, x))^2 + sin(u(t, x))
for i in 1:6
    global expr = (expr + u(t, x))^2 + sin(expr)
end
eq = expr ~ 0

println("Benchmarking simplify_and_group_orig:")
@btime simplify_and_group_orig($eq, $dvs)

println("Benchmarking simplify_and_group_opt:")
@btime simplify_and_group_opt($eq, $dvs)
