using Test
using Symbolics
using ModelingToolkit
using DiffEqCAS

@parameters x
@variables u(x)

system = DiffEqSystem(
    [x * u + x ~ 0],
    Symbolics.Equation[],
    [x => [x > 0]],
    [x],
    [u],
)

result = simplify_system(system)

@test result.status === :fixed_point
@test length(result.systems) == 1
@test string(result.systems[1].eqs[1].rhs) == "0"
@test string(simplify(result.systems[1].eqs[1].lhs - (1 + u))) == "0"
@test any(step -> step.stage === :certified_cancellation, result.trace)

dependent_factor = DiffEqSystem(
    [u * u ~ 0],
    Symbolics.Equation[],
    [x => [x > 0]],
    [x],
    [u],
)

dependent_result = simplify_system(dependent_factor)
@test string(dependent_result.systems[1].eqs[1].rhs) == "0"
@test string(simplify(
    dependent_result.systems[1].eqs[1].lhs - u^2)) == "0"

duplicate_union = DiffEqSystem()
@test push_branch!(duplicate_union, DiffEqBranch(
    [u ~ 0], Symbolics.Equation[], [x => [x > 0]], [x], [u])) 
@test !push_branch!(duplicate_union, DiffEqBranch(
    [u ~ 0], Symbolics.Equation[], [x => [x > 0]], [x], [u]))
@test length(duplicate_union.pending) == 1
