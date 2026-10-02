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

@test length(result.branches) == 1
@test string(result.branches[1].eqs[1].rhs) == "0"
@test string(simplify(result.branches[1].eqs[1].lhs - (1 + u))) == "0"
@test result.branches[1].history.steps isa Vector{DerivationStep}
@test length(result.branches[1].history.steps) == 1
@test only(result.branches[1].history.steps).options ==
    SimplificationOptions()

dependent_factor = DiffEqSystem(
    [u * u ~ 0],
    Symbolics.Equation[],
    [x => [x > 0]],
    [x],
    [u],
)

dependent_result = simplify_system(dependent_factor)
@test string(dependent_result.branches[1].eqs[1].rhs) == "0"
@test string(simplify(
    dependent_result.branches[1].eqs[1].lhs - u^2)) == "0"

duplicate_union = DiffEqSystem()
@test push_branch!(duplicate_union, DiffEqBranch(
    [u ~ 0], Symbolics.Equation[], [x => [x > 0]], [x], [u])) 
@test !push_branch!(duplicate_union, DiffEqBranch(
    [u ~ 0], Symbolics.Equation[], [x => [x > 0]], [x], [u]))
@test length(duplicate_union.pending) == 1
