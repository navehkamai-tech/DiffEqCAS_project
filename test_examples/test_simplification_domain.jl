using Test
using Symbolics
using DiffEqCAS

@variables x a n

positive_a = Symbolics.setmetadata(a, DiffEqCAS.VarSign, DiffEqCAS.positive)

@test DiffEqCAS._relation_sign(2x > 0, x) === DiffEqCAS.positive
@test DiffEqCAS._relation_sign(x - positive_a > 0, x) === DiffEqCAS.positive
@test DiffEqCAS._relation_sign(x > positive_a + 1, x) === DiffEqCAS.positive
@test DiffEqCAS._relation_sign(-2x < 0, x) === DiffEqCAS.positive

@test DiffEqCAS._zero_excluded_by_relation(x^2 > 0, x)
@test DiffEqCAS._zero_excluded_by_relation(x^3 > 0, x)
@test DiffEqCAS._zero_excluded_by_relation(x^n > 0, x) == false
@test DiffEqCAS._constraints_exclude_zero([x^2 > 0], x)
@test DiffEqCAS._constraints_exclude_zero([x - positive_a > 0], x)

@test DiffEqCAS._relation_sign(x - a > 0, x) === DiffEqCAS.either
@test !DiffEqCAS._constraints_exclude_zero([x - a > 0], x)

positive_n = Symbolics.setmetadata(n, DiffEqCAS.VarSign, DiffEqCAS.positive)
@test DiffEqCAS._relation_sign(positive_n * x > 0, x) === DiffEqCAS.positive
@test DiffEqCAS._relation_sign(positive_n * x > positive_a, x) === DiffEqCAS.positive
@test DiffEqCAS._relation_sign(positive_n * x < 0, x) === DiffEqCAS.negative
@test DiffEqCAS._relation_sign(positive_n * x < -positive_a, x) === DiffEqCAS.negative
@test DiffEqCAS._constraints_exclude_zero([x^positive_n > 0], x)

system = DiffEqSystem([], [], [x => [2x > 0]], [x], [])
@test DiffEqCAS.factor_divisibility(x, system).status === DiffEqCAS.divisible

positive_domain = DiffEqSystem([], [], [x => [x > 0]], [x], [])
@test DiffEqCAS.factor_divisibility(x + 1, positive_domain).status === DiffEqCAS.divisible
@test DiffEqCAS.factor_divisibility(x - 1, positive_domain).status === DiffEqCAS.haszero

negative_domain = DiffEqSystem([], [], [x => [x < 0]], [x], [])
@test DiffEqCAS.factor_divisibility(2x + 1, negative_domain).status === DiffEqCAS.haszero
@test DiffEqCAS.factor_divisibility(2x - 1, negative_domain).status === DiffEqCAS.divisible
