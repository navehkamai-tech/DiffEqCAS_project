# Issues Log

- test_my_functions.jl fails with UndefKeywordError: keyword argument `name` not assigned when calling `PDESystem` at `test_my_functions.jl:21` (corresponding to PDESystem invocation). In `my_functions.jl`, instances of `PDESystem` instantiation might also be missing the `name` kwarg.

- `PDESystem` calls missing `name` argument at `my_functions.jl:228`, `my_functions.jl:385`, `my_functions.jl:480`. (Wait, let me double check ModelingToolkit's PDESystem constructor. It usually accepts name as a kwarg like `name=:sys`).
- The special rewriter initialization in `change_dvs` misses passing `params`: `dr = special_rewriter(params)` at line 454 (params is not defined until line 477).
- In `change_parameters`, `new_domains` is used at line 228 but is never defined.
- `extract_parameters` called with two arguments in `change_parameters` (line 213) but is defined with only one argument.
- `special_rewriter` is defined without arguments (line 38), but it is called with `new_params` in `change_parameters` (line 216), `change_ivs` (line 357), and `change_dvs` (line 454).
- `is_scalar` used as a constraint in `special_rewriter` rule (`~c::is_scalar`) but is not defined. (line 77)
- `transform_domains` expects `old_domains::Vector{Pair}` but `sys.domain` can be an empty array (`Vector{Any}`). This happens at line 383, which calls `transform_domains(sys.domain, iv_mapping, new_ivs)` (line 287).
- `_diff_dvth` is referenced in `simplify_and_group` (line 546) and `_diff_depth` (line 529), but it is not defined (likely a typo for `_diff_depth`).
