
function display_expr(expr)
    # Unwrap to access the raw SU tree
    expr_unwrapped = Symbolics.unwrap(expr)

    # 1. Base Case: If it's just a variable (x) or a number (5), leave it alone
    if !SU.iscall(expr_unwrapped)
        return expr
    end

    op = SU.operation(expr_unwrapped)
    args = SU.arguments(expr_unwrapped)

    # 2. The Magic: Intercepting the Differentials
    if op isa Differential
        vars = []
        curr = expr_unwrapped

        # Dig all the way down the nested rabbit hole and collect the variables
        while SU.iscall(curr) && SU.operation(curr) isa Differential
            push!(vars, SU.operation(curr).x)
            curr = SU.arguments(curr)[1]
        end

        # Join the variables into a single string (e.g., "x", "y" becomes "xy")
        var_str = join(string.(vars), "")

        # Create a temporary, fake function operator just for printing
        # This creates a callable symbol like D_xy
        display_op = SU.Sym{SU.FnType{Tuple,Real}}(Symbol("D_{$var_str}"))

        # Process whatever is inside the derivative, then wrap it in our fake function
        return wrap(display_op(Symbolics.unwrap(display_pde(curr))))
    end

    # 3. For Everything Else: (+, *, ^), rebuild the tree normally
    processed_args = map(a -> Symbolics.unwrap(display_pde(a)), args)
    return wrap(SU.similarterm(expr_unwrapped, op, processed_args))
end

function display_pde(eq::Symbolics.Equation)
    return display_expr(eq.lhs) ~ display_expr(eq.rhs)
end

display_pde(expr) = display_expr(expr)
