using ModelingToolkit
using Symbolics
using SymbolicUtils

@parameters t x y
@variables u(t,x,y)[1:3]
@variables v(t,x,y)

function get_base_op(expr)
    expr = Symbolics.unwrap(expr)
    op = SymbolicUtils.operation(expr)
    if op == getindex
        return get_base_op(SymbolicUtils.arguments(expr)[1])
    end
    return op
end

println(get_base_op(u[1]))
println(get_base_op(v))
