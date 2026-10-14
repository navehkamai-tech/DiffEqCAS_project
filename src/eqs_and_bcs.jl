
const EqId = Int

struct SymEquation
    id::EqId
    residual::Symbolics.Num

    function SymEquation(residual::Symbolics.Num, id::EqId = UNASSIGNED_ID)
        id=get_unique_id()
        new(id, residual)
    end
end

SymEquation(eq::Symbolics.Equation,id::EqId = UNASSIGNED_ID) = SymEquation(eq.lhs - eq.rhs, id)
SymEquation(expr::Expr, id::EqId = UNASSIGNED_ID) = SymEquation(wrap(expr), id)

Symbolics.simplify(eq::SymEquation) = SymEquation(eq.id, simplify(eq.residual))
Symbolics.expand(eq::SymEquation) = SymEquation(eq.id, expand(eq.residual))



#operator used for boundary conditions
@register_symbolic Restrict(expr, domain)
SU.promote_symtype(::typeof(Restrict), _...) = Real
