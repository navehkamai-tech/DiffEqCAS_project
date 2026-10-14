
const EqId = Int

struct SymEquation
    id::EqId
    residual::Symbolics.Num

    function SymEquation(lhs, rhs)
        new(id, wrap(lhs) - wrap(rhs))
    end
end

Symbolics.simplify(eq::SymEquation) = SymEquation(eq.id, simplify(eq.residual))
Symbolics.expand(eq::SymEquation) = SymEquation(eq.id, expand(eq.residual))

