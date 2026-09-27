
struct DiffEqSystem
    name::String
    ivs::Vector{Symbolics.Num}
    dvs::Vector{Symbolics.Num}
    ps::Vector{Symbolics.Num}
    eqs::Vector{Symbolics.Equation}
    bcs::Vector{Symbolics.Num}
    domain_constraints::Vector{Pair{Any,Symbolics.Num}}
    domain_set::Vector{IntervalBoxes.IntervalBox}
    trivial_sols::Vector{Pair{Any,Symbolics.Equations}}

    function DiffEqSystem(name="system", ivs, dvs, eqs, bcs, domain_constraints, domain_set=nothing, trivial_solutions=[])
        new(name, ivs, dvs, eqs, bcs, domain_constraints, domain_set, trivial_solutions)
    end
end

#defining sign metadata for symbols
@enum SignState positive negative either undetermined
struct VarSign end
Symbolics.option_to_metadata_type(::Val{:sign}) = VarSign

function get_sign(var)
    var_unwrapped = unwrap(var)

    if var_unwrapped isa Real
        return var_unwrapped > 0 ? positive : (var_unwrapped < 0 ? negative : undetermined)
    end

    return Symbolics.getmetadata(var_unwrapped, VarSign, undetermined)
end

#defining divisibility metadata for symbols
@enum DivisState divisible haszero undetermined
struct VarDivisibility end
Symbolics.option_to_metadata_type(::Val{:divisible}) = VarDivisibility

function get_divisibility(var)
    var_unwrapped = unwrap(var)

    if var_unwrapped isa Real
        return var_unwrapped == 0 ? haszero : divisible
    end

    return Symbolics.getmetadata(var_unwrapped, VarDivisibility, undetermined)
end