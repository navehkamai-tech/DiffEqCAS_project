
struct DiffEqSystem
    name
    ivs
    dvs
    ps
    eqs
    bcs
    domain
    domain_set
    trivial_sols
end

function DiffEqSystem(
    eqs,
    bcs,
    domain,
    ivs,
    dvs;
    ps=Symbolics.Num[],
    name=:system,
    domain_set=nothing,
    trivial_solutions=Any[],
)
    return DiffEqSystem(name, ivs, dvs, ps, eqs, bcs, domain, domain_set, trivial_solutions)
end

function DiffEqSystem(;
    eqs,
    ivs,
    dvs,
    ps=Symbolics.Num[],
    bcs=Symbolics.Equation[],
    domain=Pair[],
    name=:system,
    domain_set=nothing,
    trivial_solutions=Any[],
)
    return DiffEqSystem(eqs, bcs, domain, ivs, dvs;
        ps, name, domain_set, trivial_solutions)
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