#=
goals: 
1) have a stack of the current systems being processed. certain processes will output multiple systems rather than one, so a stack is needed to manage it
2) have a LRUCache for global caching. create the function that gives a value to each thing cached
3) add a field to the DiffEqSystem struct for it's history. update functions to append the current process to the outputted system's history
=#

struct SymbolicDomain
    pairs::Vector{Pair}
    variables::Vector{Any}

    function SymbolicDomain(pairs)
        normalized = Pair[]
        variables = Any[]
        for pair in pairs
            if pair isa Symbolics.VarDomainPairing
                pair = pair.variables => [pair]
            end
            pair isa Pair || throw(ArgumentError("domain entries must be pairs of variables and constraints"))
            key, constraints = pair
            key_variables = key isa Tuple ? collect(key) : Any[key]
            isempty(key_variables) && throw(ArgumentError("domain keys cannot be empty"))
            constraints isa AbstractVector ||
                throw(ArgumentError("domain constraints must be stored in a vector"))
            for variable in key_variables
                any(isequal(variable), variables) || push!(variables, variable)
            end
            push!(normalized, key => collect(constraints))
        end
        new(normalized, variables)
    end
end

Base.length(domain::SymbolicDomain) = length(domain.pairs)
Base.getindex(domain::SymbolicDomain, index::Int) = domain.pairs[index]
Base.iterate(domain::SymbolicDomain, state...) = iterate(domain.pairs, state...)
Base.isempty(domain::SymbolicDomain) = isempty(domain.pairs)

_domain_pairs(domain::SymbolicDomain) = domain.pairs
_domain_pairs(domain) = domain

# Components are the connected groups represented by the domain keys. They are
# structural metadata only; integral factorization also requires a separable
# integrand and a product domain.
domain_variables(domain::SymbolicDomain) = copy(domain.variables)
domain_components(domain::SymbolicDomain) = copy(domain.pairs)

mutable struct DiffEqSystem{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:Symbolics.Equation},B<:AbstractVector{<:Symbolics.Equation},T<:AbstractVector}
    name::String
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymbolicDomain
end

function Base.setproperty!(sys::DiffEqSystem, name::Symbol, value)
    if name === :domain
        normalized = value isa SymbolicDomain ? value : SymbolicDomain(value)
        setfield!(sys, :domain, normalized)
        setfield!(sys, :domain_set, nothing)
        return normalized
    end
    setfield!(sys, name, value)
end

function DiffEqSystem(eqs, bcs, domain, ivs, dvs; ps=Symbolics.Num[], name=:system,
    domain_set=nothing, trivial_solutions=Any[])
    normalized_ivs = Symbolics.Num[ivs...]
    normalized_dvs = Symbolics.Num[dvs...]
    normalized_ps = Symbolics.Num[ps...]
    normalized_eqs = Symbolics.Equation[eqs...]
    normalized_bcs = Symbolics.Equation[bcs...]
    normalized_domain = domain isa SymbolicDomain ? domain : SymbolicDomain(domain)
    DiffEqSystem(String(name), normalized_ivs, normalized_dvs, normalized_ps,
        normalized_eqs, normalized_bcs, normalized_domain, domain_set, trivial_solutions)
end

function DiffEqSystem(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system, domain_set=nothing, trivial_solutions=Any[])
    DiffEqSystem(eqs, bcs, domain, ivs, dvs; ps=ps, name=name,
        domain_set=domain_set, trivial_solutions=trivial_solutions)
end

working_systems = Stack{DiffEqSystem}()

const cache_size = Ref{Int64}(100)

global cache = LRU{Any,Any}(maxsize=cache_size)

@enum SignState positive negative either undetermined
struct VarSign end
Symbolics.option_to_metadata_type(::Val{:sign}) = VarSign

function get_sign(var)
    value = unwrap(var)
    value isa Real && return value > 0 ? positive : value < 0 ? negative : undetermined
    Symbolics.getmetadata(value, VarSign, undetermined)
end

@enum DivisState divisible haszero undetermined
struct VarDivisibility end
Symbolics.option_to_metadata_type(::Val{:divisible}) = VarDivisibility

function get_divisibility(var)
    value = unwrap(var)
    value isa Real && return value == 0 ? haszero : divisible
    Symbolics.getmetadata(value, VarDivisibility, undetermined)
end
