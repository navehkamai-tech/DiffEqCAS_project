#=
Goals:
1) keep a stack of branches being processed; a split can produce several
   branches while preserving the union represented by the parent system;
2) keep a session-local LRU cache for expensive semantic checks;
3) store accepted derivation steps on each branch, so every branch retains its
   own history after repeated transformations and factor splits.
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

abstract type DerivationStep end

struct DerivationHistory
    steps::Vector{DerivationStep}
end

DerivationHistory() = DerivationHistory(DerivationStep[])

function append_derivation(history::DerivationHistory, step::DerivationStep)
    DerivationHistory(vcat(history.steps, [step]))
end

struct CoordTransformStep <: DerivationStep
    iv_mapping::Dict
    old_ivs::Vector{Symbolics.Num}
    new_ivs::Vector{Symbolics.Num}
    jacobian_inverse::Any
end

struct ParamTransformStep <: DerivationStep
    mapping::Dict
    old_parameters::Vector{Symbolics.Num}
    new_parameters::Vector{Symbolics.Num}
end

struct DepVarTransformStep <: DerivationStep
    mapping::Dict
    old_dvs::Vector{Symbolics.Num}
    new_dvs::Vector{Symbolics.Num}
end

struct FactorStep <: DerivationStep
    factors::Vector{Any}
    selected_factor::Any
    branch_index::Union{Nothing,Int}
end

mutable struct DiffEqBranch{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:Symbolics.Equation},B<:AbstractVector{<:Symbolics.Equation},T<:AbstractVector}
    identifier::Int
    name::String
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymbolicDomain
    domain_set::Union{Nothing,Tuple{<:AbstractVector{<:IntervalBoxes.IntervalBox},<:AbstractVector{<:IntervalBoxes.IntervalBox}}}
    trivial_sols::T
    # TODO: Replace `trivial_sols` with a branch-local record of factors
    # already split out, so repeated factorization cannot create duplicates.
    history::DerivationHistory
end

function Base.setproperty!(sys::DiffEqBranch, name::Symbol, value)
    if name === :domain
        normalized = value isa SymbolicDomain ? value : SymbolicDomain(value)
        setfield!(sys, :domain, normalized)
        setfield!(sys, :domain_set, nothing)
        return normalized
    end
    setfield!(sys, name, value)
end

function DiffEqBranch(eqs, bcs, domain, ivs, dvs; identifier=0, ps=Symbolics.Num[], name=:system,
    domain_set=nothing, trivial_solutions=Any[], history=DerivationHistory())
    normalized_ivs = Symbolics.Num[ivs...]
    normalized_dvs = Symbolics.Num[dvs...]
    normalized_ps = Symbolics.Num[ps...]
    normalized_eqs = Symbolics.Equation[eqs...]
    normalized_bcs = Symbolics.Equation[bcs...]
    normalized_domain = domain isa SymbolicDomain ? domain : SymbolicDomain(domain)
    DiffEqBranch(identifier, String(name), normalized_ivs, normalized_dvs, normalized_ps,
        normalized_eqs, normalized_bcs, normalized_domain, domain_set,
        trivial_solutions, history)
end

function DiffEqBranch(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system, domain_set=nothing, trivial_solutions=Any[],
    history=DerivationHistory(), identifier=0)
    DiffEqBranch(eqs, bcs, domain, ivs, dvs; identifier=identifier, ps=ps, name=name,
        domain_set=domain_set, trivial_solutions=trivial_solutions,
        history=history)
end

"""
Collection of branches representing a union of solution sets.

`seen` stores structural fingerprints, not derivation history.  This makes
duplicate suppression independent of how a branch was reached and naturally
collapses repeated factors such as `A^3 * B^2` into the distinct branches
`A = 0` and `B = 0`.
"""
mutable struct DiffEqSystem
    branches::Vector{DiffEqBranch}
    pending::Stack{DiffEqBranch} #I think I want to move the pending field
    completed::Vector{DiffEqBranch}
    seen::Set{UInt}
end

function DiffEqSystem(branches::Vector{<:DiffEqBranch}=DiffEqBranch[])
    normalized = DiffEqBranch[branches...]
    system = DiffEqSystem(normalized, Stack{DiffEqBranch}(),
        DiffEqBranch[], Set{UInt}())
    for branch in normalized
        branch.identifier == 0 &&
            (branch.identifier = reinterpret(Int, hash((branch.eqs, branch.bcs,
                branch.domain.pairs))))
        push!(system.seen, _branch_fingerprint(branch))
    end
    system
end

function DiffEqSystem(eqs, bcs, domain, ivs, dvs; kwargs...)
    DiffEqSystem([DiffEqBranch(eqs, bcs, domain, ivs, dvs; kwargs...)])
end

function DiffEqSystem(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system, domain_set=nothing, trivial_solutions=Any[],
    history=DerivationHistory(), identifier=0)
    DiffEqSystem([DiffEqBranch(eqs=eqs, ivs=ivs, dvs=dvs, ps=ps, bcs=bcs,
        domain=domain, name=name, domain_set=domain_set,
        trivial_solutions=trivial_solutions, history=history,
        identifier=identifier)])
end

DiffEqSystem() = DiffEqSystem(DiffEqBranch[])

function Base.getproperty(system::DiffEqSystem, name::Symbol)
    name in (:branches, :pending, :completed, :seen) &&
        return getfield(system, name)
    length(system.branches) == 1 ||
        throw(ArgumentError("$(name) is branch-specific; select a branch first"))
    getproperty(only(system.branches), name)
end

function Base.setproperty!(system::DiffEqSystem, name::Symbol, value)
    name in (:branches, :pending, :completed, :seen) &&
        return setfield!(system, name, value)
    length(system.branches) == 1 ||
        throw(ArgumentError("$(name) is branch-specific; select a branch first"))
    setproperty!(only(system.branches), name, value)
end

Base.length(system::DiffEqSystem) = length(system.branches)
Base.getindex(system::DiffEqSystem, index::Int) = system.branches[index]
Base.iterate(system::DiffEqSystem, state...) = iterate(system.branches, state...)

function _branch_fingerprint(branch::DiffEqBranch)
    hash((branch.ivs, branch.dvs, branch.ps, branch.eqs, branch.bcs,
        branch.domain.pairs, branch.trivial_sols))
end

function push_branch!(system::DiffEqSystem, branch::DiffEqBranch)
    branch.identifier == 0 &&
        (branch.identifier = reinterpret(Int, hash((branch.eqs, branch.bcs,
            branch.domain.pairs))))
    fingerprint = _branch_fingerprint(branch)
    fingerprint in system.seen && return false
    push!(system.seen, fingerprint)
    push!(system.pending, branch)
    true
end

function complete_branch!(system::DiffEqSystem, branch::DiffEqBranch)
    push!(system.completed, branch)
    branch
end

# TODO: add canonical expression/domain normalization to `_branch_fingerprint`
# so mathematically identical but structurally reordered branches also merge.
working_systems = Stack{DiffEqSystem}()

const cache_size = Ref{Int64}(1024)

global cache = LRU{Any,Any}(maxsize=cache_size[])

@enum SignState positive negative either undetermined
struct VarSign end
Symbolics.option_to_metadata_type(::Val{:sign}) = VarSign

function get_sign(var)
    value = unwrap(var)
    value isa Real && return value > 0 ? positive : value < 0 ? negative : undetermined
    Symbolics.getmetadata(value, VarSign, undetermined)
end

@enum DivisState divisible haszero undetermined
