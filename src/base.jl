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
            pair isa Pair || throw(ArgumentError("domain entries must be pairs of variables and constraints"))
            key, constraints = pair
            key_variables = key isa Tuple ? collect(key) : Any[key]
            isempty(key_variables) && throw(ArgumentError("domain keys cannot be empty"))
            constraints isa AbstractVector ||
                throw(ArgumentError("domain constraints must be stored in a vector"))
            sort!(key_variables, by=string)
            for variable in key_variables
                any(isequal(variable), variables) || push!(variables, variable)
            end
            push!(normalized, key => collect(constraints))
        end
        sort!(normalized, by=pair -> string(pair.first isa Tuple ? pair.first[begin] : pair.first))
        new(normalized, variables)
    end
end

"""
    SymbolicRestriction(residual, relation)

A branch-local relation between a symbolic residual and zero.  Equalities are
represented by the branch equations; restrictions represent only non-equality
relations used to describe a branch cell.
"""
struct SymbolicRestriction
    residual::Symbolics.Num
    relation::Symbol

    function SymbolicRestriction(residual, relation)
        relation_symbol = relation isa Symbol ? relation : Symbol(string(relation))
        relation_symbol in (Symbol("!="), :>, Symbol(">="), :<, Symbol("<=")) ||
            throw(ArgumentError("unsupported symbolic restriction relation: $relation"))
        new(wrap(residual), relation_symbol)
    end
end

const _restriction_relations = (Symbol("!="), :>, Symbol(">="), :<, Symbol("<="))

function _restriction_operator(restriction::SymbolicRestriction)
    relation = restriction.relation
    relation === Symbol("!=") && return !=
    relation === :> && return >
    relation === Symbol(">=") && return >=
    relation === :< && return <
    relation === Symbol("<=") && return <=
end

function _restriction_expression(restriction::SymbolicRestriction)
    _restriction_operator(restriction)(restriction.residual, 0)
end

function _normalize_restriction(restriction::SymbolicRestriction)
    SymbolicRestriction(simplify(restriction.residual), restriction.relation)
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

struct DomainRestrictStep <: DerivationStep
    variables::Vector{Symbolics.Num}
    constraint::Symbolics.Num
end

mutable struct DiffEqBranch{I<:AbstractVector{<:Symbolics.Num},D<:AbstractVector{<:Symbolics.Num},P<:AbstractVector{<:Symbolics.Num},E<:AbstractVector{<:Symbolics.Equation},B<:AbstractVector{<:Symbolics.Equation}}
    name::String
    ivs::I
    dvs::D
    ps::P
    eqs::E
    bcs::B
    domain::SymbolicDomain
    domain_set::Union{Nothing,Tuple{<:AbstractVector{<:IntervalBoxes.IntervalBox},<:AbstractVector{<:IntervalBoxes.IntervalBox}}}
    restrictions::Vector{SymbolicRestriction}
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

function DiffEqBranch(eqs, bcs, domain, ivs, dvs; ps=Symbolics.Num[], name=:system,
    domain_set=nothing, restrictions=SymbolicRestriction[],
    history=DerivationHistory())
    normalized_ivs = Symbolics.Num[ivs...]
    normalized_dvs = Symbolics.Num[dvs...]
    normalized_ps = Symbolics.Num[ps...]
    normalized_eqs = Symbolics.Equation[eqs...]
    normalized_bcs = Symbolics.Equation[bcs...]
    normalized_domain = domain isa SymbolicDomain ? domain : SymbolicDomain(domain)
    normalized_restrictions = SymbolicRestriction[restrictions...]
    DiffEqBranch(String(name), normalized_ivs, normalized_dvs, normalized_ps,
        normalized_eqs, normalized_bcs, normalized_domain, domain_set,
        normalized_restrictions, history)
end

function DiffEqBranch(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system, domain_set=nothing,
    restrictions=SymbolicRestriction[], history=DerivationHistory())
    DiffEqBranch(eqs, bcs, domain, ivs, dvs; ps=ps, name=name,
        domain_set=domain_set, restrictions=restrictions,
        history=history)
end

struct RootBranch
    ivs::Tuple
    dvs::Tuple
    ps::Tuple
    eqs::Tuple
    bcs::Tuple
    domain::SymbolicDomain
end

function RootBranch(DiffEqBranch)
    ivs = Tuple(DiffEqBranch.ivs...)
    dvs = Tuple(DiffEqBranch.dvs...)
    ps = Tuple(DiffEqBranch.ps...)
    eqs = Tuple(DiffEqBranch.eqs...)
    bcs = Tuple(DiffEqBranch.bcs...)
    RootBranch(ivs, dvs, ps, eqs, bcs, domain)
end

struct SystemRoot
    branches::Tuple #tuple of RootBranches
end

function SystemRoot(branches::Vector{<:DiffEqBranch}=DiffEqBranch[])
    root_branches = RootBranch[]
    for branch in branches
        push!(root_branches, RootBranch(branch))
    end
    SystemRoot(Tuple(root_branches...))
end

SystemRoot(branch::DiffEqBranch) = SystemRoot([branch])

"""
Collection of branches representing a union of solution sets.

Branch generation is responsible for maintaining disjoint partition cells.
No global duplicate set is kept: a branch's inherited restrictions are part of
the logical cell it represents.
"""
mutable struct DiffEqSystem
    branches::Vector{DiffEqBranch}
    pending::Stack{DiffEqBranch} #I think I want to move the pending field
    completed::Vector{DiffEqBranch}
    root::SystemRoot
end

SystemRoot(sys::DiffEqSystem) = SystemRoot(sys.branches)

function record_root!(branches::Vector{<:DiffEqBranch})
    root === nothing && DiffEqSystem.root = SystemRoot(branches)
end

function DiffEqSystem(branches::Vector{<:DiffEqBranch}=DiffEqBranch[], record_root=true)
    normalized = DiffEqBranch[branches...]
    if record_root
        DiffEqSystem(normalized, Stack{DiffEqBranch}(), DiffEqBranch[], SystemRoot(branches))
    end
    println("danger: root is not recorded")
    DiffEqSystem(normalized, Stack{DiffEqBranch}(), DiffEqBranch[], root=nothing)
end

function DiffEqSystem(eqs, bcs, domain, ivs, dvs; kwargs...)
    DiffEqSystem([DiffEqBranch(eqs, bcs, domain, ivs, dvs; kwargs...)])
end

function DiffEqSystem(; eqs, ivs, dvs, ps=Symbolics.Num[], bcs=Symbolics.Equation[],
    domain=Pair[], name=:system, domain_set=nothing,
    restrictions=SymbolicRestriction[], history=DerivationHistory())
    DiffEqSystem([DiffEqBranch(eqs=eqs, ivs=ivs, dvs=dvs, ps=ps, bcs=bcs,
        domain=domain, name=name, domain_set=domain_set,
        restrictions=restrictions, history=history)])
end

DiffEqSystem() = DiffEqSystem(DiffEqBranch[])

# Replace a branch's state without replacing the branch object stored by its
# parent system.  This also preserves branch-local metadata not involved in
# the transformation.
function _replace_branch!(
    branch::DiffEqBranch;
    eqs=branch.eqs, ivs=branch.ivs, dvs=branch.dvs, ps=branch.ps, bcs=branch.bcs, domain=branch.domain, history=branch.history, restrictions=branch.restrictions
)
    # Constructors used to perform this conversion implicitly.  Keep it here
    # because transformed intermediate collections may have eltype `Any`.
    branch.eqs = typeof(branch.eqs)(eqs)
    branch.ivs = typeof(branch.ivs)(ivs)
    branch.dvs = typeof(branch.dvs)(dvs)
    branch.ps = typeof(branch.ps)(ps)
    branch.bcs = typeof(branch.bcs)(bcs)
    branch.domain = domain
    branch.history = history
    branch.restrictions = SymbolicRestriction[restrictions...]
    branch
end

function Base.getproperty(system::DiffEqSystem, name::Symbol)
    name in (:branches, :pending, :completed) &&
        return getfield(system, name)
    length(system.branches) == 1 ||
        throw(ArgumentError("$(name) is branch-specific; select a branch first"))
    getproperty(only(system.branches), name)
end

function Base.setproperty!(system::DiffEqSystem, name::Symbol, value)
    name in (:branches, :pending, :completed) &&
        return setfield!(system, name, value)
    length(system.branches) == 1 ||
        throw(ArgumentError("$(name) is branch-specific; select a branch first"))
    setproperty!(only(system.branches), name, value)
end

Base.length(system::DiffEqSystem) = length(system.branches)
Base.getindex(system::DiffEqSystem, index::Int) = system.branches[index]
Base.iterate(system::DiffEqSystem, state...) = iterate(system.branches, state...)

function push_branch!(system::DiffEqSystem, branch::DiffEqBranch)
    push!(system.pending, branch)
    true
end

function complete_branch!(system::DiffEqSystem, branch::DiffEqBranch)
    push!(system.completed, branch)
    branch
end

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
