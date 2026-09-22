
SI_BASIS = [:Mass, :Length, :Time, :Temperature, :Current, :Luminosity, :Amount]
#=
if defining a custom basis with a new unit U with dimension D, then each unit in the system that has a non zero power of U needs to be redefined with U
example - defining heat as a new basis unit:

Unitful.register(@__MODULE__)
@dimension 𝐇 "𝐇" Heat
@refunit J_h "J_h" HeatJoule 𝐇 true
const Heat_Basis = vcat(SI_BASIS,[:Heat])

then defining a modified version of another unit such as Watt for this system:

@unit W_h "W_h" HeatWatt 1J_h/s true (true for automatic metric prefixes and scaling)

good practice to have the custom basis unit in the subscript of the modified unit
=#

#helpers for nondimensionalize_pde
function has_full_dimensions(sys::PDESystem)
    symbols = vcat(sys.ivs, sys, dvs, sys.ps)
    return !any(getunit(v)===nothing for v in symbols)
end

function get_units_vector(var, basis::AbstractVector{Symbol}=SI_BASIS)
    # 1. Extract the unit and underlying dimensions
    u = ModelingToolkit.get_unit(var)
    d = dimension(u)
    dims = typeof(d).parameters[1]

    # 2. Initialize a dictionary with 0//1 for every dimension in our basis
    powers = Dict{Symbol,Rational{Int}}(dim => 0//1 for dim in basis)

    # 3. Populate the dictionary with the extracted rational powers
    for dim in dims
        dim_name = Unitful.name(dim)
        if haskey(powers, dim_name)
            powers[dim_name] = Unitful.power(dim)
        end
    end

    # 4. Extract and return the values in the exact order of the basis array
    return [powers[b] for b in basis]
end
