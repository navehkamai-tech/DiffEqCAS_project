
function nondimensionalize_pde(sys::PDESystem, basis=SI_BASIS)
    if !has_full_dimensions(sys)
        throw(IOError("all symbols must have units for nondimensionalization"))
    end
    for eq in vcat(sys.eqs, sys.bcs)
        if !(eq.rhs==0||ModelingToolkit.get_unit(eq.lhs)==ModelingToolkit.get_unit(eq.rhs))
            throw(IOError("$(eq) has different units on each side"))
        end
    end
    vars=vcat(sys.ivs, sys.ps)
    dimensional_matrix = hcat(get_unit_vector.(vars)...)
    new_dvs_mapping = Dict{Symbol,Symbol}() #check if these types are correct. keys are the old dvs, values are the corresponding expressions
    if rank(dimensional_matrix)==LinearAlgebra.size(dimensional_matrix)[2]
        #=
        placeholder. find a way to dynamically add symbolic constants, denoted for the rest of the code by SC[dv] for dv in sys.dvs 
        =#
        for d in sys.dvs
            powers_vec=dimensional_matrix\dimension(get_units_vector(d))
            new_dvs_mapping[d] = SC[d]*prod(var[i]^powers_vec[i] for i ∈ 1:length(vars))
        end

    else
        pi_matrix = nullspace(dimensional_matrix)
        pi_groups=[]
        for col ∈ 1:rank(pi_matrix)
            pi_groups[col] = prod(var[i]^pi_matrix[i, col] for i ∈ 1:length(vars))
        end
        #=
        placeholder. find way to dynamically add new dependent variables, denoted for the rest of the code by DV[dv](..) for dv in sys.dvs
        =#
        for d in sys.dvs
            powers_vec=pinv(dimensional_matrix)*dimension(get_units_vector(d))
            new_dvs_mapping[d] = prod(var[i]^powers_vec[i] for i ∈ 1:length(vars))*DV[d](pi_groups...)
            J = transpose(jacobian(new_dvs_mapping.vals, new_dvs_mapping.keys; simplify=true))

        end

    end
end

