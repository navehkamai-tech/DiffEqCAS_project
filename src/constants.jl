module Constants
using Symbolics
import DynamicQuantities as DQ
import Base.MathConstants as MC
import ModelingToolkit: constants

# Define custom metadata keys
struct ConstantValue end

# Mathematical Constants
@constants π=MC.pi e=MC.e γ=MC.eulergamma φ=MC.golden catalan=MC.catalan

# Light speed
@constants c_0 = 299_792_458 [unit=DQ.m/DQ.s]
const c = c_0

# Planck constant (J * s)
@constants h = 6.62607015e-34 [unit=DQ.J*DQ.s]

# Reduced Planck constant / Dirac constant (h / 2π)
@constants ħ = 1.0545718176461565e-34 [unit=DQ.J*DQ.s]
const hbar = ħ

# Elementary charge (C)
@constants q_e = 1.602176634e-19 [unit=DQ.C]
const e_charge = q_e

# Boltzmann constant (J / K)
@constants k_B = 1.380649e-23 [unit=DQ.J/DQ.K]
const k_b = k_B

# Avogadro constant (1 / mol)
@constants N_A = 6.02214076e23 [unit=DQ.mol^-1]

# Luminous efficacy of 540 THz radiation (lm / W)
@constants K_cd = 683 [unit=DQ.cd/DQ.W]

# Hyperfine transition frequency of Cs-133 (Hz)
@constants Δν_Cs = 9_192_631_770 [unit=DQ.Hz]

# Universal gas constant: R = N_A * k_B (J / (mol * K))
@constants R_gas = 8.31446261815324 [unit=DQ.J/(DQ.mol*DQ.K)]

# Newtonian constant of gravitation (m^3 / (kg * s^2))
@constants G_grav = 6.67430e-11 [unit=DQ.m^3/(DQ.kg*DQ.s^2)]
const G = G_grav

# Standard acceleration of gravity (m / s^2)
@constants g_0 = 9.80665 [unit=DQ.m/DQ.s^2]
const g = g_0

# Vacuum electric permittivity / electric constant (F / m)
@constants ε_0 = 8.8541878128e-12 [unit=DQ.F/DQ.m]
const eps0 = ε_0

# Vacuum magnetic permeability / magnetic constant (N / A^2 or H / m)
@constants μ_0 = 1.25663706212e-6 [unit=DQ.H/DQ.m]
const mu0 = μ_0

# Stefan-Boltzmann constant (W / (m^2 * K^4))
@constants σ_SB = 5.670374419e-8 [unit=DQ.W/(DQ.m^2*DQ.K^4)]

# Electron mass
@constants m_e = 9.1093837015e-31 [unit=DQ.kg]

# Proton mass
@constants m_p = 1.67262192369e-27 [unit=DQ.kg]

# Neutron mass
@constants m_n = 1.67492749804e-27 [unit=DQ.kg]

# Atomic mass constant / Dalton (kg)
@constants m_u = 1.66053906660e-27 [unit=DQ.kg]
const u = m_u

export π, e, γ, φ, catalan
export c_0, c, h, ħ, hbar, q_e, e_charge, k_B, k_b, N_A, K_cd, Δν_Cs, R_gas
export G_grav, G, g_0, g, ε_0, eps0, μ_0, mu0, σ_SB, m_e, m_p, m_n, m_u, u

end
