module Constants
using Symbolics
using Unitful
import Base.MathConstants as MC

# Define custom metadata keys
struct ConstantValue end
struct ConstantUnit end

# Helper to create a purely symbolic constant with attached data
function define_constant(name::Symbol, val::Number, unit=Unitful.NoUnits)
    sym = Symbolics.Sym{Real}(name)
    sym = Symbolics.setmetadata(sym, ConstantValue, val)
    sym = Symbolics.setmetadata(sym, ConstantUnit, unit)
    return Symbolics.Num(sym)
end

# Mathematical Constants
const π = define_constant(:π, MC.pi)
const pi = π
const ℯ = define_constant(:ℯ, MC.e)
const e = ℯ
const γ = define_constant(:γ, MC.eulergamma)
const φ = define_constant(:φ, MC.golden)
const catalan = define_constant(:catalan, MC.catalan)

# Complex & Boundary Constants
const ı = define_constant(:ı, im)
const ∞ = define_constant(:∞, Inf)
const inf = ∞

# Light speed
const c_0 = define_constant(:c_0, 299_792_458, u"m/s")
const c = c_0

# Planck constant (J * s)
const h = define_constant(:h, 6.62607015e-34, u"J*s")

# Reduced Planck constant / Dirac constant (h / 2π)
const ℏ = define_constant(:ℏ, 1.0545718176461565e-34, u"J*s")
const hbar = ℏ

# Elementary charge (C)
const q_e = define_constant(:q_e, 1.602176634e-19, u"C")
const e_charge = q_e

# Boltzmann constant (J / K)
const k_B = define_constant(:k_B, 1.380649e-23, u"J/K")
const k_b = k_B

# Avogadro constant (1 / mol)
const N_A = define_constant(:N_A, 6.02214076e23, u"mol^-1")

# Luminous efficacy of 540 THz radiation (lm / W)
const K_cd = define_constant(:K_cd, 683, u"lm/W")

# Hyperfine transition frequency of Cs-133 (Hz)
const Δν_Cs = define_constant(:Δν_Cs, 9_192_631_770, u"Hz")

# Universal gas constant: R = N_A * k_B (J / (mol * K))
const R_gas = define_constant(:R_gas, 8.31446261815324, u"J/(mol*K)")

# Newtonian constant of gravitation (m^3 / (kg * s^2))
const G_grav = define_constant(:G_grav, 6.67430e-11, u"m^3/(kg*s^2)")
const G = G_grav

# Standard acceleration of gravity (m / s^2)
const g_0 = define_constant(:g_0, 9.80665, u"m/s^2")
const g = g_0

# Vacuum electric permittivity / electric constant (F / m)
const ε_0 = define_constant(:ε_0, 8.8541878128e-12, u"F/m")
const eps0 = ε_0

# Vacuum magnetic permeability / magnetic constant (N / A^2 or H / m)
const μ_0 = define_constant(:μ_0, 1.25663706212e-6, u"H/m")
const mu0 = μ_0

# Stefan-Boltzmann constant (W / (m^2 * K^4))
const σ_SB = define_constant(:σ_SB, 5.670374419e-8, u"W/(m^2*K^4)")

# Electron mass
const m_e = define_constant(:m_e, 9.1093837015e-31, u"kg")

# Proton mass
const m_p = define_constant(:m_p, 1.67262192369e-27, u"kg")

# Neutron mass
const m_n = define_constant(:m_n, 1.67492749804e-27, u"kg")

# Atomic mass constant / Dalton (kg)
const m_u = define_constant(:m_u, 1.66053906660e-27, u"kg")
const u = m_u

export π, pi, ℯ, e, γ, φ, catalan, ı, ∞, inf
export c_0, c, h, ℏ, hbar, q_e, e_charge, k_B, k_b, N_A, K_cd, Δν_Cs, R_gas
export G_grav, G, g_0, g, ε_0, eps0, μ_0, mu0, σ_SB, m_e, m_p, m_n, m_u, u
end