import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods

/-! Legendre's relation and arbitrary integer shifts (paper.tex, d12:22-08).
Zeta identities use punctured germs at every point, including poles. The
integer power in the sigma formula includes negative integers. -/
noncomputable section
open Filter
open scoped Topology
namespace Specs.D12Complex.Ch22.LegendreLatticeShifts
open ZetaSigmaQuasiperiods (eta zeta sigma)

def legendre_relation_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    eta ω₁ ω₂ ω₁ * ω₂ - eta ω₁ ω₂ ω₂ * ω₁ = 2 * Real.pi * Complex.I

def zeta_lattice_shift_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ m n : ℤ, ∀ a : ℂ,
    (fun z => zeta ω₁ ω₂ (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂))) =ᶠ[𝓝[≠] a]
      (fun z => zeta ω₁ ω₂ z + ((m : ℂ) * eta ω₁ ω₂ ω₁ +
        (n : ℂ) * eta ω₁ ω₂ ω₂))

def sigma_lattice_shift_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ m n : ℤ, ∀ z : ℂ,
    sigma ω₁ ω₂ (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂)) =
      (-1 : ℂ) ^ (m + n + m * n) *
        Complex.exp (((m : ℂ) * eta ω₁ ω₂ ω₁ + (n : ℂ) * eta ω₁ ω₂ ω₂) *
          (z + ((m : ℂ) * ω₁ + (n : ℂ) * ω₂) / 2)) * sigma ω₁ ω₂ z
end Specs.D12Complex.Ch22.LegendreLatticeShifts
