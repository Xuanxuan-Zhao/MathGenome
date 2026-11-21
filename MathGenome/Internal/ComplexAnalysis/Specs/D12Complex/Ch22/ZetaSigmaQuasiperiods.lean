import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ZetaSigmaConvergence

/-! Generator quasi-periods of the canonical regularized series/product.
The zeta equalities are equalities of meromorphic germs; no assertion is
made about the arbitrary scalar values assigned at poles. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods
abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice
abbrev zeta := Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta
abbrev sigma := Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma

/-- This fixed choice also supplies the constants for subsequent formulas. -/
def eta (ω₁ ω₂ ω : ℂ) : ℂ := 2 * zeta ω₁ ω₂ (ω / 2)
def eta_type := ℂ → ℂ → ℂ → ℂ

def zeta_quasiperiod_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ ω ∈ ({ω₁, ω₂} : Set ℂ), ∀ a : ℂ,
      (fun z => zeta ω₁ ω₂ (z + ω)) =ᶠ[𝓝[≠] a]
        (fun z => zeta ω₁ ω₂ z + eta ω₁ ω₂ ω)

def sigma_quasiperiod_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ ω ∈ ({ω₁, ω₂} : Set ℂ), ∀ z : ℂ,
      sigma ω₁ ω₂ (z + ω) =
        -Complex.exp (eta ω₁ ω₂ ω * (z + ω / 2)) * sigma ω₁ ω₂ z

/-- Every pole of the difference cancels, giving a constant entire extension. -/
def zeta_pole_cancellation_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ ω ∈ ({ω₁, ω₂} : Set ℂ), ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧ (∀ z, F z = eta ω₁ ω₂ ω) ∧
      ∀ a : ℂ, (fun z => zeta ω₁ ω₂ (z + ω) - zeta ω₁ ω₂ z) =ᶠ[𝓝[≠] a] F

/-- The ratio has the same nonzero constant germ at every point, including zeros. -/
def sigma_ratio_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ ω ∈ ({ω₁, ω₂} : Set ℂ), ∃ C : ℂ,
      C ≠ 0 ∧ C = -Complex.exp (eta ω₁ ω₂ ω * (ω / 2)) ∧
      ∀ a : ℂ,
        (fun z => sigma ω₁ ω₂ (z + ω) /
          (sigma ω₁ ω₂ z * Complex.exp (eta ω₁ ω₂ ω * z))) =ᶠ[𝓝[≠] a] (fun _ => C)

/-- Both constants are witnessed simultaneously and used in both identities. -/
def generator_quasiperiods_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∃ η₁ η₂ : ℂ,
    η₁ = eta ω₁ ω₂ ω₁ ∧ η₂ = eta ω₁ ω₂ ω₂ ∧
    (∀ a, (fun z => zeta ω₁ ω₂ (z + ω₁)) =ᶠ[𝓝[≠] a] (fun z => zeta ω₁ ω₂ z + η₁)) ∧
    (∀ a, (fun z => zeta ω₁ ω₂ (z + ω₂)) =ᶠ[𝓝[≠] a] (fun z => zeta ω₁ ω₂ z + η₂)) ∧
    (∀ z, sigma ω₁ ω₂ (z + ω₁) = -Complex.exp (η₁ * (z + ω₁ / 2)) * sigma ω₁ ω₂ z) ∧
    (∀ z, sigma ω₁ ω₂ (z + ω₂) = -Complex.exp (η₂ * (z + ω₂ / 2)) * sigma ω₁ ω₂ z)
end Specs.D12Complex.Ch22.ZetaSigmaQuasiperiods
