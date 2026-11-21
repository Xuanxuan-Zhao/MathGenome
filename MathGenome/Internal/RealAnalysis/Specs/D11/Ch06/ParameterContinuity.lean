import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements for paper.tex:2043–2057. The parameter lives in
the closed interval with its subspace topology. Thus continuity at either
endpoint is the relative, one-sided assertion. Only the individual sections
in the measure variable are assumed measurable; no joint measurability is used.
The shared scalar integral requires a proof of finite absolute integrability.
-/

open Set MeasureTheory
universe u
noncomputable section
namespace Specs.D11.Ch06.ParameterContinuity
open Specs.D11.Ch06.ScalarIntegral

/-- Pointwise continuity at a fixed parameter passes through the integral.
`RCLike` includes the complex statement in the paper and its real version.
There is no finiteness, completeness, or sigma-finiteness assumption on `μ`. -/
def parameter_continuity_at : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (a b : ℝ), a < b →
    ∀ (F : X → Icc a b → 𝕜) (g : X → ℝ)
      (hF : ∀ t, scalarIntegrable_value μ (fun x => F x t)),
      scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
      (∀ x t, ‖F x t‖ ≤ g x) →
      ∀ t₀ : Icc a b, (∀ x, ContinuousAt (F x) t₀) →
        ContinuousAt
          (fun t => scalarIntegral_value μ (fun x => F x t) (hF t)) t₀

/-- Continuous parameter sections give a continuous integral on all of `[a,b]`,
including its endpoints. -/
def parameter_continuity : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (a b : ℝ), a < b →
    ∀ (F : X → Icc a b → 𝕜) (g : X → ℝ)
      (hF : ∀ t, scalarIntegrable_value μ (fun x => F x t)),
      scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
      (∀ x t, ‖F x t‖ ≤ g x) →
      (∀ x, Continuous (F x)) →
        Continuous (fun t => scalarIntegral_value μ (fun x => F x t) (hF t))

end Specs.D11.Ch06.ParameterContinuity
