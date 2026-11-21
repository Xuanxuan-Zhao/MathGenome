import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation

/-! K03.15.rs_uniform, paper.tex:3793–3809. The interval includes its
endpoints and may be a singleton. The integrator is the same real BV function
throughout; no continuity or monotonicity is assumed. `RCLike` covers ℝ and ℂ.
The supremum below is used only for bounded functions on nonempty [a,b]. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsUniform
open RsSums Variation
open Filter

abbrev supNormType := {K : Type} → [RCLike K] → ℝ → ℝ → (ℝ → K) → ℝ
noncomputable def supNormValue : supNormType := fun a b h =>
  sSup ((fun x => ‖h x‖) '' Set.Icc a b)

/-- The estimate holds for every bounded refinement-integrable integrand,
including when total variation is zero. -/
def integralBound : Prop :=
  ∀ {K : Type} [RCLike K] (a b : ℝ), a ≤ b →
    ∀ (h : ℝ → K) (α : ℝ → ℝ) (I : K),
    boundedVariationValue α a b → integralValue a b h α I →
    ‖I‖ ≤ supNormValue a b h * (totalVariationValue α a b).toReal

/-- Uniform convergence is written in its epsilon form on the interval;
no information about the ambient functions outside [a,b] is required. -/
def uniformStability : Prop :=
  ∀ {K : Type} [RCLike K] (a b : ℝ), a ≤ b →
    ∀ (α : ℝ → ℝ) (F : ℕ → ℝ → K) (f : ℝ → K) (J : ℕ → K),
    boundedVariationValue α a b →
    (∀ n, integralValue a b (F n) α (J n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc a b,
      ‖F n x - f x‖ < ε) →
    boundedOnValue a b f ∧ ∃ I : K,
      integralValue a b f α I ∧
      (∀ n, ‖I - J n‖ ≤ supNormValue a b (fun x => f x - F n x) *
        (totalVariationValue α a b).toReal) ∧
      Tendsto (fun n => supNormValue a b (fun x => f x - F n x) *
        (totalVariationValue α a b).toReal) atTop (nhds 0) ∧
      Tendsto J atTop (nhds I)

/-- Explicit zero-variation specialization: the limit integral and every
approximating integral have value zero. -/
def zeroVariation : Prop :=
  ∀ {K : Type} [RCLike K] (a b : ℝ), a ≤ b →
    ∀ (α : ℝ → ℝ) (F : ℕ → ℝ → K) (f : ℝ → K) (J : ℕ → K),
    boundedVariationValue α a b → totalVariationValue α a b = 0 →
    (∀ n, integralValue a b (F n) α (J n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc a b,
      ‖F n x - f x‖ < ε) →
    boundedOnValue a b f ∧ integralValue a b f α 0 ∧ ∀ n, J n = 0

end Specs.SingleVariableAnalysis.Ch15.RsUniform
