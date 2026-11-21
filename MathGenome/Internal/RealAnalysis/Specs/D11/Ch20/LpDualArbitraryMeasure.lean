import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing

/-! Independent statements for paper.tex:5733–5739.

The source's scalar-linear map is the already specified continuous linear
bilinear integral pairing, g ↦ (f ↦ ∫ f*g). Native Lp is identified with the
ordinary measurable a.e. quotient by the upstream quotient construction.
The conjugacy condition expresses q = p/(p-1); both exponents are finite
when 1 < p < ∞. There is no size assumption on the positive measure.
-/
open MeasureTheory
open scoped ENNReal
universe u
namespace Specs.D11.Ch20.LpDualArbitraryMeasure

/-- The specified scalar-linear integral pairing is an isometric bijection
onto the continuous scalar dual on every positive measure space. -/
def lp_dual_arbitrary_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
      Isometry (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q) ∧
      Function.Bijective
        (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q)

/-- Every continuous linear functional has a unique ordinary a.e. density,
with actual product integrability and equality of norms. -/
def representation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜, ∃! g : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        ℓ f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖ℓ‖

end Specs.D11.Ch20.LpDualArbitraryMeasure
