import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness

/-! Independent statements for the Lᵖ clause of paper.tex:2894–2938.
The canonical `Lp` quotient is the shared Bochner Lᵖ quotient. The accepted
scalar representative and equality results identify it with the ordinary
measurable a.e. quotient for both ℝ and ℂ. No restriction on the measure is made.
A finite interior exponent is represented by a real p > 1.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.P1.LpUniformConvexitySpec
universe u v

/-- One positive modulus works for all measures and both scalar fields. -/
def MeasureUniformModulus : Prop :=
  ∀ (p : ℝ) (hp : 1 < p) (ε : ℝ), 0 < ε → ε ≤ 2 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (𝕜 : Type v) [RCLike 𝕜]
      (X : Type u) [MeasurableSpace X] (μ : Measure X),
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
      ∀ f g : FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue 𝕜
        (ENNReal.ofReal p) μ,
        ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ε ≤ ‖f - g‖ →
          ‖(2 : 𝕜)⁻¹ • (f + g)‖ ≤ 1 - δ

/-- The manuscript closed-unit-ball predicate, including zero spaces. -/
def MeasureUniformConvexity : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] (X : Type u) [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue 𝕜 (ENNReal.ofReal p) μ)

end ExpandedFA.P1.LpUniformConvexitySpec
