import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SchauderHatBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HaarUnconditional

/-!
The complete function-space basis theorem `fa2:p1:schauder-haar`,
paper.tex:4380–4387. The canonical upstream definitions specify the actual
closed unit interval, Lebesgue measure, and dyadic order: 1,t followed by
height-one hats, and 1 followed by the unnormalised Haar functions.
The raw basis property means unique natural-order norm convergence;
unconditionality means convergence of the net of all finite subsums.
Conditionality is the basis property together with failure of unconditionality.
The scalar field ranges over both real and complex fields through RCLike.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal unitInterval
universe u

namespace ExpandedFA.P1.SchauderHaar.Spec

/-- The endpoint Haar basis fails the same unconditional-basis predicate used
for the interior exponents. Its Schauder property is included in the full theorem. -/
def HaarL1Conditionality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (Lp 𝕜 1 (volume : Measure I)) (HaarBasis.Spec.haarLp 𝕜 1)

/-- All claims of the source theorem, including p=1 and both scalar fields. -/
def FunctionSpaceBases : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (SchauderHatBasis.Spec.basis 𝕜) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
      C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (HaarBasis.Spec.haarLp 𝕜 p)) ∧
    (¬ C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (SchauderHatBasis.Spec.FunctionSpace 𝕜) (SchauderHatBasis.Spec.basis 𝕜)) ∧
    (¬ C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (Lp 𝕜 1 (volume : Measure I)) (HaarBasis.Spec.haarLp 𝕜 1)) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
        (Lp 𝕜 p (volume : Measure I)) (HaarBasis.Spec.haarLp 𝕜 p))

end ExpandedFA.P1.SchauderHaar.Spec
