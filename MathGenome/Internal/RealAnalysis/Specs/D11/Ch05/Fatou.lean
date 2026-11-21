import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException

/-! Independent statements for Fatou's inequality, paper.tex:1637–1657.
The integral is the shared supremum over finite nonnegative simple minorants.
`ℝ≥0∞` is the full nonnegative extended range, including infinity. The a.e.
premise uses a measurable null envelope in the original sigma-algebra.
There are no size, completeness, or integrability assumptions on the measure
or functions. Natural indices enumerate the source's sequence starting at one.
-/

open Filter MeasureTheory
open scoped ENNReal
universe u

namespace Specs.D11.Ch05.Fatou

open NonnegativeIntegral
open _root_.Specs.D11.Ch04.AeCommonException

/-- The integral of the pointwise lower limit is bounded by the lower limit
of the integrals, with both sides allowed to be infinite. -/
def fatou : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞), (∀ n, Measurable (f n)) →
    nonnegativeIntegral_value μ (fun x => liminf (fun n => f n x) atTop) ≤
      liminf (fun n => nonnegativeIntegral_value μ (f n)) atTop

/-- The source's additional conclusion for a measurable nonnegative function
which is bounded by the lower limit almost everywhere. -/
def fatou_of_ae_le_liminf : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞) (g : X → ℝ≥0∞),
    (∀ n, Measurable (f n)) → Measurable g →
    almostEverywhere_value μ (fun x => g x ≤ liminf (fun n => f n x) atTop) →
    nonnegativeIntegral_value μ g ≤
      liminf (fun n => nonnegativeIntegral_value μ (f n)) atTop

end Specs.D11.Ch05.Fatou
