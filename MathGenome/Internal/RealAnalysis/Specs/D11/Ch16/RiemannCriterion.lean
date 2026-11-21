import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion

/-! The ordinary closed-cell Darboux integral is the calculus foundation's
`realIntegrableValue`. The ambient function is restricted to `[a,b]`; its
values outside that interval are immaterial. The discontinuities use
`ContinuousWithinAt`, including both endpoints. The measurable domain is the
completion of Borel volume, not Borel volume itself. -/

open Set MeasureTheory

namespace Specs.D11.Ch16.RiemannCriterion

/-- Both directions, for the given bounded representative. Completion has
exactly the same outer values as Borel volume on all subsets. -/
def riemann_criterion : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Specs.SingleVariableAnalysis.Ch08.DarbouxSums.boundedOnIntervalValue f a b →
    (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a b ↔
      Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)
        {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x} = 0)

/-- Actual measurability of the representative, extended by zero off `[a,b]`. -/
def representative_measurable : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a b →
    @Measurable ℝ ℝ
      (Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ))
      (borel ℝ) ((Icc a b).indicator f)

/-- The same conclusion on the trace sigma-algebra of the closed interval. -/
def restriction_measurable : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a b →
    @Measurable (Icc a b) ℝ
      (MeasurableSpace.comap Subtype.val
        (Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)))
      (borel ℝ) (fun x => f x)

/-- A domain-literal form for every function whose domain is exactly `[a,b]`.
The extension only supplies the ambient input expected by the established
Darboux convention; the discontinuities and measurability are those of `f`. -/
def subtype_criterion : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : Icc a b → ℝ),
    BddBelow (Set.range f) ∧ BddAbove (Set.range f) →
    let F := Function.extend Subtype.val f (fun _ : ℝ => (0 : ℝ))
    (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue F a b ↔
      Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)
        (Subtype.val '' {x | ¬ ContinuousAt f x}) = 0) ∧
    (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue F a b →
      @Measurable (Icc a b) ℝ
        (MeasurableSpace.comap Subtype.val
          (Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)))
        (borel ℝ) f)

end Specs.D11.Ch16.RiemannCriterion
