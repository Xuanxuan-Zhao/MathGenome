import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Independent specification of the circle integration clause of
`paper.tex:5334–5352`, `fa2:p1:banach-measure`.

`UnitAddCircle` is `ℝ / ℤ`, with Lebesgue (Haar) volume of total mass one.
`lp … ∞` consists of actual, everywhere defined bounded functions, without
any continuity or measurability requirement; it is not an almost-everywhere
quotient. `NullMeasurable` is measurability for the completion of volume,
so the extension clause includes all bounded Lebesgue measurable functions.
The integral is the ordinary Lebesgue/Bochner integral for this volume.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.P1

/-- All bounded real functions on the unit additive circle, with supremum norm. -/
abbrev BoundedCircleFunction := lp (fun _ : UnitAddCircle => ℝ) ∞

/-- Translation on actual bounded functions. -/
def circleTranslate (a : UnitAddCircle) (f : BoundedCircleFunction) :
    BoundedCircleFunction :=
  ⟨fun x => f (a + x), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨x, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (a + x)⟩⟩

end ExpandedFA.P1

namespace Specs.ExpandedFA.P1.BanachCircleIntegration

/-- Positive, translation-invariant, norm-one extension of the Lebesgue integral
from bounded Lebesgue measurable functions to all bounded circle functions. -/
def banachCircleIntegrationType : Prop :=
  ∃ I : _root_.ExpandedFA.P1.BoundedCircleFunction →L[ℝ] ℝ,
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) ∧
    ‖I‖ = 1 ∧
    (∀ a f, I (_root_.ExpandedFA.P1.circleTranslate a f) = I f) ∧
    (∀ f, NullMeasurable (fun x => f x) volume →
      I f = ∫ x : UnitAddCircle, f x)

end Specs.ExpandedFA.P1.BanachCircleIntegration
