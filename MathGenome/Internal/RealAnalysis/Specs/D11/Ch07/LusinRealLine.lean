import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! Independent statements of paper.tex:2285–2295.
The source structure on the real line is the completion of Borel Lebesgue
measure. In particular `MeasurableSet` below admits all Lebesgue sets, and
measurability of `f` uses its trace, not the Borel trace. The error uses the
same outer evaluation as Borel volume (`Measure.completion_apply`). -/

noncomputable section
open Set MeasureTheory

namespace Specs.D11.Ch07.LusinRealLine

/-- The canonical completed Borel Lebesgue structure, on the type `ℝ`. -/
abbrev realLebesgueSpace : MeasurableSpace ℝ :=
  inferInstanceAs (MeasurableSpace (NullMeasurableSpace ℝ (volume : Measure ℝ)))

/-- The full Carathéodory test for real Lebesgue outer measure. This bridge
makes the admitted domain explicit, including non-Borel measurable sets. -/
def lebesgue_caratheodory : Prop :=
  ∀ A : Set ℝ, MeasurableSet[realLebesgueSpace] A ↔
    ∀ S : Set ℝ, (volume : Measure ℝ) S = volume (S ∩ A) + volume (S \ A)

/-- No boundedness or finite-measure-domain hypothesis is imposed. -/
def lusin_real : Prop :=
  ∀ (E : Set ℝ), MeasurableSet[realLebesgueSpace] E →
    ∀ (f : E → ℝ),
      @Measurable E ℝ (realLebesgueSpace.comap Subtype.val) (borel ℝ) f →
      ∀ ε : ℝ, 0 < ε → ∃ (F : Set ℝ) (hFE : F ⊆ E) (g : ℝ → ℝ),
        IsClosed F ∧ Continuous g ∧
        (volume : Measure ℝ).completion (E \ F) < ENNReal.ofReal ε ∧
        ∀ x : F, g x = f ⟨x, hFE x.property⟩

/-- The full complex-valued assertion, with an extension on all of `ℝ`. -/
def lusin_complex : Prop :=
  ∀ (E : Set ℝ), MeasurableSet[realLebesgueSpace] E →
    ∀ (f : E → ℂ),
      @Measurable E ℂ (realLebesgueSpace.comap Subtype.val) (borel ℂ) f →
      ∀ ε : ℝ, 0 < ε → ∃ (F : Set ℝ) (hFE : F ⊆ E) (g : ℝ → ℂ),
        IsClosed F ∧ Continuous g ∧
        (volume : Measure ℝ).completion (E \ F) < ENNReal.ofReal ε ∧
        ∀ x : F, g x = f ⟨x, hFE x.property⟩

end Specs.D11.Ch07.LusinRealLine
