import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.CompletionVersions
import MathGenome.Internal.RealAnalysis.D11.Ch02.Completion
import MathGenome.Internal.RealAnalysis.D11.Ch04.AeCommonException
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
Versions for the completion, paper.tex:1377–1411.

The Borel sigma-algebras of EReal, real, and complex scalars are countably
generated. Thus a function measurable in the completion has an originally
measurable a.e. version, by `NullMeasurable.aemeasurable`. This library result
uses a single measurable null envelope for the countably many generators and
does not require any finiteness assumption on the measure or the source.
For the bounding pair we change that version to the two infinities on its
original measurable null envelope. Conversely the bounds squeeze the given
function to an original measurable function off such an envelope.
-/

open Set MeasureTheory MeasurableSpace
universe u v

namespace D11.Ch04.CompletionVersions

open D11.Ch02.Completion
open D11.Ch04.AeCommonException

/-- Countably generated scalar targets admit versions in the original space. -/
theorem version_of_countablyGenerated {X : Type u} {Y : Type v}
    [m : MeasurableSpace X] [MeasurableSpace Y] [CountablyGenerated Y]
    (μ : Measure X) (f : X → Y)
    (hf : @Measurable X Y (completedSpace μ) _ f) :
    ∃ h : X → Y, Measurable h ∧ aeEq μ h f := by
  have hn : NullMeasurable f μ := hf
  have ha : AEMeasurable f μ := hn.aemeasurable
  exact ⟨ha.mk f, ha.measurable_mk,
    (aeEq_iff_native μ _ _).mpr ha.ae_eq_mk.symm⟩

theorem ereal_version : Specs.D11.Ch04.CompletionVersions.ereal_version := by
  intro X m μ f hf
  exact version_of_countablyGenerated μ f hf

theorem real_version : Specs.D11.Ch04.CompletionVersions.real_version := by
  intro X m μ f hf
  exact version_of_countablyGenerated μ f hf

theorem complex_version : Specs.D11.Ch04.CompletionVersions.complex_version := by
  intro X m μ f hf
  exact version_of_countablyGenerated μ f hf

theorem ereal_measurable_iff_bounds :
    Specs.D11.Ch04.CompletionVersions.ereal_measurable_iff_bounds := by
  classical
  intro X m μ f
  constructor
  · intro hf
    obtain ⟨h, hh, N, hN, heq⟩ := ereal_version μ f hf
    let f₀ : X → EReal := N.piecewise (fun _ => ⊥) h
    let f₁ : X → EReal := N.piecewise (fun _ => ⊤) h
    refine ⟨f₀, f₁, measurable_const.piecewise hN.1 hh,
      measurable_const.piecewise hN.1 hh, ?_, ?_, N, hN, ?_⟩
    · intro x
      by_cases hx : x ∈ N
      · simp [f₀, hx]
      · simpa [f₀, hx] using (heq x hx).le
    · intro x
      by_cases hx : x ∈ N
      · simp [f₁, hx]
      · simpa [f₁, hx] using (heq x hx).symm.le
    · intro x hx
      simp only [f₀, f₁, piecewise_eq_of_notMem _ _ _ hx]
  · rintro ⟨f₀, f₁, h₀, _h₁, h₀f, hf₁, N, hN, heq⟩
    have hff₀ : aeEq μ f f₀ := by
      refine ⟨N, hN, fun x hx => ?_⟩
      exact le_antisymm ((hf₁ x).trans_eq (heq x hx).symm) (h₀f x)
    exact h₀.eventuallyMeasurable_of_eventuallyEq ((aeEq_iff_native μ _ _).mp hff₀)

end D11.Ch04.CompletionVersions
