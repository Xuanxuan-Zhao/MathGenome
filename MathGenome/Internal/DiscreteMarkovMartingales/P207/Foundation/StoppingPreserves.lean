import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.Stopping
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.StoppingPreserves
import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory
open scoped MeasureTheory

universe u

namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Stopping at an arbitrary, possibly infinite, stopping time preserves a
real submartingale for the original filtration. -/
theorem submartingale_stoppedProcess (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hX : IsSubmartingale X ℱ μ) (hτ : IsDiscreteStoppingTime ℱ τ) :
    IsSubmartingale (stoppedProcess X τ) ℱ μ := by
  exact (submartingale_iff_library μ ℱ _).mpr
    (((submartingale_iff_library μ ℱ X).mp hX).stoppedProcess hτ)

/-- Apply submartingale preservation to both `X` and `-X` to retain the
conditional equality. No finiteness or boundedness of the stopping time is needed. -/
theorem martingale_stoppedProcess (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hX : IsMartingale X ℱ μ) (hτ : IsDiscreteStoppingTime ℱ τ) :
    IsMartingale (stoppedProcess X τ) ℱ μ := by
  have h := (martingale_iff_library μ ℱ X).mp hX
  apply (martingale_iff_library μ ℱ _).mpr
  apply MeasureTheory.martingale_iff.mpr
  constructor
  · have hneg := (h.neg.submartingale.stoppedProcess hτ).neg
    have heq : -MeasureTheory.stoppedProcess (-X) τ = stoppedProcess X τ := by
      funext n ω
      exact neg_neg _
    rw [heq] at hneg
    exact hneg
  · exact h.submartingale.stoppedProcess hτ

end P207
