import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

/-! Independent statements for paper.tex §1.4 (p207:W04).
The stopping time may be infinite. The minimum with each finite observation
time is finite, as in the shared definition `P207.stoppedProcess`.
-/

open MeasureTheory
open scoped MeasureTheory

universe u

namespace P207.StoppingPreservesSpec

def martingale_stoppedProcess : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ),
    IsMartingale X ℱ μ → IsDiscreteStoppingTime ℱ τ →
      IsMartingale (stoppedProcess X τ) ℱ μ

def submartingale_stoppedProcess : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ),
    IsSubmartingale X ℱ μ → IsDiscreteStoppingTime ℱ τ →
      IsSubmartingale (stoppedProcess X τ) ℱ μ

end P207.StoppingPreservesSpec
