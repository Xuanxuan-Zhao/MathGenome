import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent interface for the Euclidean part of paper.tex, Theorem 4.1.
`Fin m → ℝ` has its usual finite product topology, vector space, and Lebesgue measure.
No measurable-set assumption on a critical image is made: `volume` is evaluated as
an outer measure on every set. -/
open scoped ContDiff

namespace SmoothManifolds.Ch04

/-- The critical points in an open Euclidean domain, using the actual derivative. -/
def criticalSet {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) : Set (Fin m → ℝ) :=
  {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}

/-- The full smooth Euclidean Sard statement in source dimension `m`. -/
def EuclideanSardIn (m : ℕ) : Prop :=
  ∀ (n : ℕ) (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)),
    IsOpen U → ContDiffOn ℝ ∞ f U →
    MeasureTheory.volume (f '' criticalSet U f) = 0

namespace EuclideanSardSpecs

/-- All dimensions, including both zero-dimensional boundary cases. -/
def smoothSard : Prop := ∀ m : ℕ, EuclideanSardIn m

end EuclideanSardSpecs
end SmoothManifolds.Ch04
