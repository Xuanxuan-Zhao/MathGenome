import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent interfaces for the nonzero-derivative step of the Euclidean
Sard proof, paper.tex:1148–1152. All measures are outer measures on arbitrary
sets. Smoothness and derivatives are those of the ambient real vector spaces. -/

open scoped ContDiff

namespace SmoothManifolds.Ch04.SardNonzeroRank

/-- Sard's assertion in precisely one source dimension, for all target dimensions. -/
def SardIn (d : ℕ) : Prop :=
  ∀ (q : ℕ) (V : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → (Fin q → ℝ)),
    IsOpen V → ContDiffOn ℝ ∞ g V →
      MeasureTheory.volume
        (g '' {x | x ∈ V ∧ ¬Function.Surjective (fderiv ℝ g x)}) = 0

/-- Critical points whose actual first derivative is nonzero. -/
def offZeroCriticalSet {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) : Set (Fin m → ℝ) :=
  {x | x ∈ U ∧ ¬Function.Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0}

namespace Specs

/-- The full off-zero stratum; the only Sard assumption is in source `m - 1`. -/
def nonzeroRankStep : Prop :=
  ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (U : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → (Fin n → ℝ)),
    IsOpen U → ContDiffOn ℝ ∞ f U → SardIn (m - 1) →
      MeasureTheory.volume (f '' offZeroCriticalSet U f) = 0

end Specs
end SmoothManifolds.Ch04.SardNonzeroRank
