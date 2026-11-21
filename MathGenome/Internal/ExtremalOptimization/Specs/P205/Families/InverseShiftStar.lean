import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.Shifting
import Mathlib.Data.Finset.Powerset

namespace P205.Families.InverseShiftStar
open Finset Shifting

/-- All rank-`k` subsets containing the specified center. -/
def fullStar {n : ℕ} (k : ℕ) (c : Fin n) : Family n :=
  (univ.powersetCard k).filter (c ∈ ·)

namespace Expected
/-- Undoing one singleton compression in the strict EKR range. -/
def inverseShiftStar : Prop :=
  ∀ {n k : ℕ}, 1 ≤ k → 2 * k < n →
    ∀ (i j : Fin n), i < j → ∀ (F : Family n),
      (F : Set (Finset (Fin n))).Sized k →
      (F : Set (Finset (Fin n))).Intersecting →
      ∀ c : Fin n, shift i j F = fullStar k c →
        ∃ d : Fin n, F = fullStar k d
end Expected
end P205.Families.InverseShiftStar
