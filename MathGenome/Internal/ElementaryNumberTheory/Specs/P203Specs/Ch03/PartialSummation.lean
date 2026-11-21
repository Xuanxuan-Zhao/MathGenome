import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.RCLike.Basic

open Finset MeasureTheory

namespace P203.PartialSummation

/-- Positive-index partial sums, including for real cutoffs below one. -/
noncomputable def partialSum {R : Type*} [AddCommMonoid R] (c : ℕ → R) (t : ℝ) : R :=
  ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n

/-- Positive integer indices in the half-open real interval `(a,b]`. -/
noncomputable def intervalIndices (a b : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊b⌋₊).filter (fun n => a < (n : ℝ))

/-- C¹ data on the closed interval, with derivatives taken with respect to the real variable.
No condition is imposed on values outside the interval. -/
def C1Weight {K : Type*} [RCLike K] (w w' : ℝ → K) (a b : ℝ) : Prop :=
  ContinuousOn w (Set.Icc a b) ∧ ContinuousOn w' (Set.Icc a b) ∧
    ∀ t ∈ Set.Icc a b, HasDerivWithinAt w (w' t) (Set.Icc a b) t

end P203.PartialSummation

namespace P203Specs.PartialSummation
open P203.PartialSummation

def discreteType : Prop :=
  ∀ (R : Type*) [CommRing R] (c w : ℕ → R) (m N : ℕ), 1 ≤ m → m ≤ N →
    ∑ n ∈ Finset.Icc m N, c n * w n =
      (∑ n ∈ Finset.Icc 1 N, c n) * w N -
      (∑ n ∈ Finset.Icc 1 (m - 1), c n) * w m +
      ∑ n ∈ Finset.Ico m N, (∑ k ∈ Finset.Icc 1 n, c k) * (w n - w (n + 1))

def abelType : Prop :=
  ∀ (K : Type*) [RCLike K] (c : ℕ → K) (w w' : ℝ → K) (a b : ℝ),
    a ≤ b → C1Weight w w' a b →
    ∑ n ∈ intervalIndices a b, c n * w n =
      partialSum c b * w b - partialSum c a * w a -
        ∫ t in a..b, partialSum c t * w' t

end P203Specs.PartialSummation
