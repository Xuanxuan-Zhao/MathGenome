import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
Independent specification of K03.11.condensation (paper.tex:1035–1047).
`a n` is the manuscript's term with positive index n; a 0 is unused and
unrestricted. Thus the original series is represented by `fun n => a (n+1)`
in the upstream zero-indexed ordinary-series predicate. The condensed series
starts at k = 0. All powers in arguments of a and interval endpoints are natural
powers; coefficients are real powers with natural exponent.

Besides convergence equivalence, retain the individual block bounds, their
finite cumulative bounds (the lower comparison is half the condensed sum
with its first term removed), and control of every intermediate partial sum.
No convergence or summability certificate is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Condensation

open scoped BigOperators
open PartialSums

/-- The source's two estimates on the half-open block [2^k, 2^(k+1)). -/
def dyadicBlockBounds : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 1 ≤ n → 0 ≤ a n) →
    AntitoneOn a (Set.Ici 1) → ∀ k : ℕ,
      (2 : ℝ)^k * a (2^(k+1)) ≤
        ∑ n ∈ Finset.Ico (2^k) (2^(k+1)), a n ∧
      (∑ n ∈ Finset.Ico (2^k) (2^(k+1)), a n) ≤
        (2 : ℝ)^k * a (2^k)

/-- Finite cumulative lower and upper comparisons, including K = 0. -/
def dyadicPartialSumBounds : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 1 ≤ n → 0 ≤ a n) →
    AntitoneOn a (Set.Ici 1) → ∀ K : ℕ,
      ((∑ k ∈ Finset.range (K+1), (2 : ℝ)^k * a (2^k)) - a 1) / 2 ≤
        ∑ n ∈ Finset.Ico 1 (2^K), a n ∧
      (∑ n ∈ Finset.Ico 1 (2^K), a n) ≤
        ∑ k ∈ Finset.range K, (2 : ℝ)^k * a (2^k)

/-- Nonnegativity controls all partial sums between dyadic endpoints. -/
def dyadicIntermediatePartialSumBound : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 1 ≤ n → 0 ≤ a n) →
    AntitoneOn a (Set.Ici 1) → ∀ (N K : ℕ), N ≤ 2^K →
      (∑ n ∈ Finset.Ico 1 N, a n) ≤
        ∑ k ∈ Finset.range K, (2 : ℝ)^k * a (2^k)

/-- Ordinary convergence of the positive-index series and its condensation. -/
def cauchyCondensation : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n, 1 ≤ n → 0 ≤ a n) →
    AntitoneOn a (Set.Ici 1) →
      (realSeriesConvergesValue (fun n => a (n+1)) ↔
        realSeriesConvergesValue (fun k => (2 : ℝ)^k * a (2^k)))

end Specs.SingleVariableAnalysis.Ch11.Condensation
