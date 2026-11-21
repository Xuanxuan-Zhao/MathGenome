import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import Mathlib.Algebra.BigOperators.Intervals

/-!
Independent specification of K03.11.necessary (paper.tex:987–996).
Series are the ordinary inclusive partial sums from PartialSums, allowing
conditional convergence. Both endpoints of a finite tail are included, and
p = q is permitted. The harmonic sequence is represented by 1 / (n : ℝ):
its zeroth term is explicitly zero (division by zero in ℝ), so its partial
sum through N is exactly the paper's sum from 1 through N. No positive
harmonic term is removed or changed. Dyadic blocks use a half-open natural
interval, precisely the indices 2^k through 2^(k+1)-1.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Necessary

open PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open scoped BigOperators

def realSeriesCauchyCriterion : Prop :=
  ∀ a : ℕ → ℝ, realSeriesConvergesValue a ↔
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ p,
      |∑ n ∈ Finset.Icc p q, a n| < ε

def complexSeriesCauchyCriterion : Prop :=
  ∀ a : ℕ → ℂ, complexSeriesConvergesValue a ↔
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ p,
      ‖∑ n ∈ Finset.Icc p q, a n‖ < ε

def realSeriesTermLimit : Prop :=
  ∀ a : ℕ → ℝ, realSeriesConvergesValue a → realSequenceConvergesValue a 0

def complexSeriesTermLimit : Prop :=
  ∀ a : ℕ → ℂ, complexSeriesConvergesValue a → complexSequenceConvergesValue a 0

def harmonicTermLimit : Prop :=
  realSequenceConvergesValue (fun n : ℕ => 1 / (n : ℝ)) 0

def harmonicDyadicBlock : Prop :=
  ∀ k : ℕ, (1 : ℝ) / 2 ≤
    ∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)), 1 / (n : ℝ)

def harmonicDyadicPartialSumLowerBound : Prop :=
  ∀ k : ℕ, (k : ℝ) / 2 ≤
    realPartialSumValue (fun n : ℕ => 1 / (n : ℝ)) (2 ^ k - 1)

def harmonicPartialSumsUnbounded : Prop :=
  ∀ B : ℝ, ∃ N : ℕ, B < realPartialSumValue (fun n : ℕ => 1 / (n : ℝ)) N

def harmonicDivergesToPosInfinity : Prop :=
  divergesToPosInfinityValue (realPartialSumValue (fun n : ℕ => 1 / (n : ℝ)))

def harmonicSeriesDiverges : Prop :=
  realSeriesDivergesValue (fun n : ℕ => 1 / (n : ℝ))

end Specs.SingleVariableAnalysis.Ch11.Necessary
