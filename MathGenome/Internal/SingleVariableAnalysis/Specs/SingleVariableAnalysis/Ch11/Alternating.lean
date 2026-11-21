import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of K03.11.alternating (paper.tex:1045–1053)
and its conditional harmonic example in K03.11.absolute (1081–1088).

All sums mean ordinary convergence of inclusive ordered partial sums.
The remainder after N is S - (a₀ + ⋯ + a_N); its sign is expressed by
nonnegativity after multiplication by (-1)^(N+1), allowing a zero remainder.
The harmonic example is 1 - 1/2 + 1/3 - ⋯, with no zero denominator.
Failure of absolute convergence means that the ordered series of absolute
values has no finite sum; no unconditional summability predicate is used.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Alternating

open PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def alternatingSeriesConverges : Prop :=
  ∀ b : ℕ → ℝ, (∀ n, 0 ≤ b n) → (∀ n, b (n + 1) ≤ b n) →
    realSequenceConvergesValue b 0 →
      realSeriesConvergesValue (fun n => (-1 : ℝ) ^ n * b n)

def alternatingSeriesRemainder : Prop :=
  ∀ b : ℕ → ℝ, (∀ n, 0 ≤ b n) → (∀ n, b (n + 1) ≤ b n) →
    realSequenceConvergesValue b 0 → ∀ S : ℝ,
      realSeriesHasSumValue (fun n => (-1 : ℝ) ^ n * b n) S → ∀ N : ℕ,
        0 ≤ (-1 : ℝ) ^ (N + 1) *
          (S - realPartialSumValue (fun n => (-1 : ℝ) ^ n * b n) N) ∧
        |S - realPartialSumValue (fun n => (-1 : ℝ) ^ n * b n) N| ≤ b (N + 1)

def alternatingHarmonicConditional : Prop :=
  realSeriesConvergesValue (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1)) ∧
    ¬ realSeriesConvergesValue (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|)

end Specs.SingleVariableAnalysis.Ch11.Alternating
