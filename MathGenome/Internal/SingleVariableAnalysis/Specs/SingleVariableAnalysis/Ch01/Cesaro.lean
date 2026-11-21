import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Independent propositions for K03.01.cesaro and the alternating/natural
counterexamples in K03.01.counterexamples (paper.tex:311–320, 352–356).

As in the upstream sequence interface, Lean index `n` represents positive
index `n + 1`. Thus the average at index `n` contains exactly `n + 1`
terms, numbered `0` through `n` in Lean. The alternating sequence is
`(-1)^(n+1)`, and the natural sequence is `n+1`. Its even positive-index
subsequence uses Lean indices `2*n+1`, and its odd one uses `2*n`.
All limits below are finite scalar limits, except the separately stated
real divergence to positive infinity. These specifications assume no
conclusion or auxiliary convergence certificate.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Cesaro

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open scoped BigOperators

def realCesaro : Prop :=
  ∀ (a : ℕ → ℝ) (L : ℝ), realSequenceConvergesValue a L →
    realSequenceConvergesValue
      (fun n => ((n : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), a j) L

def complexCesaro : Prop :=
  ∀ (a : ℕ → ℂ) (L : ℂ), complexSequenceConvergesValue a L →
    complexSequenceConvergesValue
      (fun n => ((n : ℂ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), a j) L

def alternatingEvenSubsequence : Prop :=
  realSequenceConvergesValue (fun n : ℕ => (-1 : ℝ) ^ ((2 * n + 1) + 1)) 1

def alternatingOddSubsequence : Prop :=
  realSequenceConvergesValue (fun n : ℕ => (-1 : ℝ) ^ (2 * n + 1)) (-1)

def alternatingBounded : Prop :=
  ∀ n : ℕ, |(-1 : ℝ) ^ (n + 1)| ≤ 1

def alternatingPartialSumsBounded : Prop :=
  ∀ n : ℕ, |∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1)| ≤ 1

def alternatingNotConvergent : Prop :=
  ¬ ∃ L : ℝ, realSequenceConvergesValue (fun n => (-1 : ℝ) ^ (n + 1)) L

def alternatingCesaro : Prop :=
  realSequenceConvergesValue
    (fun n => ((n : ℝ) + 1)⁻¹ *
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1)) 0

def naturalDivergesToPosInfinity : Prop :=
  divergesToPosInfinityValue (fun n : ℕ => (n : ℝ) + 1)

def naturalNotConvergent : Prop :=
  ¬ ∃ L : ℝ, realSequenceConvergesValue (fun n : ℕ => (n : ℝ) + 1) L

end Specs.SingleVariableAnalysis.Ch01.Cesaro
