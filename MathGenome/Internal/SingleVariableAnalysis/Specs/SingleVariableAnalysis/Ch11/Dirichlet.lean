import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import Mathlib.Algebra.BigOperators.Intervals

/-!
Independent specification of K03.11.dirichlet, paper.tex:1063–1073.
Monotonicity allows either direction. Terms start at zero and convergence
means a finite limit of the ordinary inclusive partial sums, so conditional
convergence is included. The finite bounds include p = 0 and p = q.
The real amplitude is cast into ℂ only when multiplying complex terms.
-/
namespace Specs.SingleVariableAnalysis.Ch11.Dirichlet
open PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open scoped BigOperators

def realDirichlet : Prop :=
  ∀ (a b : ℕ → ℝ),
    (∃ M : ℝ, ∀ n, |realPartialSumValue a n| ≤ M) →
    (Monotone b ∨ Antitone b) → realSequenceConvergesValue b 0 →
    realSeriesConvergesValue (fun n => a n * b n)

def complexDirichlet : Prop :=
  ∀ (a : ℕ → ℂ) (b : ℕ → ℝ),
    (∃ M : ℝ, ∀ n, ‖complexPartialSumValue a n‖ ≤ M) →
    (Monotone b ∨ Antitone b) → realSequenceConvergesValue b 0 →
    complexSeriesConvergesValue (fun n => a n * (b n : ℂ))

def realDirichletTailBound : Prop :=
  ∀ (a b : ℕ → ℝ) (M : ℝ),
    (∀ n, |realPartialSumValue a n| ≤ M) →
    (Monotone b ∨ Antitone b) → realSequenceConvergesValue b 0 →
    ∀ (p q : ℕ), p ≤ q →
      |∑ n ∈ Finset.Icc p q, a n * b n| ≤ 2 * M * |b p|

def complexDirichletTailBound : Prop :=
  ∀ (a : ℕ → ℂ) (b : ℕ → ℝ) (M : ℝ),
    (∀ n, ‖complexPartialSumValue a n‖ ≤ M) →
    (Monotone b ∨ Antitone b) → realSequenceConvergesValue b 0 →
    ∀ (p q : ℕ), p ≤ q →
      ‖∑ n ∈ Finset.Icc p q, a n * (b n : ℂ)‖ ≤ 2 * M * |b p|
end Specs.SingleVariableAnalysis.Ch11.Dirichlet
