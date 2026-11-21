import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Algebra.BigOperators.Intervals

/-!
Independent specification of K03.11.summation_parts (paper.tex:1053–1063).
The four obligations specialize the finite identities to the canonical real
and complex fields. There are no convergence or boundedness assumptions.

`Icc p q` means the inclusive sum from `p` through `q`; `Ico p q`
means the sum from `p` through `q - 1`, empty when `p = q`.
The prefix `∑ j ∈ range p, a j` is `A_(p-1)` for positive `p`
and is zero for `p = 0`, implementing the source convention `A_(-1) = 0`
without truncated natural-number subtraction.
-/

namespace Specs.SingleVariableAnalysis.Ch11.SummationParts

open scoped BigOperators

/-- The global partial-sum identity, with both endpoints included. -/
def globalFormula (K : Type) [CommRing K] : Prop :=
  ∀ (a b : ℕ → K) (p q : ℕ), p ≤ q →
    (∑ n ∈ Finset.Icc p q, a n * b n) =
      (∑ j ∈ Finset.range (q + 1), a j) * b q -
        (∑ j ∈ Finset.range p, a j) * b p +
      ∑ n ∈ Finset.Ico p q,
        (∑ j ∈ Finset.range (n + 1), a j) * (b n - b (n + 1))

/-- The tail-anchored identity, with `T n = ∑ j ∈ Icc p n, a j`. -/
def tailFormula (K : Type) [CommRing K] : Prop :=
  ∀ (a b : ℕ → K) (p q : ℕ), p ≤ q →
    (∑ n ∈ Finset.Icc p q, a n * b n) =
      (∑ j ∈ Finset.Icc p q, a j) * b q +
      ∑ n ∈ Finset.Ico p q,
        (∑ j ∈ Finset.Icc p n, a j) * (b n - b (n + 1))

def globalReal : Prop := globalFormula ℝ
def globalComplex : Prop := globalFormula ℂ
def tailReal : Prop := tailFormula ℝ
def tailComplex : Prop := tailFormula ℂ

end Specs.SingleVariableAnalysis.Ch11.SummationParts
