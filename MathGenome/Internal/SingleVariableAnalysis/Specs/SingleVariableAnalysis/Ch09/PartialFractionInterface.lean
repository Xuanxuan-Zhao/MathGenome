import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators

/-!
The real rational identity in K03.09.partial_fractions (paper.tex:2662–2675).
A common finite index set is filtered by factor degree to write the two sums.
The index `k : Fin (e i)` represents the positive pole order `k.val + 1`.
No factorization or decomposition is assumed: both are existential conclusions.
-/
namespace Specs.SingleVariableAnalysis.Ch09.PartialFractionInterface

open Polynomial
open scoped BigOperators

/-- The full algebraic bridge, including normalization and the pointwise domain.
For a linear factor the root is `-(p i).coeff 0`; for a quadratic the two
coefficients are `(p i).coeff 1` and `(p i).coeff 0`.  Empty index sets cover
nonzero constant denominators, and there is no properness assumption on `P`. -/
def RealPartialFractions : Prop :=
  ∀ P Q : ℝ[X], Q ≠ 0 →
    ∃ (n : ℕ) (p : Fin n → ℝ[X]) (e : Fin n → ℕ) (A : ℝ[X])
      (a b c : (i : Fin n) → Fin (e i) → ℝ),
      (∀ i, (p i).Monic) ∧
      (∀ i, Irreducible (p i)) ∧
      Function.Injective p ∧
      (∀ i, 0 < e i) ∧
      Q = C Q.leadingCoeff * ∏ i, p i ^ e i ∧
      (∀ i,
        ((p i).natDegree = 1 ∧ p i = X - C (-(p i).coeff 0)) ∨
        ((p i).natDegree = 2 ∧
          p i = X ^ 2 + C ((p i).coeff 1) * X + C ((p i).coeff 0) ∧
          (p i).coeff 1 ^ 2 - 4 * (p i).coeff 0 < 0)) ∧
      ∀ x : ℝ, Q.eval x ≠ 0 →
        P.eval x / Q.eval x = A.eval x +
          (∑ i ∈ Finset.univ.filter (fun i => (p i).natDegree = 1),
            ∑ k : Fin (e i), a i k / (x - (-(p i).coeff 0)) ^ (k.val + 1)) +
          (∑ i ∈ Finset.univ.filter (fun i => (p i).natDegree = 2),
            ∑ k : Fin (e i),
              (b i k * x + c i k) /
                (x ^ 2 + (p i).coeff 1 * x + (p i).coeff 0) ^ (k.val + 1))

end Specs.SingleVariableAnalysis.Ch09.PartialFractionInterface
