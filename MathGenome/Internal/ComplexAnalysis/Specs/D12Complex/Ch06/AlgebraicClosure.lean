import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.Liouville
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.PolynomialMultiplicity
import Mathlib.Algebra.Polynomial.Roots

/-! Independent statements for paper.tex:1455–1473 (D12.06.02).
The multiset of n roots records repetitions without choosing an ordering.
Its count at every complex number is identified with both algebraic root
multiplicity and the canonical analytic order of the evaluation function.
Entire means weak holomorphy, with exactly the earlier Liouville hypotheses.
-/
noncomputable section
open Polynomial

namespace Specs.D12Complex.Ch06.AlgebraicClosure
open _root_.D12Complex

def bounded_entire_constant_type : Prop :=
  ∀ (f : ℂ → ℂ) (M : ℝ), HolomorphicOn Set.univ f →
    0 ≤ M → (∀ z : ℂ, ‖f z‖ ≤ M) →
    ∃ c : ℂ, ∀ z : ℂ, f z = c

/-- Nonconstant is stated algebraically, excluding every constant polynomial. -/
def polynomial_exists_root_type : Prop :=
  ∀ P : Polynomial ℂ, (¬ ∃ c : ℂ, P = C c) → ∃ a : ℂ, P.eval a = 0

/-- Exactly n roots counted with repetitions, with the leading coefficient
and both polynomial and pointwise factorizations. The count agreement holds
also at nonroots, where both multiplicities are zero. -/
def polynomial_factorization_type : Prop :=
  ∀ (P : Polynomial ℂ) (n : ℕ), P.natDegree = n → 1 ≤ n →
    ∃ A : Multiset ℂ, A.card = n ∧
      (∀ a ∈ A, P.eval a = 0) ∧
      P = C P.leadingCoeff * (A.map (fun a => X - C a)).prod ∧
      (∀ z : ℂ, P.eval z = P.leadingCoeff * (A.map (fun a => z - a)).prod) ∧
      (∀ a : ℂ, A.count a = P.rootMultiplicity a ∧
        Specs.D12Complex.Ch05.LocalZeroFactorization.order_value
          (fun z => P.eval z) a = (A.count a : ℕ∞))

end Specs.D12Complex.Ch06.AlgebraicClosure
