import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The last coordinate is separated as the univariate polynomial variable.
`Fin (n + 1)` represents the source's positive number of variables; `i : Fin n`
labels its first n variables, with source label i + 1. -/
namespace P103.Ch06.MonicCoordinate.Specs

open MvPolynomial
universe u

/-- View the last variable as X and all preceding variables as coefficients. -/
noncomputable def lastVariableEquiv (k : Type u) [CommSemiring k] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] Polynomial (MvPolynomial (Fin n) k) :=
  (renameEquiv k (finRotate (n + 1))).trans (finSuccEquiv k n)

/-- Lemma 6.3, with the forward and inverse triangular substitutions explicit.
No infinitude or characteristic restriction is imposed on the field. -/
def makingPolynomialMonic : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) k),
    (∀ a : k, f ≠ C a) →
    ∃ (b : ℕ) (_ : 2 ≤ b)
      (σ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k)
      (c : k),
      c ≠ 0 ∧
      σ (X (Fin.last n)) = X (Fin.last n) ∧
      (∀ i : Fin n, σ (X i.castSucc) =
        X i.castSucc + X (Fin.last n) ^ (b ^ (i.val + 1))) ∧
      σ.symm (X (Fin.last n)) = X (Fin.last n) ∧
      (∀ i : Fin n, σ.symm (X i.castSucc) =
        X i.castSucc - X (Fin.last n) ^ (b ^ (i.val + 1))) ∧
      (lastVariableEquiv k n (c • σ f)).Monic ∧
      0 < (lastVariableEquiv k n (c • σ f)).natDegree

end P103.Ch06.MonicCoordinate.Specs
