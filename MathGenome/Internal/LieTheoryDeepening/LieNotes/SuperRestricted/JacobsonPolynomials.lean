import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.JacobsonPolynomials

/-! The coefficient formula and universality of the Jacobson polynomials. -/

open scoped TensorProduct

namespace LieNotes.SuperRestricted.JacobsonPolynomials

open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
open _root_.Specs.LieNotes.SuperRestricted.JacobsonPolynomials
open Polynomial (X)

universe u v w

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]

/-- The individual Jacobson term `s_i(x,y)` for `1 ≤ i < p`. -/
def jacobsonTerm (k : Type u) [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    (p i : ℕ) (x y : G) : G :=
  (i : k)⁻¹ • jacobsonCoeffValue x y (p - 1) (i - 1)

private theorem polynomialCoeff_tmul (j : ℕ) (a : Polynomial k) (z : G) :
    polynomialCoeff j (a ⊗ₜ[k] z) = a.coeff j • z := by
  simp [polynomialCoeff]

private theorem polynomialCoeff_ad_step (x y : G) (z : Polynomial k ⊗[k] G) (j : ℕ) :
    polynomialCoeff j ⁅((X : Polynomial k) ⊗ₜ[k] x) + (1 ⊗ₜ[k] y), z⁆ =
      match j with
      | 0 => ⁅y, polynomialCoeff 0 z⁆
      | j + 1 => ⁅x, polynomialCoeff j z⁆ + ⁅y, polynomialCoeff (j + 1) z⁆ := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    cases j <;>
      simp [LieRing.add_lie, LieAlgebra.ExtendScalars.bracket_tmul,
        polynomialCoeff_tmul, Polynomial.coeff_X_mul, lie_smul]
  | add z w hz hw =>
    rw [LieRing.lie_add, map_add, hz, hw]
    cases j <;> simp [lie_add, add_add_add_comm]

/-- The bracket recurrence extracts the coefficients of the actual polynomial adjoint. -/
theorem coeff_adjointPolynomial : coeff_adjointPolynomialType.{u, v} := by
  intro k _ G _ _ x y n j
  induction n generalizing j with
  | zero =>
    cases j <;> simp [adjointPolynomial, polynomialCoeff_tmul, jacobsonCoeffValue, Polynomial.coeff_one]
  | succ n ih =>
    rw [adjointPolynomial, pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
    change polynomialCoeff j ⁅_, adjointPolynomial (k := k) x y n⁆ = _
    rw [polynomialCoeff_ad_step]
    cases j <;> simp [ih, jacobsonCoeffValue]

/-- Multiplication by `i` characterizes the term for each `1 ≤ i < p`. -/
theorem jacobsonTerm_spec {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (x y : G) {i : ℕ}
    (hi : 1 ≤ i) (hip : i < p) (s : G) :
    s = jacobsonTerm k p i x y ↔
      (i : k) • s = polynomialCoeff (i - 1) (adjointPolynomial (k := k) x y (p - 1)) := by
  have hcast : (i : k) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hi hip) ((CharP.cast_eq_zero_iff k p i).mp h)
  rw [coeff_adjointPolynomial, jacobsonTerm]
  constructor
  · rintro rfl
    rw [smul_smul, mul_inv_cancel₀ hcast, one_smul]
  · intro hs
    rw [← hs, smul_smul, inv_mul_cancel₀ hcast, one_smul]

private theorem map_jacobsonCoeff {H : Type w} [LieRing H] [LieAlgebra k H]
    (f : G →ₗ⁅k⁆ H) (x y : G) (n j : ℕ) :
    f (jacobsonCoeffValue x y n j) = jacobsonCoeffValue (f x) (f y) n j := by
  induction n generalizing j with
  | zero => cases j <;> simp [jacobsonCoeffValue]
  | succ n ih => cases j <;> simp [jacobsonCoeffValue, ih]

theorem jacobsonTerm_isLiePolynomial (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    (i : ℕ) (_hi : 1 ≤ i) (_hip : i < p) :
    ∃ P : FreeLieAlgebra k Bool,
      ∀ {G : Type v} [LieRing G] [LieAlgebra k G] (x y : G),
        FreeLieAlgebra.lift k (fun b : Bool => if b then y else x) P = jacobsonTerm k p i x y := by
  refine ⟨jacobsonTerm k p i (FreeLieAlgebra.of k false) (FreeLieAlgebra.of k true), ?_⟩
  intro G _ _ x y
  simp [jacobsonTerm, map_jacobsonCoeff, FreeLieAlgebra.lift_of_apply]

/-- The individual terms sum to the correction used in the restricted-power axioms. -/
theorem sum_jacobsonTerm (k : Type u) [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    (p : ℕ) (x y : G) :
    (∑ i ∈ Finset.Ico 1 p, jacobsonTerm k p i x y) = jacobsonCorrectionValue k p x y := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [jacobsonTerm, jacobsonCorrectionValue, Nat.add_comm 1, Nat.add_sub_cancel]

end LieNotes.SuperRestricted.JacobsonPolynomials
