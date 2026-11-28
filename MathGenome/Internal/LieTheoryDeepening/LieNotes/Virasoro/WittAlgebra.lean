import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.WittAlgebra

/-! The complex Witt algebra as derivations of Laurent polynomials. -/

noncomputable section

open LaurentPolynomial

namespace LieNotes.Virasoro.Witt

local notation "A" => LaurentPolynomial ℂ

/-- The complex Lie algebra of derivations of the Laurent polynomial algebra. -/
abbrev W : Type := WittSpec.Witt

/-- Formal differentiation with respect to the Laurent variable. -/
def derivative : W := WittSpec.derivative

/-- The mode `L_m = -t^(m+1) ∂ₜ`. -/
def L (m : ℤ) : W := WittSpec.mode m

@[simp]
theorem derivative_T (i : ℤ) : derivative (T i) = (i : ℂ) • T (i - 1) :=
  WittSpec.derivative_T i

@[simp]
theorem L_apply_T (m i : ℤ) : L m (T i) = (-(i : ℂ)) • T (m + i) := by
  change (-(T (m + 1) : A)) • derivative (T i) = _
  rw [smul_eq_mul, neg_mul, derivative_T, mul_smul_comm, ← T_add, ← neg_smul]
  congr 2
  omega

@[simp]
theorem derivative_t : derivative (T 1) = 1 := by
  simp

@[simp]
theorem L_apply_t (m : ℤ) : L m (T 1) = -T (m + 1) := by
  simp

/-- A complex derivation is determined by its value on the Laurent variable. -/
theorem ext ⦃D E : W⦄ (h : D (T 1) = E (T 1)) : D = E := by
  have hinv (F : W) : F (T (-1)) = -(T (-1) : A) ^ 2 • F (T 1) := by
    simpa only [invOf_T] using F.leibniz_invOf (a := T 1)
  have hneg : D (T (-1)) = E (T (-1)) := by rw [hinv D, hinv E, h]
  apply Derivation.ext
  intro f
  induction f using LaurentPolynomial.induction_on with
  | h_C a => simp only [C_eq_algebraMap, Derivation.map_algebraMap]
  | h_add hp hq => simp only [map_add, hp, hq]
  | h_C_mul_T n a ih =>
    rw [T_add, ← mul_assoc]
    simp only [Derivation.leibniz, h, ih]
  | h_C_mul_T_Z n a ih =>
    rw [show -(n : ℤ) - 1 = -(n : ℤ) + (-1) by omega, T_add, ← mul_assoc]
    simp only [Derivation.leibniz, hneg, ih]

/-- Evaluation at the Laurent variable as a complex-linear map. -/
def evalT : W →ₗ[ℂ] A := WittSpec.evaluation

@[simp]
theorem evalT_apply (D : W) : evalT D = D (T 1) := rfl

theorem evalT_bijective : Function.Bijective evalT := by
  refine ⟨fun _ _ h => ext h, fun f => ⟨f • derivative, ?_⟩⟩
  simp [Derivation.smul_apply, smul_eq_mul]

/-- The value at `t` is the Laurent coefficient multiplying the formal derivative. -/
theorem apply_eq_mul_derivative (D : W) (f : A) : D f = D (T 1) * derivative f := by
  have h : D = D (T 1) • derivative := ext (by simp [Derivation.smul_apply, smul_eq_mul])
  exact Derivation.congr_fun h f

/-- The linear equivalence between derivations and their Laurent coefficients. -/
def evalTEquiv : W ≃ₗ[ℂ] A := LinearEquiv.ofBijective evalT evalT_bijective

@[simp]
theorem evalTEquiv_apply (D : W) : evalTEquiv D = D (T 1) := rfl

/-- The integer-indexed Witt basis, obtained from the signed and shifted Laurent monomials. -/
def basis : Module.Basis ℤ ℂ W :=
  ((AddMonoidAlgebra.basis ℤ ℂ).reindex (Equiv.subRight 1)).map
    ((LinearEquiv.neg ℂ : A ≃ₗ[ℂ] A).trans evalTEquiv.symm)

@[simp]
theorem basis_apply (m : ℤ) : basis m = L m := by
  apply evalTEquiv.injective
  rw [basis, Module.Basis.map_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.reindex_apply, AddMonoidAlgebra.basis_apply, LinearEquiv.neg_apply]
  exact (L_apply_t m).symm

theorem basis_repr_apply (D : W) (m : ℤ) :
    basis.repr D m = -((D (T 1)).coeff (m + 1)) := by
  change ((AddMonoidAlgebra.basis ℤ ℂ).reindex (Equiv.subRight 1)).repr
    (((LinearEquiv.neg ℂ : A ≃ₗ[ℂ] A).trans evalTEquiv.symm).symm D) m = _
  rw [Module.Basis.repr_reindex_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.symm_neg, LinearEquiv.neg_apply, evalTEquiv_apply]
  rfl

theorem exists_mode_basis : WittSpec.ModeBasis :=
  ⟨basis, basis_apply, basis_repr_apply⟩

theorem mode_expansion (D : W) :
    D = (D (T 1)).coeff.sum (fun j c => (-c) • L (j - 1)) := by
  apply evalT_bijective.injective
  rw [map_finsuppSum]
  simp only [map_smul, evalT_apply, L_apply_t, sub_add_cancel, neg_smul_neg]
  simpa only [LaurentPolynomial.T, AddMonoidAlgebra.smul_single', mul_one] using
    (AddMonoidAlgebra.sum_coeff_single (D (T 1))).symm

/-- The commutator of two modes, computed by evaluating at the Laurent variable. -/
theorem lie_L (m n : ℤ) : ⁅L m, L n⁆ = ((m : ℂ) - (n : ℂ)) • L (m + n) := by
  apply ext
  rw [Derivation.commutator_apply, L_apply_t, L_apply_t, map_neg, map_neg,
    L_apply_T, L_apply_T, Derivation.smul_apply, L_apply_t]
  have h₁ : m + (n + 1) = m + n + 1 := by omega
  have h₂ : n + (m + 1) = m + n + 1 := by omega
  rw [h₁, h₂, neg_smul, neg_smul, neg_neg, neg_neg, ← sub_smul, smul_neg, ← neg_smul]
  congr 1
  push_cast
  ring

end LieNotes.Virasoro.Witt
