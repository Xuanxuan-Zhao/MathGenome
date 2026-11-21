import MathGenome.Internal.Specs.D05.M11.PrincipalMinors.Leading
import MathGenome.Internal.D05.M11.Hermitian
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

noncomputable section
open Matrix
open scoped ComplexOrder
namespace D05.M11.PrincipalMinors.Leading
open Specs.D05.M11.PrincipalMinors.Leading

variable {K : Type*} [RCLike K]

-- A library bridge: the real-part convention agrees with the star order on
-- a Hermitian quadratic expression.
theorem positiveDefinite_iff_posDef {n : Type*} [Fintype n]
    (A : Matrix n n K) (hA : A.IsHermitian) :
    Specs.D05.M11.Definiteness.positiveDefinite_value
      (fun x y => star y ⬝ᵥ A *ᵥ x) ↔ A.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hA, fun x hx => ?_⟩
    apply RCLike.pos_iff.mpr
    refine ⟨h x hx, ?_⟩
    have hs : star (star x ⬝ᵥ A *ᵥ x) = star x ⬝ᵥ A *ᵥ x := by
      exact hA.star_dotProduct_mulVec_comm x x
    exact (RCLike.conj_eq_iff_im.mp hs)
  · rintro ⟨_, h⟩ x hx
    exact (RCLike.pos_iff.mp (h hx)).1

/-- One induction step, bordering a positive definite leading block by one row
and column. Determinant positivity forces the scalar Schur complement positive. -/
theorem posDef_of_leading_and_det {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (hM : M.IsHermitian)
    (hA : (leadingBlock M n (Nat.le_succ n)).PosDef) (hd : 0 < M.det) : M.PosDef := by
  let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  let N := M.submatrix e e
  let A := N.toBlocks₁₁
  let b := N.toBlocks₁₂
  let d := N.toBlocks₂₂
  have hN : N.IsHermitian := hM.submatrix e
  have hAN : A.PosDef := by
    convert hA using 1
    ext i j
    congr 1
  have hblocks : N = fromBlocks A b bᴴ d := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact (hN.apply (Sum.inr i) (Sum.inl j)).symm
      | inr j => rfl
  let : Invertible A := hAN.isUnit.invertible
  let S := d - bᴴ * A⁻¹ * b
  have hdet : N.det = A.det * S.det := by
    rw [hblocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hdN : 0 < N.det := by simpa [N, e, det_submatrix_equiv_self] using hd
  have hdS : 0 < S.det := by
    apply lt_of_mul_lt_mul_left (a := A.det)
    · simpa only [mul_zero, ← hdet] using hdN
    · exact hAN.det_pos.le
  have hS : S.PosSemidef := by
    have heq : S = diagonal (fun _ => S 0 0) := by
      ext i j
      fin_cases i; fin_cases j; simp
    rw [heq, posSemidef_diagonal_iff]
    intro i
    exact (by simpa only [det_fin_one] using hdS.le)
  have hpN : N.PosSemidef := by
    rw [hblocks]
    exact (Matrix.PosDef.fromBlocks₁₁ b d hAN).mpr hS
  have hpdN : N.PosDef :=
    hpN.posDef_iff_det_ne_zero.mpr (ne_of_gt hdN)
  simpa [N] using hpdN.submatrix e.symm.injective

theorem posDef_iff_leadingPositive {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : A.IsHermitian) : A.PosDef ↔ LeadingPositive A := by
  constructor
  · intro hp k hk _
    exact (RCLike.pos_iff.mp (hp.submatrix (Fin.castLE_injective hk)).det_pos).1
  · intro hp
    induction n with
    | zero =>
      have heq : A = 1 := Subsingleton.elim _ _
      rw [heq]
      exact Matrix.PosDef.one
    | succ n ih =>
      have htop : (leadingBlock A n (Nat.le_succ n)).PosDef := by
        apply ih
        · exact hA.submatrix _
        · intro k hk hkp
          have := hp k (hk.trans (Nat.le_succ n)) hkp
          simpa [leadingBlock, submatrix_submatrix, Function.comp_def] using this
      have hd : 0 < A.det := by
        apply RCLike.pos_iff.mpr
        refine ⟨?_, ?_⟩
        · simpa [leadingBlock] using hp (n+1) le_rfl (Nat.succ_pos n)
        · apply RCLike.conj_eq_iff_im.mp
          change star A.det = A.det
          rw [← det_conjTranspose, hA.eq]
      exact posDef_of_leading_and_det A hA htop hd

theorem strict_criterion : Specs.D05.M11.PrincipalMinors.Leading.strict_criterion := by
  intro K _ n A hA
  exact (positiveDefinite_iff_posDef A hA).trans (posDef_iff_leadingPositive A hA)

private def pivot (a : ℝ) : Matrix Unit Unit K := fun _ _ => (a : K)
private def row {n : ℕ} (r : Fin n → K) : Matrix Unit (Fin n) K := fun _ j => star (r j)

private theorem pivot_inverse (a : ℝ) :
    (pivot (K := K) a)⁻¹ = (fun _ _ => (a : K)⁻¹ : Matrix Unit Unit K) := by
  rw [inv_subsingleton]
  ext i j
  simp [pivot, diagonal, Subsingleton.elim i j, Ring.inverse_eq_inv]

private theorem row_adjoint {n : ℕ} (r : Fin n → K) :
    (row r)ᴴ = (fun i (_ : Unit) => r i : Matrix (Fin n) Unit K) := by
  ext i j
  simp [row, conjTranspose_apply]

private theorem schur_product {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K) :
    B - (row r)ᴴ * (pivot a)⁻¹ * row r = schur a r B := by
  rw [pivot_inverse, row_adjoint]
  ext i j
  change B i j - (∑ t : Unit, (∑ s : Unit, r i * (a : K)⁻¹) * star (r j)) =
    B i j - (a : K)⁻¹ * (r i * star (r j))
  simp
  ring

@[instance_reducible] private def invertiblePivot (a : ℝ) (ha : 0 < a) : Invertible (pivot (K := K) a) :=
  ((isUnit_iff_isUnit_det _).mpr (by
    have haK : (a : K) ≠ 0 := by exact_mod_cast ne_of_gt ha
    simpa [pivot, det_unique] using (isUnit_iff_ne_zero.mpr haK))).invertible

theorem completed_square : Specs.D05.M11.PrincipalMinors.Leading.completed_square := by
  intro K _ n a r B ha z y
  let := invertiblePivot (K := K) a ha
  have hP : (pivot (K := K) a).IsHermitian := by
    ext i j
    simp [pivot, conjTranspose_apply]
  have hs := schur_complement_eq₁₁ (row r) B (fun _ : Unit => z) y hP
  rw [← dotProduct_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec,
    schur_product] at hs
  have hb : fromBlocks (pivot a) (row r) (row r)ᴴ B = bordered a r B := by
    rw [row_adjoint]
    rfl
  rw [hb] at hs
  have hvec : ((pivot a)⁻¹ * row r : Matrix Unit (Fin n) K) *ᵥ y =
      (fun _ : Unit => (a : K)⁻¹ * (star r ⬝ᵥ y)) := by
    rw [pivot_inverse]
    ext i
    change (∑ j : Fin n, (∑ t : Unit, (a : K)⁻¹ * star (r j)) * y j) = _
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  rw [hs, hvec]
  congr 1
  simp [pivot, dotProduct, Matrix.mulVec]
  ring

theorem completed_square_norm : Specs.D05.M11.PrincipalMinors.Leading.completed_square_norm := by
  intro K _ n a r B ha z y
  rw [completed_square a r B ha z y]
  congr 2
  exact RCLike.conj_mul _

theorem real_strict_criterion : Specs.D05.M11.PrincipalMinors.Leading.real_strict_criterion := by
  intro n A hA
  have hH : A.IsHermitian := by simpa using hA
  simpa [Specs.D05.M11.Definiteness.positiveDefinite_value, LeadingPositive] using
    strict_criterion A hH

private theorem bordered_det {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K) (ha : 0 < a) :
    (bordered a r B).det = (a : K) * (schur a r B).det := by
  let := invertiblePivot (K := K) a ha
  have hb : bordered a r B = fromBlocks (pivot a) (row r) (row r)ᴴ B := by
    rw [row_adjoint]
    rfl
  rw [hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv, schur_product]
  simp [pivot, det_unique]

theorem schur_positive_definite :
    Specs.D05.M11.PrincipalMinors.Leading.schur_positive_definite := by
  intro K _ n a r B ha hB
  let := invertiblePivot (K := K) a ha
  have haK : 0 < (a : K) := RCLike.pos_iff.mpr ⟨by simpa using ha, by simp⟩
  have hP : (pivot (K := K) a).PosDef := by
    have heq : pivot (K := K) a = diagonal (fun _ => (a : K)) := by
      ext i j
      simp [pivot, diagonal, Subsingleton.elim i j]
    rw [heq, posDef_diagonal_iff]
    exact fun _ => haK
  have hb : bordered a r B = fromBlocks (pivot a) (row r) (row r)ᴴ B := by
    rw [row_adjoint]
    rfl
  have hH : (bordered a r B).IsHermitian := by
    rw [hb]
    exact Matrix.IsHermitian.fromBlocks hP.isHermitian rfl hB
  have hC : (schur a r B).IsHermitian := by
    rw [hb] at hH
    simpa only [schur_product] using
      (Matrix.IsHermitian.fromBlocks₁₁ (row r) B hP.isHermitian).mp hH
  rw [positiveDefinite_iff_posDef _ hH, positiveDefinite_iff_posDef _ hC]
  have hps : (bordered a r B).PosSemidef ↔ (schur a r B).PosSemidef := by
    rw [hb]
    simpa only [schur_product] using Matrix.PosDef.fromBlocks₁₁ (row r) B hP
  constructor
  · intro h
    apply (hps.mp h.posSemidef).posDef_iff_det_ne_zero.mpr
    intro hz
    have hd := h.det_pos.ne'
    rw [bordered_det a r B ha, hz, mul_zero] at hd
    exact hd rfl
  · intro h
    apply (hps.mpr h.posSemidef).posDef_iff_det_ne_zero.mpr
    rw [bordered_det a r B ha]
    exact mul_ne_zero haK.ne' h.det_pos.ne'

theorem leading_schur_determinant :
    Specs.D05.M11.PrincipalMinors.Leading.leading_schur_determinant := by
  intro K _ n a r B ha k h
  have heq : (bordered a r B).submatrix (Sum.map id (Fin.castLE h))
      (Sum.map id (Fin.castLE h)) =
      bordered a (fun i => r (Fin.castLE h i)) (leadingBlock B k h) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [heq, bordered_det a _ _ ha]
  congr 1

theorem principal_transpose : Specs.D05.M11.PrincipalMinors.Leading.principal_transpose := by
  intro K _ n k H s
  exact Matrix.det_transpose (H.submatrix s s)

theorem empty_positive_definite :
    Specs.D05.M11.PrincipalMinors.Leading.empty_positive_definite := by
  intro K _ A
  constructor
  · intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  · intro k hk hp
    omega

theorem form_criterion : Specs.D05.M11.PrincipalMinors.Leading.form_criterion := by
  intro K V _ _ _ n e B hB
  let H := Specs.D05.M11.Hermitian.formMatrix_value e B
  have hH : H.IsHermitian := (D05.M11.Hermitian.hermitian_iff_matrix e B).mp hB
  have hq (v : V) : B v v = star (e.equivFun v) ⬝ᵥ Hᵀ *ᵥ e.equivFun v :=
    D05.M11.Hermitian.quadratic_matrix_expression e B v
  have hb : Specs.D05.M11.Definiteness.positiveDefinite_value (fun x y => B x y) ↔
      Specs.D05.M11.Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ Hᵀ *ᵥ x) := by
    constructor
    · intro h x hx
      have hv : e.equivFun.symm x ≠ 0 := e.equivFun.symm.map_ne_zero_iff.mpr hx
      have hh := h _ hv
      change 0 < RCLike.re (B _ _) at hh
      rw [hq] at hh
      simpa only [LinearEquiv.apply_symm_apply] using hh
    · intro h v hv
      change 0 < RCLike.re (B v v)
      rw [hq]
      exact h _ (e.equivFun.map_ne_zero_iff.mpr hv)
  rw [hb, strict_criterion Hᵀ hH.transpose]
  change LeadingPositive Hᵀ ↔ LeadingPositive H
  unfold LeadingPositive leadingBlock
  simp only [← transpose_submatrix, det_transpose]

end D05.M11.PrincipalMinors.Leading
