import MathGenome.Internal.Specs.D05.M11.Pfaffian.Square
import MathGenome.Internal.D05.M11.Pfaffian.Congruence
import MathGenome.Internal.D05.M11.Pfaffian.DirectSum
import MathGenome.Internal.D05.M11.SymplecticBlocks
import MathGenome.Internal.D05.M05.DetProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
namespace D05.M11.Pfaffian.Square
open scoped BigOperators
open Module
open Specs.D05.M11.Pfaffian
open Specs.D05.M11.SymplecticBlocks (J)
open Specs.D05.M11.Pfaffian.DirectSum (blockIndex blockMatrix)

lemma J_skew : ∀ i j, J ℝ i j = -J ℝ j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [J]

/-- The sign is fixed by the ordered dual wedge, rather than a square-root choice. -/
lemma pfaffian_J : pfaffian (m := 1) (J ℝ) = 1 := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  have ho : omega (m := 1) (J ℝ) = volume 1 := by
    simp [omega, omega_value, Fin.sum_univ_two, h0, h1, J,
      volume, volume_value, ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]
  have h := wedge_normalization 1 (J ℝ) J_skew
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, pow_one, one_smul] at h
  change omega (m := 1) (J ℝ) = pfaffian (m := 1) (J ℝ) • volume 1 at h
  rw [ho] at h
  exact (smul_left_injective ℝ (volume_ne_zero 1)) (by simpa using h.symm)

lemma det_J : Matrix.det (J ℝ) = 1 := by
  norm_num [J, Matrix.det_fin_two]

/-- A coordinate vector in the radical forces the top coefficient to vanish.
The singular projection deleting that coordinate preserves A, so covariance
annihilates its Pfaffian. -/
lemma pfaffian_eq_zero_of_zero_row {m : ℕ}
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (hA : ∀ i j, A i j = -A j i) (i : Fin (2*m))
    (hi : ∀ j, A i j = 0) : pfaffian A = 0 := by
  classical
  let P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
    Matrix.diagonal (fun j => if j = i then 0 else 1)
  have hcol (j) : A j i = 0 := by rw [hA j i, hi j, neg_zero]
  have hdet : P.det = 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have heq : P.transpose * A * P = A := by
    ext j k
    simp only [P, Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hj : j = i <;> by_cases hk : k = i <;> simp [hj, hk, hi, hcol]
  have h : pfaffian (P.transpose * A * P) = D05.M05.determinant P * pfaffian A :=
    Congruence.congruence m A P hA
  rw [heq, D05.M05.DetDefinition.matrix_det_bridge, hdet, zero_mul] at h
  exact h

/-- A positive-dimensional zero form has a coordinate radical. -/
lemma pfaffian_zero (m : ℕ) :
    pfaffian (m := m+1) (0 : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) ℝ) = 0 := by
  exact pfaffian_eq_zero_of_zero_row _ (by simp) 0 (by simp)

lemma toBilin_isAlt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = -A j i) : A.toBilin'.IsAlt := by
  apply (D05.M11.Alternating.alternating_iff_skew (by norm_num : (2 : ℝ) ≠ 0) _).mpr
  intro x y
  simp only [Matrix.toBilin'_apply, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA i j]
  ring

/-- Determinants of the paper's ordered direct sum. -/
lemma det_block {r s : ℕ}
    (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (B : Matrix (Fin (2*s)) (Fin (2*s)) ℝ) :
    Matrix.det (blockMatrix A B) = Matrix.det A * Matrix.det B := by
  classical
  rw [show blockMatrix A B =
    (Matrix.fromBlocks A 0 0 B).submatrix (blockIndex r s).symm (blockIndex r s).symm
    from rfl, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

/-- Ordered diagonal sum of m copies of the paper's J block. -/
def standardBlocks : (m : ℕ) → Matrix (Fin (2*m)) (Fin (2*m)) ℝ
  | 0 => 0
  | m+1 => blockMatrix (standardBlocks m) (J ℝ)

/-- Repeated ordered direct sums fix the normalization at every even size. -/
lemma pfaffian_standardBlocks (m : ℕ) : pfaffian (standardBlocks m) = 1 := by
  induction m with
  | zero => exact empty_pfaffian _
  | succ m ih =>
    rw [standardBlocks, DirectSum.pfaffian_block, ih, pfaffian_J, mul_one]

lemma det_standardBlocks (m : ℕ) : (standardBlocks m).det = 1 := by
  induction m with
  | zero =>
    rw [← D05.M05.DetDefinition.matrix_det_bridge]
    exact D05.M05.DetDefinition.empty_determinant _
  | succ m ih => rw [standardBlocks, det_block, ih, det_J, mul_one]

/-- Cancellation after an invertible congruence. -/
lemma square_of_congruence {m : ℕ}
    (A P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (hA : ∀ i j, A i j = -A j i) (hP : P.det ≠ 0)
    (h : pfaffian (P.transpose * A * P) ^ 2 = (P.transpose * A * P).det) :
    pfaffian A ^ 2 = A.det := by
  have hc : pfaffian (P.transpose * A * P) = D05.M05.determinant P * pfaffian A :=
    Congruence.congruence m A P hA
  rw [hc, D05.M05.DetDefinition.matrix_det_bridge,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_pow] at h
  apply mul_left_cancel₀ (pow_ne_zero 2 hP)
  calc
    P.det ^ 2 * pfaffian A ^ 2 = P.det * A.det * P.det := h
    _ = P.det ^ 2 * A.det := by ring

/-- Normal-form induction: remove a nondegenerate alternating plane until the
remaining form is zero. This is the splitting step used in `normal_coordinates`;
no nondegeneracy of the original form or of the complement is assumed. -/
lemma pfaffian_sq_det (m : ℕ) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (hA : ∀ i j, A i j = -A j i) : pfaffian A ^ 2 = A.det := by
  classical
  induction m with
  | zero =>
    rw [show pfaffian A = 1 from empty_pfaffian A,
      ← D05.M05.DetDefinition.matrix_det_bridge A, D05.M05.DetDefinition.empty_determinant A]
    norm_num
  | succ m ih =>
    by_cases hz : A = 0
    · subst A
      rw [pfaffian_zero, Matrix.det_zero]
      norm_num
    · let B := A.toBilin'
      have hB : B.IsAlt := toBilin_isAlt A hA
      obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
        by_contra h
        push Not at h
        exact hz (by ext i j; exact h i j)
      let u : Fin (2*(m+1)) → ℝ := Pi.single i 1
      let v : Fin (2*(m+1)) → ℝ := (A i j)⁻¹ • Pi.single j 1
      have huv : B u v = 1 := by
        simp [B, u, v, Matrix.toBilin'_single, hij]
      let W := D05.M11.SymplecticBlocks.pairComplement B u v
      let f := D05.M11.SymplecticBlocks.splitPair B hB u v huv
      have hd : Module.finrank ℝ W = 2*m := by
        have hdim := f.finrank_eq
        change Module.finrank ℝ ((ℝ × ℝ) × W) =
          Module.finrank ℝ (Fin (2*(m+1)) → ℝ) at hdim
        simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at hdim
        omega
      let c : Basis (Fin (2*m)) ℝ W :=
        (Module.finBasis ℝ W).reindex (finCongr hd)
      let g : (W × (ℝ × ℝ)) ≃ₗ[ℝ] (Fin (2*(m+1)) → ℝ) :=
        (LinearEquiv.prodComm ℝ W (ℝ × ℝ)).trans f
      let b : Basis (Fin (2*(m+1))) ℝ (Fin (2*(m+1)) → ℝ) :=
        (((c.prod (Basis.finTwoProd ℝ)).map g).reindex (blockIndex m 1))
      let C : Matrix (Fin (2*m)) (Fin (2*m)) ℝ := (B.restrict W).toMatrix c
      have hC : ∀ i j, C i j = -C j i := by
        intro i j
        simpa [C, LinearMap.BilinForm.toMatrix_apply] using
          (hB.neg_eq (c j : Fin (2*(m+1)) → ℝ) (c i)).symm
      have hb : B.toMatrix b = blockMatrix C (J ℝ) := by
        ext i j
        obtain ⟨i, rfl⟩ := (blockIndex m 1).surjective i
        obtain ⟨j, rfl⟩ := (blockIndex m 1).surjective j
        simp only [LinearMap.BilinForm.toMatrix_apply, b, Basis.reindex_apply,
          Equiv.symm_apply_apply, Basis.map_apply, blockMatrix]
        rw [show g = (LinearEquiv.prodComm ℝ W (ℝ × ℝ)).trans f from rfl]
        simp only [LinearEquiv.trans_apply]
        rw [D05.M11.SymplecticBlocks.splitPair_value]
        cases i with
        | inl i =>
          cases j with
          | inl j => simp [Basis.prod_apply, LinearEquiv.prodComm_apply, C]
          | inr j => simp [Basis.prod_apply, LinearEquiv.prodComm_apply]
        | inr i =>
          cases j with
          | inl j => simp [Basis.prod_apply, LinearEquiv.prodComm_apply]
          | inr j =>
            fin_cases i <;> fin_cases j <;>
              simp [Basis.prod_apply, LinearEquiv.prodComm_apply, Basis.finTwoProd, J]
      let P := LinearMap.toMatrix b (Pi.basisFun ℝ (Fin (2*(m+1)))) LinearMap.id
      have hP : P.det ≠ 0 := by
        apply isUnit_iff_ne_zero.mp
        apply (Matrix.isUnit_iff_isUnit_det P).mp
        exact D05.M04.ChangeBasis.conversion_isUnit (Pi.basisFun ℝ _) b
      have hcong : P.transpose * A * P = blockMatrix C (J ℝ) := by
        rw [← hb]
        have h := B.toMatrix_comp (Pi.basisFun ℝ _) b LinearMap.id LinearMap.id
        simpa [P, B, LinearMap.BilinForm.toMatrix_basisFun,
          LinearMap.BilinForm.toMatrix'_toBilin'] using h.symm
      apply square_of_congruence A P hA hP
      rw [hcong, DirectSum.pfaffian_block, pfaffian_J, mul_one,
        det_block, det_J, mul_one]
      exact ih C hC

/-- The original determinant convention agrees with the square of the
normalized matrix Pfaffian, also for singular and empty matrices. -/
theorem square : Specs.D05.M11.Pfaffian.Square.square := by
  intro m A hA
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  exact pfaffian_sq_det m A hA

end D05.M11.Pfaffian.Square
