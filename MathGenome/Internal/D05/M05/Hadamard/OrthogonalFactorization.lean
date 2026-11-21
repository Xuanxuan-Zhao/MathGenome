import MathGenome.Internal.Specs.D05.M05.Hadamard.OrthogonalFactorization
import MathGenome.Internal.D05.M12.GramSchmidt
import MathGenome.Internal.D05.M12.NormLaws
import MathGenome.Internal.D05.M05.DetProduct
import MathGenome.Internal.D05.M05.TriangularBlock
import MathGenome.Internal.D05.M13.AdjointLaws
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators Matrix

namespace D05.M05.Hadamard.OrthogonalFactorization

open D05 InnerProductSpace
open D05.M05.Hadamard

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]

/-- Undo the normalization using the strictly positive residual norm. -/
theorem residual_eq_norm_smul {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent F v) (j : Fin n) :
    gramSchmidtResidual (F := F) v j =
      (‖gramSchmidtResidual (F := F) v j‖ : F) • gramSchmidtVectors (F := F) v j := by
  rw [(D05.M12.GramSchmidt.recurrence v j).2, smul_smul,
    ← RCLike.ofReal_mul, mul_inv_cancel₀
      (ne_of_gt (D05.M12.GramSchmidt.denominators_pos v hv j))]
  simp

theorem norm_decomposition : Specs.D05.M05.Hadamard.OrthogonalFactorization.norm_decomposition := by
  intro F V _ _ _ n v hv j
  exact D05.M12.FourierParseval.bessel_identity
    (gramSchmidtVectors (F := F) v) (D05.M12.GramSchmidt.orthonormal v hv)
    (Finset.Iio j) (v j)

/-- Orthonormal columns give the conjugate-transpose identity entry by entry. -/
theorem q_conjTranspose_mul {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n))
    (hv : LinearIndependent F v) : (qFactor v)ᴴ * qFactor v = 1 := by
  have hq : Orthonormal F (gramSchmidtVectors (F := F) v) :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mp
      (D05.M12.GramSchmidt.orthonormal v hv)
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, qFactor, columnMatrix,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm, Matrix.one_apply] using
    (orthonormal_iff_ite.mp hq i j)

theorem r_below {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n))
    (i j : Fin n) (h : j < i) : rFactor v i j = 0 := by
  simp [rFactor, not_lt_of_gt h, ne_of_gt h]

theorem r_diagonal {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)) (j : Fin n) :
    rFactor v j j = (‖gramSchmidtResidual (F := F) v j‖ : F) := by
  simp [rFactor]

theorem qr_mul {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n))
    (hv : LinearIndependent F v) : columnMatrix v = qFactor v * rFactor v := by
  have hs (j : Fin n) :
      (∑ i, rFactor v i j • gramSchmidtVectors (F := F) v i) = v j := by
    simp only [rFactor, ite_smul, zero_smul, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    have hd : (Finset.univ.filter (fun i : Fin n => ¬i < j)).filter (fun i => i = j) =
        {j} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact And.right
      · intro h
        subst i
        simp
    rw [hd, Finset.sum_singleton]
    have hf : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by
      ext i
      simp
    rw [hf, ← residual_eq_norm_smul v hv j, gramSchmidtResidual]
    exact add_sub_cancel _ _
  ext i j
  have h := congrArg (fun x : EuclideanSpace F (Fin n) => x i) (hs j)
  simpa [Matrix.mul_apply, qFactor, columnMatrix, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, mul_comm] using h.symm

theorem qr_factorization : Specs.D05.M05.Hadamard.OrthogonalFactorization.qr_factorization := by
  intro F _ n v hv
  refine ⟨qr_mul v hv, q_conjTranspose_mul v hv,
    mul_eq_one_comm.mp (q_conjTranspose_mul v hv), r_below v, ?_⟩
  intro j
  exact ⟨r_diagonal v j, D05.M12.GramSchmidt.denominators_pos v hv j⟩

/-- Determinant multiplicativity and conjugation suffice; no QR uniqueness or
spectral theorem is involved. -/
theorem norm_det_of_conjTranspose_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) F)
    (hQ : Qᴴ * Q = 1) : ‖Q.det‖ = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => ‖M.det‖) hQ
  rw [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star,
    Matrix.det_one, norm_one] at h
  nlinarith [norm_nonneg Q.det]

theorem det_q_norm : Specs.D05.M05.Hadamard.OrthogonalFactorization.det_q_norm := by
  intro F _ n v hv
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  exact norm_det_of_conjTranspose_mul _ (q_conjTranspose_mul v hv)

theorem det_columns_norm : Specs.D05.M05.Hadamard.OrthogonalFactorization.det_columns_norm := by
  intro F _ n v hv
  have hq := det_q_norm v hv
  rw [D05.M05.DetDefinition.matrix_det_bridge] at hq
  rw [D05.M05.DetDefinition.matrix_det_bridge, qr_mul v hv,
    Matrix.det_mul, norm_mul, hq, one_mul,
    Matrix.det_of_isUpperTriangular (r_below v)]
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [r_diagonal, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

theorem residual_ratio : Specs.D05.M05.Hadamard.OrthogonalFactorization.residual_ratio := by
  intro F V _ _ _ n v hv j
  have hp := norm_decomposition v hv j
  have hu := D05.M12.GramSchmidt.denominators_pos v hv j
  have hcol : 0 < ‖v j‖ := norm_pos_iff.mpr (hv.ne_zero j)
  have hs : 0 ≤ ∑ i ∈ Finset.Iio j,
      ‖firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hle : ‖gramSchmidtResidual (F := F) v j‖ ≤ ‖v j‖ := by nlinarith
  refine ⟨div_pos hu hcol, (div_le_one hcol).mpr hle, ?_⟩
  constructor
  · intro he
    have heq := (div_eq_one_iff_eq (ne_of_gt hcol)).mp he
    have hz : (∑ i ∈ Finset.Iio j,
        ‖firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i)‖ ^ 2) = 0 := by
      nlinarith
    intro i hi
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.Iio j) => sq_nonneg
        ‖firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v k)‖)).mp hz
        i (Finset.mem_Iio.mpr hi)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ht)
  · intro hc
    have hz : (∑ i ∈ Finset.Iio j,
        ‖firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i)‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hc i (Finset.mem_Iio.mp hi), norm_zero, zero_pow (by decide)]
    have heq : ‖gramSchmidtResidual (F := F) v j‖ = ‖v j‖ := by nlinarith
    rw [heq, div_self (ne_of_gt hcol)]

theorem empty_case : Specs.D05.M05.Hadamard.OrthogonalFactorization.empty_case := by
  intro F _ v
  exact ⟨D05.M05.DetDefinition.empty_determinant _,
    D05.M05.DetDefinition.empty_determinant _,
    D05.M05.DetDefinition.empty_determinant _, by simp⟩

end D05.M05.Hadamard.OrthogonalFactorization
