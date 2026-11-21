import MathGenome.Internal.Specs.D05.M14.QrCholesky.Qr
import MathGenome.Internal.D05.M12.GramSchmidt
import MathGenome.Internal.D05.M14.QrCholesky.TriangularUnitary

noncomputable section

namespace D05.M14.QrCholesky.Qr
open D05.QrCholesky
open scoped Matrix
variable {F : Type*} [RCLike F] {m n : ℕ}

theorem dimension_bound : Specs.D05.M14.QrCholesky.Qr.dimension_bound := by
  intro F _ m n A hA
  simpa using hA.fintype_card_le_finrank

theorem orthonormal_columns_iff : Specs.D05.M14.QrCholesky.Qr.orthonormal_columns_iff := by
  intro F _ m n Q
  have hc (i j : Fin n) : inner F (columns Q i) (columns Q j) =
      (Q.conjTranspose * Q) i j := inner_matrix_col_col Q Q i j
  constructor
  · intro h
    ext i j
    have he := h j i
    change inner F (columns Q i) (columns Q j) = _ at he
    rw [hc] at he
    simpa only [Matrix.one_apply, eq_comm] using he
  · intro h i j
    change inner F (columns Q j) (columns Q i) = _
    rw [hc, h]
    simp only [Matrix.one_apply, eq_comm]
    split_ifs <;> rfl

@[simp] theorem columns_gramSchmidtQ (A : Matrix (Fin m) (Fin n) F) :
    columns (gramSchmidtQ A) = D05.gramSchmidtVectors (F := F) (columns A) := by
  funext j
  exact WithLp.toLp_ofLp _ _

/-- Matrix multiplication is the corresponding linear combination of columns. -/
theorem columns_mul (Q : Matrix (Fin m) (Fin n) F)
    (R : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    columns (Q * R) j = ∑ i, R i j • columns Q i := by
  ext k
  simp [columns, Matrix.mul_apply, mul_comm]

/-- Restoring the positive residual norm inverts the normalization. -/
theorem residual_eq_norm_smul (A : Matrix (Fin m) (Fin n) F)
    (hA : FullColumnRank A) (j : Fin n) :
    D05.gramSchmidtResidual (F := F) (columns A) j =
      (‖D05.gramSchmidtResidual (F := F) (columns A) j‖ : F) •
        D05.gramSchmidtVectors (F := F) (columns A) j := by
  rw [(D05.M12.GramSchmidt.recurrence (columns A) j).2]
  have hn : (‖D05.gramSchmidtResidual (F := F) (columns A) j‖ : F) ≠ 0 := by
    exact_mod_cast (ne_of_gt (D05.M12.GramSchmidt.denominators_pos (columns A) hA j))
  simp only [RCLike.ofReal_inv, smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- The column equation is exactly the rearranged Gram–Schmidt recursion. -/
theorem gramSchmidt_column_expansion (A : Matrix (Fin m) (Fin n) F)
    (hA : FullColumnRank A) (j : Fin n) :
    columns A j = ∑ i, gramSchmidtR A i j •
      D05.gramSchmidtVectors (F := F) (columns A) i := by
  classical
  have hs : ∑ i, gramSchmidtR A i j • D05.gramSchmidtVectors (F := F) (columns A) i =
      (∑ i ∈ Finset.Iio j, D05.firstInner (F := F) (columns A j)
        (D05.gramSchmidtVectors (F := F) (columns A) i) •
          D05.gramSchmidtVectors (F := F) (columns A) i) +
      (‖D05.gramSchmidtResidual (F := F) (columns A) j‖ : F) •
        D05.gramSchmidtVectors (F := F) (columns A) j := by
    simp only [gramSchmidtR, ite_smul, zero_smul, Finset.sum_ite]
    rw [Finset.filter_gt_eq_Iio]
    congr 1
    simp [Finset.sum_filter]
  rw [hs, ← residual_eq_norm_smul A hA j,
    (D05.M12.GramSchmidt.recurrence (columns A) j).1]
  abel

theorem gram_schmidt_factorization :
    Specs.D05.M14.QrCholesky.Qr.gram_schmidt_factorization := by
  intro F _ m n A hA
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · apply Matrix.ext
    intro k j
    have he := gramSchmidt_column_expansion A hA j
    have hm := columns_mul (gramSchmidtQ A) (gramSchmidtR A) j
    rw [columns_gramSchmidtQ] at hm
    have hh := congrArg (fun v : EuclideanSpace F (Fin m) => v k) (he.trans hm.symm)
    exact hh
  · apply (orthonormal_columns_iff _).mp
    rw [columns_gramSchmidtQ]
    exact D05.M12.GramSchmidt.orthonormal (columns A) hA
  · intro i j hji
    change j < i at hji
    simp [gramSchmidtR, not_lt_of_ge hji.le, ne_of_gt hji]
  · intro j
    refine ⟨_, D05.M12.GramSchmidt.denominators_pos (columns A) hA j, ?_⟩
    simp [gramSchmidtR]
  · intro k hk
    rw [columns_gramSchmidtQ]
    exact D05.M12.GramSchmidt.initial_spans (columns A) hA k hk

/-- Right multiplication cannot enlarge the column span. -/
theorem column_span_mul_le (Q : Matrix (Fin m) (Fin n) F)
    (R : Matrix (Fin n) (Fin n) F) :
    Submodule.span F (Set.range (columns (Q * R))) ≤
      Submodule.span F (Set.range (columns Q)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [columns_mul]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩))

/-- Invertibility of R gives the reverse column-span containment. -/
theorem column_span_eq (A Q : Matrix (Fin m) (Fin n) F)
    (R : Matrix (Fin n) (Fin n) F) (he : A = Q * R) (hi : R * R⁻¹ = 1) :
    Submodule.span F (Set.range (columns Q)) =
      Submodule.span F (Set.range (columns A)) := by
  have hQ : Q = A * R⁻¹ := by rw [he, Matrix.mul_assoc, hi, Matrix.mul_one]
  exact le_antisymm (hQ ▸ column_span_mul_le A R⁻¹) (he ▸ column_span_mul_le Q R)

/-- Diagonal entries multiply for upper triangular factors. -/
theorem upper_triangular_mul_diag (B C : Matrix (Fin n) (Fin n) F)
    (hB : B.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (B * C) i i = B i i * C i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB h, zero_mul]
    · rw [hC h, mul_zero]
  · simp

/-- Nonzero positive diagonal gives the genuine two-sided triangular inverse. -/
theorem triangular_inverses (R : Matrix (Fin n) (Fin n) F)
    (hu : R.IsUpperTriangular) (hp : ∀ i, ∃ r : ℝ, 0 < r ∧ R i i = (r : F)) :
    IsUnit R ∧ R⁻¹.IsUpperTriangular ∧ R⁻¹ * R = 1 ∧ R * R⁻¹ = 1 := by
  apply D05.M14.QrCholesky.TriangularUnitary.nonzero_diagonal_inverse R hu
  intro i
  obtain ⟨r, hr, he⟩ := hp i
  rw [he]
  exact_mod_cast ne_of_gt hr

theorem common_column_transition :
    Specs.D05.M14.QrCholesky.Qr.common_column_transition := by
  intro F _ m n A Q Q' R R' h h'
  obtain ⟨he, hQ, hR, hp⟩ := h
  obtain ⟨he', hQ', hR', hp'⟩ := h'
  obtain ⟨_, hi, hiL, hiR⟩ := triangular_inverses R hR hp
  obtain ⟨_, hi', hiL', hiR'⟩ := triangular_inverses R' hR' hp'
  refine ⟨column_span_eq A Q R he hiR, column_span_eq A Q' R' he' hiR', ?_⟩
  dsimp only
  let C := Q.conjTranspose * Q'
  change Q' = Q * C ∧ C.conjTranspose * C = 1 ∧ R = C * R' ∧
    C.IsUpperTriangular ∧ ∀ i, ∃ r : ℝ, 0 < r ∧ C i i = (r : F)
  have hCR : R = C * R' := by
    calc
      R = Q.conjTranspose * A := by rw [he, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
      _ = C * R' := by rw [he', ← Matrix.mul_assoc]
  have hC : C = R * R'⁻¹ := by rw [hCR, Matrix.mul_assoc, hiR', Matrix.mul_one]
  have hQC : Q' = Q * C := by
    calc
      Q' = A * R'⁻¹ := by rw [he', Matrix.mul_assoc, hiR', Matrix.mul_one]
      _ = Q * C := by rw [he, Matrix.mul_assoc, ← hC]
  have hu : C.conjTranspose * C = 1 := by
    rw [hQC, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q.conjTranspose Q C, hQ, Matrix.one_mul] at hQ'
    exact hQ'
  have ht : C.IsUpperTriangular := by rw [hC]; exact hR.mul hi'
  refine ⟨hQC, hu, hCR, ht, ?_⟩
  intro i
  obtain ⟨r, hr, her⟩ := hp i
  obtain ⟨s, hs, hes⟩ := hp' i
  have hdiag : (r : F) = C i i * (s : F) := by
    rw [← her, hCR, upper_triangular_mul_diag C R' ht hR', hes]
  refine ⟨r / s, div_pos hr hs, ?_⟩
  rw [RCLike.ofReal_div]
  exact (eq_div_iff (by exact_mod_cast ne_of_gt hs)).mpr hdiag.symm

theorem uniqueness : Specs.D05.M14.QrCholesky.Qr.uniqueness := by
  intro F _ m n A Q Q' R R' h h'
  obtain ⟨_, _, hQC, hu, hR, ht, hp⟩ := common_column_transition A Q Q' R R' h h'
  have hC := D05.M14.QrCholesky.TriangularUnitary.positive_diagonal_unitary
    (Q.conjTranspose * Q') ht hu hp
  rw [hC, Matrix.mul_one] at hQC
  rw [hC, Matrix.one_mul] at hR
  exact ⟨hQC.symm, hR⟩

theorem exists_unique_reduced_qr :
    Specs.D05.M14.QrCholesky.Qr.exists_unique_reduced_qr := by
  intro F _ m n A hA
  refine ⟨(gramSchmidtQ A, gramSchmidtR A), (gram_schmidt_factorization A hA).1, ?_⟩
  rintro ⟨Q, R⟩ hp
  obtain ⟨hQ, hR⟩ := uniqueness A Q (gramSchmidtQ A) R (gramSchmidtR A) hp
    (gram_schmidt_factorization A hA).1
  exact Prod.ext hQ hR

theorem zero_columns : Specs.D05.M14.QrCholesky.Qr.zero_columns := by
  intro F _ m A
  have hA : FullColumnRank A := linearIndependent_empty_type
  refine ⟨hA, (gram_schmidt_factorization A hA).1, ?_⟩
  intro Q R
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end D05.M14.QrCholesky.Qr
