import MathGenome.Internal.Specs.D05.M05.Hadamard
import MathGenome.Internal.D05.M05.Hadamard.OrthogonalFactorization

/-! Hadamard's determinant inequality with both equality cases.
The QR determinant formula and Pythagorean residual bounds are supplied by the
upstream factorization. Equality of positive products forces equality of every
residual norm; the recurrence then removes every preceding projection. -/

noncomputable section
open scoped BigOperators

namespace D05.M05.Hadamard

open D05 InnerProductSpace

variable {F : Type*} [RCLike F] {n : ℕ}

/-- Dependence of Euclidean columns is the same algebraic dependence as for
plain coordinate functions, by the canonical linear equivalence. -/
theorem det_zero_of_dependent (v : Fin n → EuclideanSpace F (Fin n))
    (hv : ¬ LinearIndependent F v) : determinant (columnMatrix v) = 0 := by
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro h
  apply hv
  exact h.map' (WithLp.linearEquiv 2 F (Fin n → F)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 F (Fin n → F)).symm.injective)

section Residuals
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace F V]

/-- A residual cannot have greater norm than its original column. -/
theorem residual_norm_le (v : Fin n → V) (hv : LinearIndependent F v) (j : Fin n) :
    ‖gramSchmidtResidual (F := F) v j‖ ≤ ‖v j‖ := by
  have h := (OrthogonalFactorization.residual_ratio v hv j).2.1
  exact (div_le_one (norm_pos_iff.mpr (hv.ne_zero j))).mp h

/-- If every projection coefficient vanishes, each original vector is a
positive scalar multiple of its orthonormal Gram–Schmidt vector. -/
theorem orthogonal_of_coefficients_zero (v : Fin n → V) (hv : LinearIndependent F v)
    (hc : ∀ j i, i < j →
      firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i) = 0) :
    orthogonalFamily (F := F) v := by
  have hr (j : Fin n) : gramSchmidtResidual (F := F) v j = v j := by
    rw [gramSchmidtResidual]
    have hz : (∑ i ∈ Finset.Iio j,
        firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i) •
          gramSchmidtVectors (F := F) v i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hc j i (Finset.mem_Iio.mp hi), zero_smul]
    rw [hz, sub_zero]
  have hs (j : Fin n) : v j = (‖v j‖ : F) • gramSchmidtVectors (F := F) v j := by
    simpa only [hr] using OrthogonalFactorization.residual_eq_norm_smul v hv j
  have ho := (D05.M12.Orthonormal.orthonormal_iff_orthogonal_norm_one
    (gramSchmidtVectors (F := F) v)).mp (D05.M12.GramSchmidt.orthonormal v hv)
  intro j k hjk
  change inner F (v k) (v j) = 0
  rw [hs k, hs j, inner_smul_left, inner_smul_right]
  have hz : inner F (gramSchmidtVectors (F := F) v k)
      (gramSchmidtVectors (F := F) v j) = 0 := ho.1 j k hjk
  rw [hz, mul_zero, mul_zero]

/-- Gram–Schmidt fixes an orthogonal input before normalization. -/
theorem residual_eq_of_orthogonal (v : Fin n → V) (ho : orthogonalFamily (F := F) v)
    (j : Fin n) : gramSchmidtResidual (F := F) v j = v j := by
  rw [D05.M12.GramSchmidt.residual_eq_mathlib,
    gramSchmidt_of_orthogonal F ((D05.M12.Orthonormal.orthogonal_iff_pairwise v).mp ho)]

/-- The nonzero condition is needed only to make orthogonality imply independence. -/
theorem independent_of_orthogonal (v : Fin n → V) (ho : orthogonalFamily (F := F) v)
    (hne : ∀ j, v j ≠ 0) : LinearIndependent F v := by
  exact linearIndependent_of_ne_zero_of_inner_eq_zero hne
    ((D05.M12.Orthonormal.orthogonal_iff_pairwise v).mp ho)

end Residuals

theorem inequality : Specs.D05.M05.Hadamard.inequality := by
  intro F _ n v
  by_cases hv : LinearIndependent F v
  · rw [OrthogonalFactorization.det_columns_norm v hv]
    exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      (fun j _ => residual_norm_le v hv j)
  · rw [det_zero_of_dependent v hv, norm_zero]
    exact Finset.prod_nonneg (fun j _ => norm_nonneg _)

theorem dependent_strict : Specs.D05.M05.Hadamard.dependent_strict := by
  intro F _ n v hne hv
  rw [det_zero_of_dependent v hv, norm_zero]
  exact Finset.prod_pos (fun j _ => norm_pos_iff.mpr (hne j))

theorem equality_nonzero : Specs.D05.M05.Hadamard.equality_nonzero := by
  intro F _ n v hne
  constructor
  · intro he
    have hv : LinearIndependent F v := by
      by_contra hv
      exact (ne_of_lt (dependent_strict v hne hv)) he
    have hp : (∏ j, ‖gramSchmidtResidual (F := F) v j‖) = ∏ j, ‖v j‖ := by
      rw [← OrthogonalFactorization.det_columns_norm v hv]
      exact he
    have hr (j : Fin n) : ‖gramSchmidtResidual (F := F) v j‖ = ‖v j‖ := by
      by_contra h
      have hlt := Finset.prod_lt_prod₀
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
          D05.M12.GramSchmidt.denominators_pos v hv i)
        (fun i _ => residual_norm_le v hv i)
        ⟨j, Finset.mem_univ j, lt_of_le_of_ne (residual_norm_le v hv j) h⟩
      exact (ne_of_lt hlt) hp
    apply orthogonal_of_coefficients_zero v hv
    intro j
    apply (OrthogonalFactorization.residual_ratio v hv j).2.2.mp
    rw [hr, div_self (norm_ne_zero_iff.mpr (hne j))]
  · intro ho
    have hv := independent_of_orthogonal v ho hne
    rw [OrthogonalFactorization.det_columns_norm v hv]
    apply Finset.prod_congr rfl
    intro j _
    rw [residual_eq_of_orthogonal v ho j]

theorem zero_column : Specs.D05.M05.Hadamard.zero_column := by
  intro F _ n v j hj
  have hd : determinant (columnMatrix v) = 0 :=
    det_zero_of_dependent v (fun hv => hv.ne_zero j hj)
  have hp : (∏ k, ‖v k‖) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, norm_zero])
  exact ⟨hd, hp, by rw [hd, hp, norm_zero]⟩

theorem equality_iff : Specs.D05.M05.Hadamard.equality_iff := by
  intro F _ n v
  by_cases hz : ∃ j, v j = 0
  · obtain ⟨j, hj⟩ := hz
    exact iff_of_true (zero_column v j hj).2.2 (Or.inl ⟨j, hj⟩)
  · have hne : ∀ j, v j ≠ 0 := fun j hj => hz ⟨j, hj⟩
    rw [equality_nonzero v hne, or_iff_right hz]

theorem matrix_statement : Specs.D05.M05.Hadamard.matrix_statement := by
  intro F _ n A
  let v : Fin n → EuclideanSpace F (Fin n) := fun j => WithLp.toLp 2 (A.col j)
  have hm : columnMatrix v = A := rfl
  exact hm ▸ ⟨inequality v, equality_iff v⟩

theorem empty_case : Specs.D05.M05.Hadamard.empty_case := by
  intro F _ v
  have hd := D05.M05.DetDefinition.empty_determinant (columnMatrix v)
  exact ⟨hd, by simp, by rw [hd, norm_one]; simp⟩

end D05.M05.Hadamard
