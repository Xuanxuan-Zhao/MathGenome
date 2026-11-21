import MathGenome.Internal.Specs.D05.M12.GramSchmidt
import MathGenome.Internal.D05.M12.Orthonormal
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! Gram–Schmidt for finite indexed lists, retaining every initial span. -/

noncomputable section

namespace D05.M12.GramSchmidt

open D05 InnerProductSpace

abbrev vectors : Specs.D05.M12.GramSchmidt.family_type := @D05.gramSchmidtVectors
abbrev residual : Specs.D05.M12.GramSchmidt.family_type := @D05.gramSchmidtResidual

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]

/-- Projection onto a line can be computed using its normalized generator.
At a zero generator both sides vanish, so this identity also handles skipped terms. -/
theorem projection_eq_normalized (w x : V) :
    (F ∙ w).starProjection x =
      firstInner (F := F) x (normalizeVector (F := F) w) • normalizeVector (F := F) w := by
  rw [Submodule.starProjection_singleton]
  simp only [firstInner, normalizeVector, inner_smul_left, RCLike.conj_inv, RCLike.conj_ofReal,
    smul_smul, RCLike.ofReal_inv, RCLike.ofReal_pow, div_eq_mul_inv]
  congr 1
  ring

theorem normed_eq_normalize {n : ℕ} (v : Fin n → V) (j : Fin n) :
    gramSchmidtNormed F v j = normalizeVector (F := F) (gramSchmidt F v j) := by
  simp only [gramSchmidtNormed, normalizeVector, RCLike.ofReal_inv]

/-- The independent, normalized recursion agrees with Mathlib's projection
recursion. This bridge is valid even for dependent input, with zero terms totalized. -/
theorem vectors_eq_mathlib {n : ℕ} (v : Fin n → V) :
    gramSchmidtVectors (F := F) v = gramSchmidtNormed F v := by
  funext j
  induction j using (wellFounded_lt (α := Fin n)).induction with
  | h j ih =>
    rw [gramSchmidtVectors, normed_eq_normalize, gramSchmidt]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ih i (Finset.mem_Iio.mp i.2), normed_eq_normalize]
    exact (projection_eq_normalized (gramSchmidt F v i) (v j)).symm

/-- The unnormalized residuals agree too, not just the normalized directions. -/
theorem residual_eq_mathlib {n : ℕ} (v : Fin n → V) (j : Fin n) :
    gramSchmidtResidual (F := F) v j = gramSchmidt F v j := by
  rw [gramSchmidtResidual, gramSchmidt_def]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [vectors_eq_mathlib, normed_eq_normalize]
  exact (projection_eq_normalized (gramSchmidt F v i) (v j)).symm

theorem recurrence : Specs.D05.M12.GramSchmidt.recurrence := by
  intro F V _ _ _ n v j
  refine ⟨rfl, ?_⟩
  change gramSchmidtVectors (F := F) v j = normalizeVector (F := F) _
  rw [gramSchmidtResidual, ← Finset.sum_attach, Finset.attach_eq_univ,
    gramSchmidtVectors]

theorem residual_ne_zero : Specs.D05.M12.GramSchmidt.residual_ne_zero := by
  intro F V _ _ _ n v hv j
  rw [residual_eq_mathlib]
  exact gramSchmidt_ne_zero j hv

theorem denominators_pos : Specs.D05.M12.GramSchmidt.denominators_pos := by
  intro F V _ _ _ n v hv j
  exact norm_pos_iff.mpr (residual_ne_zero v hv j)

theorem orthonormal : Specs.D05.M12.GramSchmidt.orthonormal := by
  intro F V _ _ _ n v hv
  apply (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr
  rw [vectors_eq_mathlib]
  exact gramSchmidtNormed_orthonormal hv

/-- Span preservation does not itself require independence. -/
theorem initial_spans_all {n : ℕ} (v : Fin n → V) (k : ℕ) (hk : k ≤ n) :
    Submodule.span F (gramSchmidtVectors (F := F) v '' {i | i.val < k}) =
      Submodule.span F (v '' {i | i.val < k}) := by
  rw [vectors_eq_mathlib, span_gramSchmidtNormed]
  cases k with
  | zero => simp
  | succ k =>
    let c : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    have hs : {i : Fin n | i.val < k + 1} = Set.Iic c := by
      ext i
      exact Nat.lt_succ_iff
    rw [hs]
    exact span_gramSchmidt_Iic F v c

theorem initial_spans : Specs.D05.M12.GramSchmidt.initial_spans := by
  intro F V _ _ _ n v _ k hk
  exact initial_spans_all v k hk

theorem gram_schmidt : Specs.D05.M12.GramSchmidt.gram_schmidt := by
  intro F V _ _ _ n v hv
  exact ⟨denominators_pos v hv, orthonormal v hv, initial_spans v hv⟩

theorem omit_zero_residuals : Specs.D05.M12.GramSchmidt.omit_zero_residuals := by
  intro F V _ _ _ n v
  refine ⟨fun j => norm_pos_iff.mpr j.2, ?_, ?_⟩
  · have ho : orthogonalFamily (F := F)
        (fun j : {j // gramSchmidtResidual (F := F) v j ≠ 0} =>
          gramSchmidtResidual (F := F) v j) := by
      intro i j hij
      simp only [firstInner, residual_eq_mathlib]
      exact gramSchmidt_orthogonal F v (fun he => hij (Subtype.ext he.symm))
    have hn := D05.M12.Orthonormal.normalize_orthogonal _ ho (fun j => j.2)
    have he (j : Fin n) : normalizeVector (F := F)
        (gramSchmidtResidual (F := F) v j) = gramSchmidtVectors (F := F) v j :=
      (recurrence v j).2.symm
    simpa only [he] using hn
  · trans Submodule.span F (Set.range (gramSchmidtVectors (F := F) v))
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨j, rfl⟩
        exact Submodule.subset_span ⟨j.val, rfl⟩
      · apply Submodule.span_le.mpr
        rintro x ⟨j, rfl⟩
        by_cases hj : gramSchmidtResidual (F := F) v j = 0
        · rw [(recurrence v j).2, hj]
          simp
        · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    · rw [vectors_eq_mathlib, span_gramSchmidtNormed_range, span_gramSchmidt]

end D05.M12.GramSchmidt
