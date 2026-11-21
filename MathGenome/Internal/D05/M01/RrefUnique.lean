import MathGenome.Internal.Specs.D05.M01.RrefUnique
import MathGenome.Internal.D05.M01.Elimination
import MathGenome.Internal.D05.M01.RrefUnique.RowSpace

/-! Uniqueness and classification of reduced row-echelon forms.
Existence comes from actual elimination sequences, and uniqueness comes from
the intrinsic row-space result. Inverse sequences are constructed explicitly.
-/
namespace D05.M01.RrefUnique

universe u
open D05.M01.RowOps D05.M01.Elimination

/-- Reachability by a finite chronological list of elementary row operations. -/
abbrev RowEquivalent : RrefUniqueSpec.RowEquivalent_type.{u} :=
  RrefUniqueSpec.RowEquivalent_value

/-- The unique reduced matrix selected from its row-equivalence class. -/
noncomputable abbrev reducedForm : RrefUniqueSpec.reducedForm_type.{u} :=
  RrefUniqueSpec.reducedForm_value

variable {K : Type u} [Field K] {m n : ℕ}

/-- Execute the inverse operations in reverse chronological order. -/
lemma applyOps_reverse_inverse (ops : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) :
    applyOps (ops.reverse.map inverse) (applyOps ops A) = A := by
  induction ops generalizing A with
  | nil => rfl
  | cons op ops ih =>
    change applyOps ((op :: ops).reverse.map inverse) (applyOps ops (applyOp op A)) = A
    rw [List.reverse_cons, List.map_append, applyOps_append]
    rw [ih, List.map_singleton, applyOps_singleton, inverse_apply]

theorem rowEquivalent_refl (A : Matrix (Fin m) (Fin n) K) : RowEquivalent A A :=
  ⟨[], rfl⟩

theorem rowEquivalent_symm (A B : Matrix (Fin m) (Fin n) K)
    (h : RowEquivalent A B) : RowEquivalent B A := by
  obtain ⟨ops, rfl⟩ := h
  exact ⟨ops.reverse.map inverse, applyOps_reverse_inverse ops A⟩

theorem rowEquivalent_trans (A B C : Matrix (Fin m) (Fin n) K)
    (hAB : RowEquivalent A B) (hBC : RowEquivalent B C) : RowEquivalent A C := by
  obtain ⟨ops, hops⟩ := hAB
  obtain ⟨ops', hops'⟩ := hBC
  exact ⟨ops ++ ops', by rw [applyOps_append, hops, hops']⟩

lemma applyOps_rowSpace (ops : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) : RowSpace.rowSpace (applyOps ops A) = RowSpace.rowSpace A := by
  induction ops generalizing A with
  | nil => rfl
  | cons op ops ih =>
    change RowSpace.rowSpace (applyOps ops (applyOp op A)) = RowSpace.rowSpace A
    rw [ih, RowSpace.row_operation_preserves_rowSpace]

theorem rowEquivalent_rowSpace (A B : Matrix (Fin m) (Fin n) K)
    (h : RowEquivalent A B) : RowSpace.rowSpace A = RowSpace.rowSpace B := by
  obtain ⟨ops, rfl⟩ := h
  exact (applyOps_rowSpace ops A).symm

theorem reduced_eq_of_rowEquivalent (R S : Matrix (Fin m) (Fin n) K)
    (hR : R.IsReducedRowEchelon) (hS : S.IsReducedRowEchelon)
    (h : RowEquivalent R S) : R = S :=
  RowSpace.eq_of_rowSpace_eq R S hR hS (rowEquivalent_rowSpace R S h)

theorem exists_unique_reduced (A : Matrix (Fin m) (Fin n) K) :
    ∃! R, R.IsReducedRowEchelon ∧ RowEquivalent A R := by
  obtain ⟨ops, hred⟩ := Elimination.exists_reduced A
  refine ⟨applyOps ops A, ⟨hred, ops, rfl⟩, ?_⟩
  intro S hS
  exact reduced_eq_of_rowEquivalent S _ hS.1 hred
    (rowEquivalent_trans S A _ (rowEquivalent_symm A S hS.2) ⟨ops, rfl⟩)

theorem reducedForm_spec (A : Matrix (Fin m) (Fin n) K) :
    (reducedForm A).IsReducedRowEchelon ∧ RowEquivalent A (reducedForm A) :=
  Classical.epsilon_spec (exists_unique_reduced A).exists

theorem rowEquivalent_iff_reduced_eq (A B R S : Matrix (Fin m) (Fin n) K)
    (hR : R.IsReducedRowEchelon) (hS : S.IsReducedRowEchelon)
    (hAR : RowEquivalent A R) (hBS : RowEquivalent B S) :
    RowEquivalent A B ↔ R = S := by
  constructor
  · intro hAB
    exact reduced_eq_of_rowEquivalent R S hR hS
      (rowEquivalent_trans R B S
        (rowEquivalent_trans R A B (rowEquivalent_symm A R hAR) hAB) hBS)
  · intro hRS
    subst S
    exact rowEquivalent_trans A R B hAR (rowEquivalent_symm B R hBS)

theorem rowEquivalent_iff_reducedForm_eq (A B : Matrix (Fin m) (Fin n) K) :
    RowEquivalent A B ↔ reducedForm A = reducedForm B :=
  rowEquivalent_iff_reduced_eq A B _ _ (reducedForm_spec A).1 (reducedForm_spec B).1
    (reducedForm_spec A).2 (reducedForm_spec B).2

end D05.M01.RrefUnique
