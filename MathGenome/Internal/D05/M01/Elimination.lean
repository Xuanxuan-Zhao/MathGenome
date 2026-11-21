import MathGenome.Internal.Specs.D05.M01.Elimination
import MathGenome.Internal.D05.M01.Elimination.Forward
import MathGenome.Internal.D05.M01.Elimination.Backward

/-! Gaussian and Gauss–Jordan elimination, K05.01.elimination.
The forward and backward procedures use the same elementary operations.
Their finite lists concatenate in chronological order, so the reduced form
is reached from the original matrix as well as from its echelon form.
-/
namespace D05.M01.Elimination

open RowOps
universe u
variable {K : Type u} [Field K] {m n : ℕ}

/-- The two upstream list executors have the same entrywise action. -/
theorem applyOperations_eq_applyOps (ops : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) : applyOperations ops A = applyOps ops A := rfl

theorem gaussian_gaussJordan : EliminationSpec.gaussian_gaussJordan := by
  intro K _ m n A
  obtain ⟨forward, B, ps, hforward, htrace, hbound, horder, hechelon⟩ :=
    Forward.forward_elimination A
  obtain ⟨backward, hreduced, hpivots⟩ :=
    Backward.exists_reduced_same_pivots B hechelon
  let R := applyOps backward B
  refine ⟨forward, backward, B, R, ps, hforward, hechelon,
    htrace, hbound, horder, rfl, ?_, ?_, ?_⟩
  · exact hreduced
  · exact hpivots
  · rw [applyOps_append, hforward]

theorem exists_echelon : EliminationSpec.exists_echelon := by
  intro K _ m n A
  obtain ⟨forward, _, B, _, _, hforward, hechelon, _⟩ := gaussian_gaussJordan A
  exact ⟨forward, hforward ▸ hechelon⟩

theorem exists_reduced : EliminationSpec.exists_reduced := by
  intro K _ m n A
  obtain ⟨forward, backward, _, R, _, _, _, _, _, _, _, hreduced, _, htotal⟩ :=
    gaussian_gaussJordan A
  exact ⟨forward ++ backward, htotal ▸ hreduced⟩

theorem zero_reduction : EliminationSpec.zero_reduction := by
  intro K _ m n
  exact ⟨rfl, Echelon.zero_forms⟩

theorem empty_rows_reduction : EliminationSpec.empty_rows_reduction := by
  intro K _ n A
  exact ⟨rfl, Echelon.empty_rows_forms A⟩

theorem empty_columns_reduction : EliminationSpec.empty_columns_reduction := by
  intro K _ m A
  exact ⟨rfl, Echelon.empty_columns_forms A⟩

end D05.M01.Elimination
