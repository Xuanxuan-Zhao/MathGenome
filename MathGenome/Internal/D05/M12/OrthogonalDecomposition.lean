import MathGenome.Internal.Specs.D05.M12.OrthogonalDecomposition
import MathGenome.Internal.D05.M06.SumDimension
import MathGenome.Internal.D05.M12.OrthogonalComplement
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! K05.12.orthogonal_decomposition: decomposition along a finite-dimensional
subspace, with no finite-dimensionality or completeness assumption on the
ambient space. Finite-dimensional subspaces are complete, which supplies
Mathlib's orthogonal-projection hypothesis without adding a premise. -/

namespace D05.M12.OrthogonalDecomposition

theorem exists_unique_components :
    Specs.D05.M12.OrthogonalDecomposition.exists_unique_components := by
  intro F V _ _ _ U _ v
  let : CompleteSpace U := FiniteDimensional.complete F U
  exact Submodule.existsUnique_add_of_isCompl_prod U.isCompl_orthogonal v

theorem internal_direct_sum :
    Specs.D05.M12.OrthogonalDecomposition.internal_direct_sum := by
  intro F V _ _ _ U _
  let : CompleteSpace U := FiniteDimensional.complete F U
  apply (D05.M06.DirectSum.pair_internal_iff_sup_inf U U.orthogonal).mpr
  exact ⟨Submodule.sup_orthogonal_of_hasOrthogonalProjection,
    D05.M12.OrthogonalComplement.inf_orthogonal_eq_bot U⟩

/-- Apply the proved dimension theorem for the paper's internal direct sum. -/
theorem dimension_add : Specs.D05.M12.OrthogonalDecomposition.dimension_add := by
  intro F V _ _ _ _ U
  let S : Bool → Submodule F V := fun b => if b then U.orthogonal else U
  let : ∀ b, FiniteDimensional F (S b) := fun b => by
    cases b <;> dsimp [S] <;> infer_instance
  have hd := D05.M06.SumDimension.internal_dimension S (internal_direct_sum U)
  simpa [S, add_comm] using hd.symm

theorem dimension_orthogonal :
    Specs.D05.M12.OrthogonalDecomposition.dimension_orthogonal := by
  intro F V _ _ _ _ U
  rw [← dimension_add U, Nat.add_sub_cancel_left]

/-- Mathlib's double-complement lemma uses precisely the available projection
hypothesis; it does not require the ambient space to be complete. -/
theorem double_orthogonal_of_finiteDimensional_subspace :
    Specs.D05.M12.OrthogonalDecomposition.double_orthogonal_of_finiteDimensional_subspace := by
  intro F V _ _ _ U _
  let : CompleteSpace U := FiniteDimensional.complete F U
  exact U.orthogonal_orthogonal

theorem double_orthogonal : Specs.D05.M12.OrthogonalDecomposition.double_orthogonal := by
  intro F V _ _ _ _ U
  exact double_orthogonal_of_finiteDimensional_subspace U

end D05.M12.OrthogonalDecomposition
