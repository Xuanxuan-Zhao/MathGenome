import MathGenome.Internal.Specs.D05.M05.TriangularBlock
import MathGenome.Internal.D05.M05.DetDefinition
import Mathlib.LinearAlgebra.Matrix.Block

/-! Triangular and finite block-triangular determinants over commutative rings. -/

noncomputable section

open scoped BigOperators

namespace D05.M05.TriangularBlock

open D05.M05.DetDefinition

theorem upper_triangular : D05.Specs.TriangularBlock.upper_triangular := by
  intro R _ n A hA
  rw [matrix_det_bridge]
  exact Matrix.det_of_isUpperTriangular (fun i j hij => hA i j hij)

theorem lower_triangular : D05.Specs.TriangularBlock.lower_triangular := by
  intro R _ n A hA
  rw [matrix_det_bridge]
  exact Matrix.det_of_isLowerTriangular A (fun i j hij => hA i j hij)

theorem upper_block : D05.Specs.TriangularBlock.upper_block := by
  intro R _ r s B C D
  rw [matrix_det_bridge, matrix_det_bridge, matrix_det_bridge,
    Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem lower_block : D05.Specs.TriangularBlock.lower_block := by
  intro R _ r s B C D
  rw [matrix_det_bridge, matrix_det_bridge, matrix_det_bridge,
    Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

theorem finite_upper_blocks : D05.Specs.TriangularBlock.finite_upper_blocks := by
  intro R _ n k A b hA
  have h : A.BlockTriangular b := fun i j hij => hA i j hij
  rw [matrix_det_bridge, h.det_fintype]
  apply Finset.prod_congr rfl
  intro a _
  rw [matrix_det_bridge, Matrix.det_reindex_self]

theorem finite_lower_blocks : D05.Specs.TriangularBlock.finite_lower_blocks := by
  intro R _ n k A b hA
  have h : A.transpose.BlockTriangular b := fun i j hij => hA j i hij
  rw [matrix_det_bridge, ← Matrix.det_transpose, h.det_fintype]
  apply Finset.prod_congr rfl
  intro a _
  rw [matrix_det_bridge, Matrix.det_reindex_self]
  change (A.toSquareBlock b a).transpose.det = (A.toSquareBlock b a).det
  exact Matrix.det_transpose _

theorem empty_block : D05.Specs.TriangularBlock.empty_block := by
  intro R _ n k A b a ha
  rw [matrix_det_bridge, Matrix.det_reindex_self]
  have : IsEmpty {i // b i = a} := ⟨fun i => ha i.val i.property⟩
  exact Matrix.det_isEmpty

theorem empty_triangular : D05.Specs.TriangularBlock.empty_triangular := by
  intro R _ A
  exact ⟨D05.M05.DetDefinition.empty_determinant A, by simp⟩

end D05.M05.TriangularBlock
