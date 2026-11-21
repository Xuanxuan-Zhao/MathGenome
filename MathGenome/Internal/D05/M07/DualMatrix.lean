import MathGenome.Internal.Specs.D05.M07.DualMatrix
import MathGenome.Internal.D05.M04.MatrixOfMap
import MathGenome.Internal.D05.M07.DualBasis
import MathGenome.Internal.D05.M07.DualMap

/-! K05.07.dual_matrix: transpose matrices for algebraic dual maps. -/

namespace D05.M07.DualMatrix

/-- Precomposition followed by the coordinate functional extracts Aᵢⱼ. -/
theorem dual_evaluation_of_expansion :
    Specs.D05.M07.DualMatrix.dual_evaluation_of_expansion := by
  intro K V W _ _ _ _ _ n m b c T A h i j
  refine ⟨D05.M07.DualMap.dualMap_apply_apply T (c.coord i) (b j), ?_⟩
  exact D05.M07.DualBasis.coordinate_of_expansion c (fun k => A k j)
    (T (b j)) (h j) i

/-- Expand the pulled-back functional using its values on the original basis. -/
theorem dual_basis_expansion : Specs.D05.M07.DualMatrix.dual_basis_expansion := by
  intro K V W _ _ _ _ _ n m b c T A h i
  calc
    T.dualMap (c.coord i) =
        ∑ j, T.dualMap (c.coord i) (b j) • b.coord j :=
      D05.M07.DualBasis.functional_expansion b (T.dualMap (c.coord i))
    _ = ∑ j, A i j • b.coord j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(dual_evaluation_of_expansion b c T A h i j).1,
        (dual_evaluation_of_expansion b c T A h i j).2]

/-- Dual-basis coordinates of a functional are its evaluations on primal vectors. -/
theorem dual_matrix_entry : Specs.D05.M07.DualMatrix.dual_matrix_entry := by
  intro K V W _ _ _ _ _ n m b c T i j
  simp only [Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.toMatrix_apply,
    Module.Basis.dualBasis_repr, LinearMap.dualMap_apply,
    Module.Basis.dualBasis_apply]

theorem matrix_transpose : Specs.D05.M07.DualMatrix.matrix_transpose := by
  intro K V W _ _ _ _ _ n m b c T
  ext j i
  exact dual_matrix_entry b c T i j

theorem matrix_transpose_of_expansion :
    Specs.D05.M07.DualMatrix.matrix_transpose_of_expansion := by
  intro K V W _ _ _ _ _ n m b c T A h
  rw [matrix_transpose b c T,
    ← D05.M04.MatrixOfMap.unique_matrix_from_basis b c T A h]

end D05.M07.DualMatrix
