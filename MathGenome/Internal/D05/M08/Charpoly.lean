import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.D05.M05.DetProduct

/-! K05.08.charpoly: the basis-independent polynomial `det(xI - [T])`. -/

noncomputable section

namespace D05.M08.Charpoly

/-- The characteristic polynomial, identified below with the shared paper
determinant in every ordered basis. -/
def charpoly : Specs.D05.M08.Charpoly.charpoly_type :=
  Specs.D05.M08.Charpoly.charpoly_value

theorem matrix_det_formula : Specs.D05.M08.Charpoly.matrix_det_formula := by
  intro K _ n A
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  rfl

theorem determinant_formula : Specs.D05.M08.Charpoly.determinant_formula := by
  intro K V _ _ _ _ n b T
  rw [← matrix_det_formula]
  exact (LinearMap.charpoly_toMatrix T b).symm

theorem similarity_invariance : Specs.D05.M08.Charpoly.similarity_invariance := by
  intro K _ n A P hP
  rw [← matrix_det_formula, ← matrix_det_formula]
  obtain ⟨U, rfl⟩ := hP
  exact Matrix.charpoly_units_conj' U A

theorem basis_independence : Specs.D05.M08.Charpoly.basis_independence := by
  intro K V _ _ _ _ n m b c T
  rw [← determinant_formula b T, ← determinant_formula c T]

theorem monic : Specs.D05.M08.Charpoly.monic := by
  intro K V _ _ _ _ T
  exact LinearMap.charpoly_monic T

theorem natDegree : Specs.D05.M08.Charpoly.natDegree := by
  intro K V _ _ _ _ T
  exact LinearMap.charpoly_natDegree T

theorem degree : Specs.D05.M08.Charpoly.degree := by
  intro K V _ _ _ _ T
  rw [Polynomial.degree_eq_natDegree (monic T).ne_zero, natDegree T]

theorem empty_matrix : Specs.D05.M08.Charpoly.empty_matrix := by
  intro K _ A
  exact D05.M05.DetDefinition.empty_determinant _

theorem zero_dimensional : Specs.D05.M08.Charpoly.zero_dimensional := by
  intro K V _ _ _ _ T h
  exact Polynomial.eq_one_of_monic_natDegree_zero (monic T) ((natDegree T).trans h)

end D05.M08.Charpoly
