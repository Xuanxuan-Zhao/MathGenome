import MathGenome.Internal.Specs.D05.M15.DeterminantLine.CauchyBinet
import MathGenome.Internal.D05.M15.DeterminantLine.MinorCoefficients
import MathGenome.Internal.D05.M05.DetProduct

/-! Cauchy–Binet by composing exterior maps and extracting increasing-wedge
coefficients. Transpose and conjugate transpose then give the Lagrange and
Gram identities, with their distinct scalar conventions. -/

noncomputable section
namespace D05.M15.DeterminantLine.CauchyBinet

open scoped BigOperators ComplexConjugate
open Specs.D05.M15
open Specs.D05.M15.DeterminantLine.CauchyBinet
open Specs.D05.M04.MatrixOfMap

theorem cauchy_binet : Specs.D05.M15.DeterminantLine.CauchyBinet.cauchy_binet := by
  intro K _ m n r A B k I J
  classical
  rw [← MinorCoefficients.minor_coefficients (A * B) k I J]
  change ((Pi.basisFun K (Fin m)).exteriorPower k).repr
    (WedgeSign.powerMap_value k ((A * B).mulVecLin)
      (ExteriorBasis.increasingWedge (Pi.basisFun K (Fin r)) k J)) I = _
  rw [Matrix.mulVecLin_mul, D05.M15.WedgeSign.power_map_comp,
    LinearMap.comp_apply]
  have hB := MinorCoefficients.minor_expansion B k J
  change WedgeSign.powerMap_value k B.mulVecLin
    (ExteriorBasis.increasingWedge (Pi.basisFun K (Fin r)) k J) = _ at hB
  rw [hB]
  change ((Pi.basisFun K (Fin m)).exteriorPower k).coord I
    (WedgeSign.powerMap_value k A.mulVecLin _) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro S _
  have hA := MinorCoefficients.minor_coefficients A k I S
  change ((Pi.basisFun K (Fin m)).exteriorPower k).coord I
    (WedgeSign.powerMap_value k A.mulVecLin _) = _ at hA
  rw [hA, mul_comm]

/-- The full-size instance of Cauchy–Binet uses all rows and columns in their
original order. This helper avoids a choice of enumeration in the corollaries. -/
theorem det_rectangular_product {K : Type*} [Field K] {n k : ℕ}
    (A : Matrix (Fin k) (Fin n) K) (B : Matrix (Fin n) (Fin k) K) :
    D05.M05.determinant (A * B) =
      ∑ S : Set.powersetCard (Fin n) k,
        D05.M05.determinant (A.submatrix id (S.val.orderEmbOfFin S.prop)) *
        rowMinor B S := by
  classical
  let U : Set.powersetCard (Fin k) k := ⟨Finset.univ, by simp⟩
  have hU : (U.val.orderEmbOfFin U.prop : Fin k → Fin k) = id := by
    symm
    apply Finset.orderEmbOfFin_unique U.prop
    · intro x
      exact Finset.mem_univ x
    · exact strictMono_id
  simpa only [hU, Matrix.submatrix_id_id, rowMinor] using cauchy_binet A B k U U

theorem lagrange : Specs.D05.M15.DeterminantLine.CauchyBinet.lagrange := by
  intro K _ n k X Y
  rw [det_rectangular_product]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Matrix.transpose_submatrix, D05.M05.DetProduct.det_transpose]
  rfl

theorem hermitian_lagrange : Specs.D05.M15.DeterminantLine.CauchyBinet.hermitian_lagrange := by
  intro n k X Y
  rw [det_rectangular_product]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Matrix.conjTranspose_submatrix, D05.M05.DetDefinition.matrix_det_bridge,
    Matrix.det_conjTranspose]
  exact congrArg (fun z : ℂ => star z * rowMinor Y S)
    (D05.M05.DetDefinition.matrix_det_bridge
      (X.submatrix (S.val.orderEmbOfFin S.prop) id)).symm

theorem complex_gram : Specs.D05.M15.DeterminantLine.CauchyBinet.complex_gram := by
  intro n k X
  rw [hermitian_lagrange]
  apply Finset.sum_congr rfl
  intro S _
  simpa only [Complex.ofReal_pow] using Complex.conj_mul' (rowMinor X S)

theorem first_slot_gram_matrix :
    Specs.D05.M15.DeterminantLine.CauchyBinet.first_slot_gram_matrix := by
  intro n k X
  ext i j
  simp only [complexGram, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

theorem first_slot_gram : Specs.D05.M15.DeterminantLine.CauchyBinet.first_slot_gram := by
  intro n k X
  rw [first_slot_gram_matrix, D05.M05.DetProduct.det_transpose, complex_gram]

theorem real_gram : Specs.D05.M15.DeterminantLine.CauchyBinet.real_gram := by
  intro n k X
  simpa only [pow_two] using lagrange X X

private theorem no_subsets {n k : ℕ} (h : n < k) : IsEmpty (Set.powersetCard (Fin n) k) := by
  refine ⟨fun S => ?_⟩
  have hs : k ≤ n := by simpa [S.prop] using Finset.card_le_univ S.val
  exact Nat.not_le_of_gt h hs

theorem cauchy_binet_above_dimension :
    Specs.D05.M15.DeterminantLine.CauchyBinet.cauchy_binet_above_dimension := by
  intro K _ m n r A B k I J h
  classical
  haveI := no_subsets h
  constructor
  · rw [cauchy_binet]
    simp
  · simp

theorem lagrange_above_dimension :
    Specs.D05.M15.DeterminantLine.CauchyBinet.lagrange_above_dimension := by
  intro K _ n k X Y h
  classical
  haveI := no_subsets h
  constructor
  · rw [lagrange]
    simp
  · simp

theorem hermitian_above_dimension :
    Specs.D05.M15.DeterminantLine.CauchyBinet.hermitian_above_dimension := by
  intro n k X Y h
  classical
  haveI := no_subsets h
  constructor
  · rw [hermitian_lagrange]
    simp
  · simp

theorem cauchy_binet_degree_zero :
    Specs.D05.M15.DeterminantLine.CauchyBinet.cauchy_binet_degree_zero := by
  intro K _ m n r A B I J
  constructor
  · exact D05.M05.DetDefinition.empty_determinant _
  · rw [← cauchy_binet]
    exact D05.M05.DetDefinition.empty_determinant _

theorem lagrange_degree_zero : Specs.D05.M15.DeterminantLine.CauchyBinet.lagrange_degree_zero := by
  intro K _ n X Y
  constructor
  · exact D05.M05.DetDefinition.empty_determinant _
  · rw [← lagrange]
    exact D05.M05.DetDefinition.empty_determinant _

theorem hermitian_degree_zero : Specs.D05.M15.DeterminantLine.CauchyBinet.hermitian_degree_zero := by
  intro n X Y
  constructor
  · exact D05.M05.DetDefinition.empty_determinant _
  · rw [← hermitian_lagrange]
    exact D05.M05.DetDefinition.empty_determinant _

theorem first_slot_gram_boundaries :
    Specs.D05.M15.DeterminantLine.CauchyBinet.first_slot_gram_boundaries := by
  constructor
  · intro n k X h
    rw [first_slot_gram_matrix, D05.M05.DetProduct.det_transpose]
    exact (hermitian_above_dimension X X h).1
  · intro n X
    exact D05.M05.DetDefinition.empty_determinant _

end D05.M15.DeterminantLine.CauchyBinet
