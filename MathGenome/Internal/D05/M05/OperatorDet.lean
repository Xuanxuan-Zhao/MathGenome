import MathGenome.Internal.Specs.D05.M05.OperatorDet
import MathGenome.Internal.D05.M04.ChangeBasis
import MathGenome.Internal.D05.M05.DetProduct

/-! Determinants of operators, K05.05.operator_det (paper.tex:896–899). -/

namespace D05.M05.OperatorDet

open Specs.D05.M04.MatrixOfMap Specs.D05.M04.ChangeBasis

noncomputable def detInBasis : Specs.D05.M05.OperatorDet.detInBasis_type :=
  Specs.D05.M05.OperatorDet.detInBasis_value

noncomputable def operatorDet : Specs.D05.M05.OperatorDet.operatorDet_type :=
  Specs.D05.M05.OperatorDet.operatorDet_value

theorem detInBasis_eq_linearMap_det :
    Specs.D05.M05.OperatorDet.detInBasis_eq_linearMap_det := by
  intro R V _ _ _ n b T
  change D05.M05.determinant (matrixOfMap_value b b T) = LinearMap.det T
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  exact LinearMap.det_toMatrix b T

theorem matrix_change_basis : Specs.D05.M05.OperatorDet.matrix_change_basis := by
  intro R V _ _ _ n b b' T
  exact D05.M04.ChangeBasis.change_basis b b' b b' T

theorem basis_independent : Specs.D05.M05.OperatorDet.basis_independent := by
  intro R V _ _ _ n m b b' T
  rw [detInBasis_eq_linearMap_det b', detInBasis_eq_linearMap_det b]

theorem detInBasis_comp : Specs.D05.M05.OperatorDet.detInBasis_comp := by
  intro R V _ _ _ n b S T
  change D05.M05.determinant (matrixOfMap_value b b (S.comp T)) =
    D05.M05.determinant (matrixOfMap_value b b S) *
      D05.M05.determinant (matrixOfMap_value b b T)
  rw [D05.M04.Composition.matrix_comp b b b S T]
  exact D05.M05.DetProduct.det_mul _ _

theorem operatorDet_eq_detInBasis : Specs.D05.M05.OperatorDet.operatorDet_eq_detInBasis := by
  intro K V _ _ _ _ n b T
  exact (detInBasis_eq_linearMap_det b T).symm

theorem operatorDet_comp : Specs.D05.M05.OperatorDet.operatorDet_comp := by
  intro K V _ _ _ _ S T
  let b := Module.finBasis K V
  rw [operatorDet_eq_detInBasis b, operatorDet_eq_detInBasis b,
    operatorDet_eq_detInBasis b]
  exact detInBasis_comp b S T

theorem operatorDet_id : Specs.D05.M05.OperatorDet.operatorDet_id := by
  intro K V _ _ _ _
  exact LinearMap.det_id

theorem detInBasis_empty : Specs.D05.M05.OperatorDet.detInBasis_empty := by
  intro R V _ _ _ b T
  exact D05.M05.DetDefinition.empty_determinant _

theorem operatorDet_zero_dim : Specs.D05.M05.OperatorDet.operatorDet_zero_dim := by
  intro K V _ _ _ _ h T
  exact LinearMap.det_eq_one_of_finrank_eq_zero h T

end D05.M05.OperatorDet
