import MathGenome.Internal.Specs.D05.M05.OperatorDet.ExteriorBridge
import MathGenome.Internal.D05.M05.OperatorDet
import MathGenome.Internal.D05.M15.DeterminantLine

/-!
K05.05.operator_det, paper.tex:899–903: the exterior interpretation of
the determinant already constructed by the column Leibniz formula.

The upstream wedge expansion is proved using alternating-map extensionality
on basis tuples and the permutation-sign rule. The resulting matrix-action
theorem combines it with functoriality on elementary wedges. The full-map
theorem extends that computation using the independently proved top-wedge
basis. We reuse those proofs here to connect the two source entries.
-/

noncomputable section
namespace D05.M05.OperatorDet.ExteriorBridge

open Specs.D05.M15.DeterminantLine
open Specs.D05.M15.WedgeSign

theorem top_wedge_basis : Specs.D05.M05.OperatorDet.ExteriorBridge.top_wedge_basis :=
  D05.M15.DeterminantLine.top_wedge_basis

theorem basis_wedge_action : Specs.D05.M05.OperatorDet.ExteriorBridge.basis_wedge_action := by
  intro K V _ _ _ n b T
  exact D05.M15.DeterminantLine.matrix_action b T _
    (D05.M04.MatrixOfMap.basis_image b b T)

theorem leibniz_wedge_action :
    Specs.D05.M05.OperatorDet.ExteriorBridge.leibniz_wedge_action := by
  intro K V _ _ _ n b T
  exact basis_wedge_action b T

theorem top_power_in_basis : Specs.D05.M05.OperatorDet.ExteriorBridge.top_power_in_basis :=
  D05.M15.DeterminantLine.top_power_in_basis

theorem top_power_operator_det :
    Specs.D05.M05.OperatorDet.ExteriorBridge.top_power_operator_det :=
  D05.M15.DeterminantLine.top_power_operator_det

theorem zero_dimensional_bridge :
    Specs.D05.M05.OperatorDet.ExteriorBridge.zero_dimensional_bridge := by
  intro K V _ _ _ b T
  refine ⟨D05.M05.OperatorDet.detInBasis_empty b T,
    _root_.ExteriorAlgebra.ιMulti_zero_apply b, ?_⟩
  intro a
  rw [D05.M15.WedgeSign.power_map_zero, LinearEquiv.apply_symm_apply]

end D05.M05.OperatorDet.ExteriorBridge
