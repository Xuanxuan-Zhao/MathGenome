import MathGenome.Internal.Specs.D05.M15.TensorCoordinates.LeftRightInvariants
import MathGenome.Internal.D05.M15.TensorDualHom
import MathGenome.Internal.D05.M15.TensorCoordinates.TraceDeterminant
import MathGenome.Internal.D05.M07.DualMatrix

/-! Left/right multiplication corresponds to the tensor of the algebraic dual
of the right factor with the left factor. Transporting the tensor invariants
along the canonical equivalence proves the formulas, including dimension zero. -/
namespace D05.M15.TensorCoordinates.LeftRightInvariants

open scoped TensorProduct
open Specs.D05.M15.TensorCoordinates.LeftRightInvariants

abbrev leftRight := @Specs.D05.M15.TensorCoordinates.LeftRightInvariants.leftRight

theorem leftRight_apply : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.leftRight_apply := by
  intro K V _ _ _ A B X x
  rfl

theorem rank_one_action : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.rank_one_action := by
  intro K V _ _ _ A B φ v
  ext x
  exact A.map_smul (φ (B x)) v

theorem intertwining : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.intertwining := by
  intro K V _ _ _ A B
  apply TensorProduct.ext
  ext φ v x
  exact A.map_smul (φ (B x)) v

theorem conjugacy : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.conjugacy := by
  intro K V _ _ _ _ A B
  let E := dualTensorHomEquiv K V V
  ext X x
  have h := LinearMap.congr_fun (intertwining A B) (E.symm X)
  have h' : leftRight A B X = E (TensorProduct.map B.dualMap A (E.symm X)) := by
    simpa only [E, LinearMap.comp_apply, ← toLinearMap_dualTensorHomEquiv,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h
  exact congrArg (fun T : Module.End K V => T x) h'.symm

theorem trace_dual : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.trace_dual := by
  intro K V _ _ _ _ B
  exact LinearMap.trace_transpose' B

theorem det_dual : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.det_dual := by
  intro K V _ _ _ _ B
  exact LinearMap.det_dualMap B

/-- Reuse the upstream invariant formulas for the same canonical operator. -/
theorem trace_leftRight : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.trace_leftRight :=
  D05.M15.TensorCoordinates.trace_sandwich

theorem det_leftRight : Specs.D05.M15.TensorCoordinates.LeftRightInvariants.det_leftRight :=
  D05.M15.TensorCoordinates.det_sandwich

end D05.M15.TensorCoordinates.LeftRightInvariants
