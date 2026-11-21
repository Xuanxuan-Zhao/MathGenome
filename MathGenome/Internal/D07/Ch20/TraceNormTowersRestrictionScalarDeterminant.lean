import MathGenome.Internal.Specs.D07.Ch20.TraceNormTowersRestrictionScalarDeterminant
import Mathlib.RingTheory.Norm.Transitivity

/-! Restriction of scalars and determinants for every finite field extension.
The library theorem used below proves the determinant identity by the
commuting-block determinant theorem, without separability assumptions.
The product basis and its matrix are defined independently in the Spec. -/

universe u v w

namespace D07.Ch20.TraceNormTowersRestrictionScalarDeterminant

open Specs.D07.Ch20.TraceNormTowersRestrictionScalarDeterminant

/-- The product-basis matrix is precisely the block matrix in the paper. -/
theorem block_entries : BlockEntries.{u, v, w} := by
  intro K M _ _ _ _ r ι _ _ b A i j k l
  unfold restrictionMatrix
  rw [LinearMap.restrictScalars_toMatrix, LinearMap.toMatrix_toLin]
  rfl

/-- det_K R(A) = Nm_(M/K)(det_M A), for every size and every matrix. -/
theorem restriction_scalar_determinant : RestrictionScalarDeterminant.{u, v, w} := by
  intro K M _ _ _ _ r ι _ _ b A
  unfold restrictionMatrix
  rw [LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin]

end D07.Ch20.TraceNormTowersRestrictionScalarDeterminant
