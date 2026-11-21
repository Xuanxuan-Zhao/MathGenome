import MathGenome.Internal.Specs.D05.M15.DeterminantLine.MinorCoefficients
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M05.DetDefinition
import MathGenome.Internal.D05.M04.MatrixOfMap

/-! The coefficient of an increasing wedge in an induced exterior map is the
corresponding ordered minor, in every characteristic and every degree. -/

noncomputable section
namespace D05.M15.DeterminantLine.MinorCoefficients

open scoped BigOperators
open Specs.D05.M15

theorem based_minor_coefficients :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.based_minor_coefficients := by
  intro K V W _ _ _ _ _ n m b c f k I J
  rw [ExteriorBasis.increasingWedge, D05.M15.WedgeSign.power_map_elementary,
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    D05.M05.DetDefinition.matrix_det_bridge]
  rw [← Matrix.det_transpose
    ((Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c f).submatrix
      (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop))]
  congr 1
  ext a j
  exact (D05.M04.MatrixOfMap.matrix_entry b c f
    (I.val.orderEmbOfFin I.prop j) (J.val.orderEmbOfFin J.prop a)).symm

/-- Specialization to a finite rectangular coordinate matrix. -/
theorem minor_coefficients :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.minor_coefficients := by
  intro K _ m n A k I J
  have hA : Specs.D05.M04.MatrixOfMap.matrixOfMap_value (Pi.basisFun K (Fin n))
      (Pi.basisFun K (Fin m)) (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) = A := by
    ext i j
    simp [Specs.D05.M04.MatrixOfMap.matrixOfMap_value, Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value,
      LinearMap.toMatrix_apply, Pi.basisFun_apply]
  simpa only [hA] using based_minor_coefficients
    (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin m))
      (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) k I J

/-- Assemble the coefficients into the full increasing-wedge expansion. -/
theorem minor_expansion :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.minor_expansion := by
  intro K _ m n A k J
  classical
  calc
    _ = ∑ I : Set.powersetCard (Fin m) k,
        ((Pi.basisFun K (Fin m)).exteriorPower k).repr
          (WedgeSign.powerMap_value k (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A)
            (ExteriorBasis.increasingWedge (Pi.basisFun K (Fin n)) k J)) I •
          (Pi.basisFun K (Fin m)).exteriorPower k I :=
      (((Pi.basisFun K (Fin m)).exteriorPower k).sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [minor_coefficients, exteriorPower.basis_apply]
      rfl

theorem degree_zero_coefficient :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.degree_zero_coefficient := by
  intro K _ m n A I J
  rw [minor_coefficients, D05.M05.DetDefinition.empty_determinant]

theorem degree_zero_map :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.degree_zero_map := by
  intro K _ m n A x
  exact D05.M15.WedgeSign.power_map_zero (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) x

theorem above_dimension :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.above_dimension := by
  intro K _ d k hk
  exact D05.M15.ExteriorBasis.above_dimension d (Pi.basisFun K (Fin d)) k hk

theorem above_dimension_map :
    Specs.D05.M15.DeterminantLine.MinorCoefficients.above_dimension_map := by
  intro K _ m n A k hk
  rcases hk with hn | hm
  · have : Subsingleton (⋀[K]^k (Fin n → K)) :=
      Submodule.subsingleton_iff_eq_bot.mpr (above_dimension n k hn)
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  · have : Subsingleton (⋀[K]^k (Fin m → K)) :=
      Submodule.subsingleton_iff_eq_bot.mpr (above_dimension m k hm)
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

end D05.M15.DeterminantLine.MinorCoefficients
