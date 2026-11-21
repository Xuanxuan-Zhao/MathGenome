import MathGenome.Internal.Specs.D05.M05.Volume
import MathGenome.Internal.D05.M05.Orientation
import MathGenome.Internal.D05.M05.DetProduct
import MathGenome.Internal.D05.Foundations.VolumeChange
import MathGenome.Internal.D05.M12.OnBasis
import Mathlib.Tactic.Linarith

/-! Signed volume, independence of oriented orthonormal coordinates, and
agreement of ordinary parallelepiped volume with complete Lebesgue measure. -/
noncomputable section
open MeasureTheory Set

namespace D05.M05.Volume
open Specs.D05.M05.Volume Specs.D05.M04.ChangeBasis
open D05.VolumeElementary

abbrev signedVolume : signedVolume_type := signedVolume_value
abbrev ordinaryVolume : ordinaryVolume_type := ordinaryVolume_value
abbrev unitCube : unitCube_type := unitCube_value
abbrev parallelepiped : parallelepiped_type := parallelepiped_value

theorem coordinate_columns : Specs.D05.M05.Volume.coordinate_columns := by
  intro V _ _ n b v i j
  rfl

theorem signedVolume_eq_basis_det : Specs.D05.M05.Volume.signedVolume_eq_basis_det := by
  intro V _ _ n b v
  exact DetDefinition.matrix_det_bridge _

private theorem conversion_matrix {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b c : Module.Basis (Fin n) ℝ V) :
    changeMatrix_value b c = b.toMatrix c := by
  change LinearMap.toMatrix c b LinearMap.id = _
  exact LinearMap.toMatrix_id_eq_basis_toMatrix c b

theorem conversion_orthogonal : Specs.D05.M05.Volume.conversion_orthogonal := by
  intro V _ _ n b c hb hc
  let B := b.toOrthonormalBasis ((D05.M12.Orthonormal.orthonormal_iff_mathlib b).mp hb)
  let C := c.toOrthonormalBasis ((D05.M12.Orthonormal.orthonormal_iff_mathlib c).mp hc)
  have h := B.toMatrix_orthonormalBasis_conjTranspose_mul_self C
  simpa [B, C, conversion_matrix, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem conversion_det_sq : Specs.D05.M05.Volume.conversion_det_sq := by
  intro V _ _ n b c hb hc
  have h := congrArg determinant (conversion_orthogonal b c hb hc)
  rw [DetProduct.det_mul, DetProduct.det_transpose, DetDefinition.identity_determinant] at h
  simpa [pow_two] using h

theorem oriented_conversion_det_one : Specs.D05.M05.Volume.oriented_conversion_det_one := by
  intro V _ _ n b c hb hc hpos
  have hs := conversion_det_sq b c hb hc
  change 0 < determinant (changeMatrix_value b c) at hpos
  rcases sq_eq_one_iff.mp hs with h | h
  · exact h
  · linarith

private theorem columns_change {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b c : Module.Basis (Fin n) ℝ V) (v : Fin n → V) :
    b.toMatrix c * c.toMatrix v = b.toMatrix v := by
  exact b.toMatrix_mul_toMatrix c v

theorem signedVolume_basis_independent : Specs.D05.M05.Volume.signedVolume_basis_independent := by
  intro V _ _ n b c hb hc ho v
  have hdet := oriented_conversion_det_one b c hb hc ho
  rw [conversion_matrix] at hdet
  change determinant (b.toMatrix v) = determinant (c.toMatrix v)
  rw [← columns_change b c v, DetProduct.det_mul, hdet, one_mul]

theorem ordinaryVolume_basis_independent : Specs.D05.M05.Volume.ordinaryVolume_basis_independent := by
  intro V _ _ n b c hb hc v
  have hs := conversion_det_sq b c hb hc
  rw [conversion_matrix] at hs
  have ha : |determinant (b.toMatrix c)| = 1 := by
    rcases sq_eq_one_iff.mp hs with h | h <;> rw [h] <;> norm_num
  change |determinant (b.toMatrix v)| = |determinant (c.toMatrix v)|
  rw [← columns_change b c v, DetProduct.det_mul, abs_mul, ha, one_mul]

theorem columns_linear_image : Specs.D05.M05.Volume.columns_linear_image := by
  intro V _ _ n b T v
  ext i j
  change b.repr (T (v j)) i =
    ∑ k, (LinearMap.toMatrix b b T) i k * b.repr (v j) k
  exact congrFun (T.toMatrix_mulVec_repr b b (v j)).symm i

theorem signedVolume_linear_image : Specs.D05.M05.Volume.signedVolume_linear_image := by
  intro V _ _ n b T v
  rw [signedVolume_eq_basis_det, signedVolume_eq_basis_det]
  exact b.det_comp T v

theorem ordinaryVolume_linear_image : Specs.D05.M05.Volume.ordinaryVolume_linear_image := by
  intro V _ _ n b T v
  change |signedVolume_value b (T ∘ v)| = |LinearMap.det T| * |signedVolume_value b v|
  rw [signedVolume_linear_image, abs_mul]

theorem unitCube_measure : Specs.D05.M05.Volume.unitCube_measure := by
  intro n
  constructor
  · exact measurableSet_Icc
  · change (volume : Measure (CoordinateSpace n)) (Icc 0 1) = 1
    simp [Real.volume_Icc_pi]

theorem parallelepiped_coordinates : Specs.D05.M05.Volume.parallelepiped_coordinates := by
  intro V _ _ n b v
  unfold parallelepiped_value
  rw [← image_comp]
  congr 1
  funext t
  ext i
  simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, map_sum, map_smul, mul_comm]

theorem invertible_measure_scaling : Specs.D05.M05.Volume.invertible_measure_scaling :=
  D05.VolumeChange.invertibleVolume

theorem singular_null_image : Specs.D05.M05.Volume.singular_null_image :=
  D05.VolumeChange.singularVolume

theorem parallelepiped_measure : Specs.D05.M05.Volume.parallelepiped_measure := by
  intro V _ _ n b _ v
  have hm : NullMeasurableSet ((b.toMatrix v).mulVec '' unitCube_value n)
      (volume : Measure (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion
        ((b.toMatrix v).mulVec '' unitCube_value n) = ENNReal.ofReal |(b.toMatrix v).det| := by
    by_cases h : (b.toMatrix v).det = 0
    · obtain ⟨U, _, _, _, hmeas, hz⟩ :=
        singular_null_image n (b.toMatrix v) h (unitCube_value n)
      exact ⟨hmeas, by simpa only [h, abs_zero, ENNReal.ofReal_zero] using hz⟩
    · have hunit : IsUnit (b.toMatrix v) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
      obtain ⟨hmeas, hv⟩ := invertible_measure_scaling n (b.toMatrix v) hunit (unitCube_value n)
        (unitCube_measure n).1.nullMeasurableSet
      exact ⟨hmeas, by simpa only [(unitCube_measure n).2, mul_one] using hv⟩
  constructor
  · rw [parallelepiped_coordinates]
    exact hm.1
  · change (volume : Measure (CoordinateSpace n)).completion
        (b.equivFun '' parallelepiped_value v) = ENNReal.ofReal |determinant (b.toMatrix v)|
    calc
      _ = (volume : Measure (CoordinateSpace n)).completion
          ((b.toMatrix v).mulVec '' unitCube_value n) :=
        congrArg (fun E : Set (CoordinateSpace n) =>
          (volume : Measure (CoordinateSpace n)).completion E) (parallelepiped_coordinates b v)
      _ = _ := by rw [DetDefinition.matrix_det_bridge]; exact hm.2

theorem empty_volumes : Specs.D05.M05.Volume.empty_volumes := by
  constructor
  · intro V _ _ b v
    have h : signedVolume_value b v = 1 := DetDefinition.empty_determinant _
    exact ⟨h, by change |signedVolume_value b v| = 1; rw [h, abs_one]⟩
  · exact D05.VolumeChange.zeroDimensionalVolume.1

end D05.M05.Volume
