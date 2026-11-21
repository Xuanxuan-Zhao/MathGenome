import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.AffineHaarNonunimodular
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch21.ModularFunction
import MathGenome.Internal.RealAnalysis.D11.Ch09.LinearJacobian
import MathGenome.Internal.RealAnalysis.D11.Ch18.SecondCountableBorelRegular
import MathGenome.Internal.RealAnalysis.D11.Ch05.DensityMeasureDomains
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Positive affine transformations, with their open-half-plane topology and
their Borel density measures. The right-set modular convention is used.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch21.AffineHaarNonunimodular
open D11.Ch21.Affine
open Specs.D11.Ch21.AffineHaarNonunimodular (leftDensity rightDensity)

def leftMeasure : @Measure Group (borel Group) :=
  D11.Ch05.DensityMeasureDomains.densityMeasure coordinateArea
    (fun g => ENNReal.ofReal (Specs.D11.Ch21.AffineHaarNonunimodular.leftDensity g))

def rightMeasure : @Measure Group (borel Group) :=
  D11.Ch05.DensityMeasureDomains.densityMeasure coordinateArea
    (fun g => ENNReal.ofReal (Specs.D11.Ch21.AffineHaarNonunimodular.rightDensity g))

theorem group_structure : Specs.D11.Ch21.AffineHaarNonunimodular.group_structure :=
  ⟨inferInstance, inferInstance, inferInstance, fun _ _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩⟩

theorem continuous_leftDensity : Continuous Specs.D11.Ch21.AffineHaarNonunimodular.leftDensity :=
  (continuous_scale.pow 2).inv₀ fun g => pow_ne_zero _ (scale_pos g).ne'

theorem continuous_rightDensity : Continuous Specs.D11.Ch21.AffineHaarNonunimodular.rightDensity :=
  continuous_scale.inv₀ fun g => (scale_pos g).ne'

theorem densities_positive_continuous : Specs.D11.Ch21.AffineHaarNonunimodular.densities_positive_continuous :=
  ⟨continuous_leftDensity, continuous_rightDensity,
    fun g => inv_pos.mpr (sq_pos_of_pos (scale_pos g)),
    fun g => inv_pos.mpr (scale_pos g)⟩

theorem coordinate_inclusion : Topology.IsOpenEmbedding (Subtype.val : Group → Plane) :=
  isOpen_halfPlane.isOpenEmbedding_subtypeVal

theorem coordinate_measurableEmbedding : MeasurableEmbedding (fun g : Group => (g.val : Plane)) :=
  Topology.IsOpenEmbedding.measurableEmbedding (α := Group) (β := Plane) coordinate_inclusion

instance coordinateArea_finiteOnCompacts : IsFiniteMeasureOnCompacts coordinateArea :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    coordinate_measurableEmbedding

instance leftMeasure_locallyFinite : IsLocallyFiniteMeasure leftMeasure :=
  IsLocallyFiniteMeasure.withDensity_ofReal continuous_leftDensity

instance rightMeasure_locallyFinite : IsLocallyFiniteMeasure rightMeasure :=
  IsLocallyFiniteMeasure.withDensity_ofReal continuous_rightDensity

theorem radon_measures : Specs.D11.Ch21.AffineHaarNonunimodular.radon_measures := by
  constructor
  · exact (D11.Ch18.SecondCountableBorelRegular.second_countable_regular leftMeasure
      ((D11.Ch18.compactFinite_iff leftMeasure).mpr inferInstance)).2.1
  · exact (D11.Ch18.SecondCountableBorelRegular.second_countable_regular rightMeasure
      ((D11.Ch18.compactFinite_iff rightMeasure).mpr inferInstance)).2.1

theorem coordinateArea_ne_zero : coordinateArea ≠ 0 := by
  intro h
  have harea : coordinateArea univ = volume halfPlane := by
    rw [coordinateArea, coordinate_measurableEmbedding.comap_apply]
    congr 1
    exact Set.image_univ.trans Subtype.range_val
  have hpos : 0 < (volume : Measure Plane) halfPlane :=
    isOpen_halfPlane.measure_pos volume ⟨!₂[1, 0], by change (0 : ℝ) < 1; exact zero_lt_one⟩
  rw [h] at harea
  simp only [Measure.coe_zero, Pi.zero_apply] at harea
  exact (ne_of_gt hpos) harea.symm

theorem densityMeasure_ne_zero (w : Group → ℝ) (hw : Continuous w) (hpos : ∀ x, 0 < w x) :
    coordinateArea.withDensity (fun x => ENNReal.ofReal (w x)) ≠ 0 := by
  have hac : coordinateArea ≪ coordinateArea.withDensity (fun x => ENNReal.ofReal (w x)) :=
    withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne'))
  intro h
  apply coordinateArea_ne_zero
  apply Measure.measure_univ_eq_zero.mp
  exact hac (by rw [h]; simp)

theorem leftMeasure_ne_zero : leftMeasure ≠ 0 :=
  densityMeasure_ne_zero Specs.D11.Ch21.AffineHaarNonunimodular.leftDensity continuous_leftDensity densities_positive_continuous.2.2.1

theorem rightMeasure_ne_zero : rightMeasure ≠ 0 :=
  densityMeasure_ne_zero Specs.D11.Ch21.AffineHaarNonunimodular.rightDensity continuous_rightDensity densities_positive_continuous.2.2.2


def rightMatrix (g : Group) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![scale g, 0; shift g, 1]

theorem rightMatrix_det (g : Group) : (rightMatrix g).det = scale g := by
  simp [rightMatrix, Matrix.det_fin_two]

def rightLinear (g : Group) : Plane ≃ₗ[ℝ] Plane :=
  (rightMatrix g).toLinearEquiv (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (isUnit_iff_ne_zero.mpr (by rw [rightMatrix_det]; exact (scale_pos g).ne'))

theorem rightLinear_apply (g : Group) (p : Plane) :
    rightLinear g p = !₂[p 0 * scale g, p 1 + p 0 * shift g] := by
  change Matrix.toEuclideanLin (rightMatrix g) p = _
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, rightMatrix,
    dotProduct, Fin.sum_univ_two, mul_comm, add_comm]

theorem rightLinear_det (g : Group) :
    LinearMap.det (rightLinear g).toLinearMap = scale g := by
  change LinearMap.det (Matrix.toLin _ _ (rightMatrix g)) = _
  rw [LinearMap.det_toLin, rightMatrix_det]

lemma weighted_image {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (e : X ≃ᵐ X) (j k : ℝ≥0∞) (w : X → ℝ≥0∞) (hw : Measurable w)
    (he : ∀ E : Set X, MeasurableSet E → μ (e '' E) = j * μ E)
    (hweight : ∀ x, w (e x) = k * w x) (E : Set X) (hE : MeasurableSet E) :
    (μ.withDensity w) (e '' E) = (j * k) * (μ.withDensity w) E := by
  have hmap : μ.map e.symm = j • μ := by
    ext A hA
    rw [Measure.map_apply e.symm.measurable hA, Measure.smul_apply, smul_eq_mul,
      ← e.image_eq_preimage_symm]
    exact he A hA
  rw [withDensity_apply _ (e.measurableSet_image.mpr hE), withDensity_apply _ hE]
  calc
    (∫⁻ x in e '' E, w x ∂μ) =
        ∫⁻ x in E, w (e x) ∂(μ.map e.symm) := by
      simpa only [Function.comp_apply, ← e.image_eq_preimage_symm, e.apply_symm_apply] using
        (setLIntegral_map (μ := μ) hE (hw.comp e.measurable) e.symm.measurable).symm
    _ = j * ∫⁻ x in E, w (e x) ∂μ := by
      rw [hmap, Measure.restrict_smul, lintegral_smul_measure]
      rfl
    _ = (j * k) * ∫⁻ x in E, w x ∂μ := by
      simp_rw [hweight]
      rw [lintegral_const_mul k hw, mul_assoc]


def leftLinear (g : Group) : Plane ≃ₗ[ℝ] Plane :=
  LinearEquiv.smulOfNeZero ℝ Plane (scale g) (scale_pos g).ne'

theorem leftLinear_apply (g : Group) (p : Plane) : leftLinear g p = scale g • p := rfl

theorem leftLinear_det (g : Group) :
    LinearMap.det (leftLinear g).toLinearMap = scale g ^ 2 := by
  change LinearMap.det (scale g • (LinearMap.id : Plane →ₗ[ℝ] Plane)) = _
  rw [LinearMap.det_smul]
  simp

/-- The previously proved linear Lebesgue Jacobian, on Borel volume. -/
theorem volume_linear (T : Plane ≃ₗ[ℝ] Plane) (E : Set Plane) :
    volume (T '' E) = ENNReal.ofReal |LinearMap.det T.toLinearMap| * volume E := by
  rw [D11.Ch03.LebesgueMeasures.native_outer_agreement 2 (T '' E),
    D11.Ch03.LebesgueMeasures.native_outer_agreement 2 E]
  exact D11.Ch09.LinearJacobian.outer_linear 2 T E

theorem coordinateArea_left_image (g : Group) (E : Set Group) :
    coordinateArea ((fun x => g * x) '' E) =
      ENNReal.ofReal (scale g ^ 2) * coordinateArea E := by
  simp only [coordinateArea, coordinate_measurableEmbedding.comap_apply]
  have hset : (fun x : Group => x.val) '' ((fun x => g * x) '' E) =
      (fun p : Plane => !₂[0, shift g] + leftLinear g p) '' ((fun x : Group => x.val) '' E) := by
    simp only [image_image]
    congr 1
    funext x
    apply PiLp.ext
    intro i
    fin_cases i
    · change scale (g * x) = 0 + scale g * scale x
      simp
    · change shift (g * x) = shift g + scale g * shift x
      rfl
  rw [hset]
  rw [← Set.image_image (fun p : Plane => !₂[0, shift g] + p) (leftLinear g)
    ((fun x : Group => x.val) '' E)]
  rw [image_add_left, measure_preimage_add, volume_linear, leftLinear_det,
    abs_of_nonneg (sq_nonneg _)]

theorem coordinateArea_right_image (g : Group) (E : Set Group) :
    coordinateArea ((fun x => x * g) '' E) =
      ENNReal.ofReal (scale g) * coordinateArea E := by
  simp only [coordinateArea, coordinate_measurableEmbedding.comap_apply]
  have hset : (fun x : Group => x.val) '' ((fun x => x * g) '' E) =
      rightLinear g '' ((fun x : Group => x.val) '' E) := by
    simp only [image_image]
    congr 1
    funext x
    rw [rightLinear_apply]
    rfl
  rw [hset, volume_linear, rightLinear_det, abs_of_pos (scale_pos g)]


theorem leftDensity_mul (g h : Group) : leftDensity (g * h) = leftDensity g * leftDensity h := by
  simp [leftDensity, mul_pow, mul_comm]

theorem rightDensity_mul (g h : Group) : rightDensity (g * h) = rightDensity g * rightDensity h := by
  simp [rightDensity, mul_comm]

theorem left_weight_mul (g h : Group) :
    ENNReal.ofReal (leftDensity (g * h)) =
      ENNReal.ofReal (leftDensity g) * ENNReal.ofReal (leftDensity h) := by
  rw [leftDensity_mul]
  exact ENNReal.ofReal_mul (show 0 ≤ leftDensity g from inv_nonneg.mpr (sq_nonneg _))

theorem right_weight_mul (g h : Group) :
    ENNReal.ofReal (rightDensity (g * h)) =
      ENNReal.ofReal (rightDensity g) * ENNReal.ofReal (rightDensity h) := by
  rw [rightDensity_mul]
  exact ENNReal.ofReal_mul (show 0 ≤ rightDensity g from (inv_pos.mpr (scale_pos g)).le)

theorem left_jacobian_cancel (g : Group) :
    ENNReal.ofReal (scale g ^ 2) * ENNReal.ofReal (leftDensity g) = 1 := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  simp [leftDensity, (scale_pos g).ne']

theorem right_jacobian_cancel (g : Group) :
    ENNReal.ofReal (scale g) * ENNReal.ofReal (rightDensity g) = 1 := by
  rw [← ENNReal.ofReal_mul (scale_pos g).le]
  simp [rightDensity, (scale_pos g).ne']

theorem right_jacobian_left_weight (g : Group) :
    ENNReal.ofReal (scale g) * ENNReal.ofReal (leftDensity g) =
      ENNReal.ofReal ((scale g)⁻¹) := by
  rw [← ENNReal.ofReal_mul (scale_pos g).le]
  congr 1
  dsimp [leftDensity]
  field_simp

/-- Left invariance of the inverse-square coordinate density. -/
theorem left_haar : Specs.D11.Ch21.AffineHaarNonunimodular.left_haar := by
  refine ⟨leftMeasure_ne_zero, radon_measures.1, ?_⟩
  intro g E hE
  have h := weighted_image coordinateArea (Homeomorph.mulLeft g).toMeasurableEquiv
    (ENNReal.ofReal (scale g ^ 2)) (ENNReal.ofReal (leftDensity g))
    (fun x => ENNReal.ofReal (leftDensity x)) continuous_leftDensity.measurable.ennreal_ofReal
    (fun A _ => coordinateArea_left_image g A) (left_weight_mul g) E hE
  rw [left_jacobian_cancel, one_mul] at h
  exact h

/-- Right invariance of the inverse-first-coordinate density. -/
theorem right_haar : Specs.D11.Ch21.AffineHaarNonunimodular.right_haar := by
  refine ⟨rightMeasure_ne_zero, radon_measures.2, ?_⟩
  intro g E hE
  have h := weighted_image coordinateArea (Homeomorph.mulRight g).toMeasurableEquiv
    (ENNReal.ofReal (scale g)) (ENNReal.ofReal (rightDensity g))
    (fun x => ENNReal.ofReal (rightDensity x)) continuous_rightDensity.measurable.ennreal_ofReal
    (fun A _ => coordinateArea_right_image g A)
    (fun x => (right_weight_mul x g).trans (mul_comm _ _)) E hE
  rw [right_jacobian_cancel, one_mul] at h
  exact h

theorem right_mass_left_measure :
    Specs.D11.Ch21.AffineHaarNonunimodular.right_mass_left_measure := by
  intro g E hE
  have h := weighted_image coordinateArea (Homeomorph.mulRight g).toMeasurableEquiv
    (ENNReal.ofReal (scale g)) (ENNReal.ofReal (leftDensity g))
    (fun x => ENNReal.ofReal (leftDensity x)) continuous_leftDensity.measurable.ennreal_ofReal
    (fun A _ => coordinateArea_right_image g A)
    (fun x => (left_weight_mul x g).trans (mul_comm _ _)) E hE
  rw [right_jacobian_left_weight] at h
  exact h

theorem modular_function : Specs.D11.Ch21.AffineHaarNonunimodular.modular_function := by
  intro g
  exact (D11.Ch21.ModularFunction.modularFunction_unique leftMeasure left_haar g
    ((scale g)⁻¹) ⟨inv_pos.mpr (scale_pos g), right_mass_left_measure g⟩).symm

theorem nonunimodular_at : Specs.D11.Ch21.AffineHaarNonunimodular.nonunimodular_at := by
  intro g hg
  rw [modular_function]
  simpa using hg

theorem nonunimodular : Specs.D11.Ch21.AffineHaarNonunimodular.nonunimodular := by
  have hg : scale (ofCoordinates 2 0 (by norm_num)) ≠ 1 := by norm_num [scale, ofCoordinates]
  constructor
  · intro h
    exact nonunimodular_at _ hg (h _)
  · intro hR
    change D11.Ch21.isRightHaarMeasure leftMeasure at hR
    have hone (g : Group) :
        Specs.D11.Ch21.ModularFunction.modularFunction_value leftMeasure g = 1 :=
      (D11.Ch21.ModularFunction.modularFunction_unique leftMeasure left_haar g 1
        ⟨zero_lt_one, fun E hE => by simpa only [ENNReal.ofReal_one, one_mul] using hR.2.2 g E hE⟩).symm
    exact nonunimodular_at _ hg (hone _)

end D11.Ch21.AffineHaarNonunimodular
