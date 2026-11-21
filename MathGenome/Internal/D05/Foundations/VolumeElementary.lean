import MathGenome.Internal.Specs.D05.Foundations.VolumeElementary
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace D05.VolumeElementary

private def permutationEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    CoordinateSpace n ≃ₜ CoordinateSpace n where
  toFun := coordinatePermutation σ
  invFun := coordinatePermutation σ.symm
  left_inv x := by ext k; simp [coordinatePermutation]
  right_inv x := by ext k; simp [coordinatePermutation]
  continuous_toFun := continuous_pi fun k => continuous_apply (σ k)
  continuous_invFun := continuous_pi fun k => continuous_apply (σ.symm k)

private theorem continuous_dilation {n : ℕ} (i : Fin n) (c : ℝ) :
    Continuous (coordinateDilation i c) := by
  apply continuous_pi
  intro k
  by_cases h : k = i <;> simp only [coordinateDilation, h, ite_true, ite_false]
  · exact continuous_const.mul (continuous_apply i)
  · exact continuous_apply k

private def dilationEquiv {n : ℕ} (i : Fin n) (c : ℝ) (hc : c ≠ 0) :
    CoordinateSpace n ≃ₜ CoordinateSpace n where
  toFun := coordinateDilation i c
  invFun := coordinateDilation i c⁻¹
  left_inv x := by ext k; by_cases h : k = i <;> simp [coordinateDilation, h, hc]
  right_inv x := by ext k; by_cases h : k = i <;> simp [coordinateDilation, h, hc]
  continuous_toFun := continuous_dilation i c
  continuous_invFun := continuous_dilation i c⁻¹

private theorem continuous_shear {n : ℕ} (i j : Fin n) (c : ℝ) :
    Continuous (coordinateShear i j c) := by
  apply continuous_pi
  intro k
  by_cases h : k = i <;> simp only [coordinateShear, h, ite_true, ite_false]
  · exact (continuous_apply i).add
      ((continuous_const : Continuous (fun _ : CoordinateSpace n => c)).mul (continuous_apply j))
  · exact continuous_apply k

private def shearEquiv {n : ℕ} (i j : Fin n) (c : ℝ) (hij : i ≠ j) :
    CoordinateSpace n ≃ₜ CoordinateSpace n where
  toFun := coordinateShear i j c
  invFun := coordinateShear i j (-c)
  left_inv x := by
    ext k
    by_cases h : k = i
    · subst k; simp [coordinateShear, hij.symm]
    · simp [coordinateShear, h]
  right_inv x := by
    ext k
    by_cases h : k = i
    · subst k; simp [coordinateShear, hij.symm]
    · simp [coordinateShear, h]
  continuous_toFun := continuous_shear i j c
  continuous_invFun := continuous_shear i j (-c)

theorem permutationHomeomorph : Spec.permutationHomeomorph :=
  fun _ σ => ⟨permutationEquiv σ, rfl⟩

theorem dilationHomeomorph : Spec.dilationHomeomorph :=
  fun _ i c hc => ⟨dilationEquiv i c hc, rfl⟩

theorem shearHomeomorph : Spec.shearHomeomorph :=
  fun _ i j c hij => ⟨shearEquiv i j c hij, rfl⟩

/-- Product-measure reindexing, without a determinant or a linear-change rule. -/
private theorem permutationMeasurePreserving {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (coordinatePermutation σ) := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm using 1
  ext x k
  simp [coordinatePermutation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]

/-- The one-coordinate dilation rule on rectangles extends by product-measure
uniqueness. The proof uses extended nonnegative measures throughout. -/
private theorem smul_map_dilation {n : ℕ} (i : Fin n) (c : ℝ) (hc : c ≠ 0) :
    ENNReal.ofReal |c| • Measure.map (coordinateDilation i c) volume = volume := by
  refine (Measure.pi_eq (μ := fun _ : Fin n => (volume : Measure ℝ)) fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (continuous_dilation i c).measurable (.univ_pi hs)]
  have hpre : coordinateDilation i c ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun k => (fun t : ℝ => if k = i then c * t else t) ⁻¹' s k) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, coordinateDilation]
  rw [hpre, volume_pi_pi, smul_eq_mul]
  have ha : (∏ k : Fin n, (if k = i then ENNReal.ofReal |c| else 1)) =
      ENNReal.ofReal |c| := by simp
  rw [← ha, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k = i
  · subst k
    simp only [ite_true]
    rw [Real.volume_preimage_mul_left hc, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul, mul_inv_cancel₀ hc]
    simp
  · simp [hk]

private theorem shear_update {n : ℕ} (i j : Fin n) (c : ℝ) (hij : i ≠ j)
    (x : CoordinateSpace n) (y : ℝ) :
    coordinateShear i j c (Function.update x i y) =
      Function.update x i (y + c * x j) := by
  ext k
  by_cases hk : k = i
  · subst k; simp [coordinateShear, hij.symm]
  · simp [coordinateShear, hk]

/-- Tonelli reduces the shear to a one-dimensional translation on each fiber.
No integrability or finite-measure hypothesis is used. -/
private theorem shearMeasurePreserving {n : ℕ} (i j : Fin n) (c : ℝ) (hij : i ≠ j) :
    MeasurePreserving (coordinateShear i j c) := by
  have ht := (continuous_shear i j c).measurable
  refine ⟨ht, (Measure.pi_eq fun s hs => ?_).symm⟩
  have h2s : MeasurableSet (univ.pi s) := .univ_pi hs
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht, volume_pi]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp_rw [shear_update i j c hij]
  exact lintegral_add_right_eq_self (fun y => (univ.pi s).indicator 1 (Function.update x i y))
    (c * x j)

theorem permutationBorelVolume : Spec.permutationBorelVolume := by
  intro n σ E hE
  have hB : MeasurableSet (coordinatePermutation σ '' E) :=
    (permutationEquiv σ).toMeasurableEquiv.measurableSet_image.mpr hE
  refine ⟨hB, ?_⟩
  have hm := congrArg (fun μ : Measure (CoordinateSpace n) => μ (coordinatePermutation σ '' E))
    (permutationMeasurePreserving σ).map_eq
  rw [Measure.map_apply (permutationMeasurePreserving σ).measurable hB,
    Set.preimage_image_eq E (show Function.Injective (coordinatePermutation σ) from
      (permutationEquiv σ).injective)] at hm
  exact hm.symm

theorem dilationBorelVolume : Spec.dilationBorelVolume := by
  intro n i c hc E hE
  have hB : MeasurableSet (coordinateDilation i c '' E) :=
    (dilationEquiv i c hc).toMeasurableEquiv.measurableSet_image.mpr hE
  refine ⟨hB, ?_⟩
  have hm := congrArg (fun μ : Measure (CoordinateSpace n) => μ (coordinateDilation i c '' E))
    (smul_map_dilation i c hc)
  rw [Measure.smul_apply, Measure.map_apply (continuous_dilation i c).measurable hB,
    Set.preimage_image_eq E (show Function.Injective (coordinateDilation i c) from
      (dilationEquiv i c hc).injective)] at hm
  change volume (coordinateDilation i c '' E) = ENNReal.ofReal |c| * volume E
  exact hm.symm

theorem shearBorelVolume : Spec.shearBorelVolume := by
  intro n i j c hij E hE
  have hB : MeasurableSet (coordinateShear i j c '' E) :=
    (shearEquiv i j c hij).toMeasurableEquiv.measurableSet_image.mpr hE
  refine ⟨hB, ?_⟩
  have hm := congrArg (fun μ : Measure (CoordinateSpace n) => μ (coordinateShear i j c '' E))
    (shearMeasurePreserving i j c hij).map_eq
  rw [Measure.map_apply (continuous_shear i j c).measurable hB,
    Set.preimage_image_eq E (show Function.Injective (coordinateShear i j c) from
      (shearEquiv i j c hij).injective)] at hm
  exact hm.symm

theorem completionAgreement : Spec.completionAgreement := fun _ _ => rfl

theorem zeroDimensionalVolume : Spec.zeroDimensionalVolume := by
  have h : (volume : Measure (CoordinateSpace 0)) = Measure.dirac 0 :=
    Measure.volume_pi_eq_dirac 0
  refine ⟨h, ?_, ?_⟩ <;> simp [h]

end D05.VolumeElementary
