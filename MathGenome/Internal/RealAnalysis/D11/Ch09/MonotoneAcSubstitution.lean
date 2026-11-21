import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.MonotoneAcSubstitution
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcFtc
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.LebesgueNormedSpace
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch09.MonotoneAcSubstitution

/-- On the interior the classical derivative of a monotone function is
nonnegative, even at points where the totalized derivative is zero. -/
lemma derivative_nonneg {F : ℝ → ℝ} {a b x : ℝ}
    (hm : MonotoneOn F (Icc a b)) (hx : x ∈ Ioo a b) : 0 ≤ deriv F x := by
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact hm.derivWithin_nonneg

/-- The measurable differentiability set has full measure in the interval. -/
lemma differentiability_set_ae (F : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hAC : D11.Ch12.AbsolutelyContinuousOnInterval F a b) :
    (Ioo a b ∩ {x | DifferentiableAt ℝ F x} : Set ℝ) =ᵐ[volume] Icc a b := by
  have hd := ((D11.Ch12.AcFtc.ftc_real F hab).2.1.mp hAC).1
  have hi : (Ioo a b : Set ℝ) =ᵐ[volume] Icc a b := by
    exact Ioo_ae_eq_Icc
  filter_upwards [hd, hi] with x hx hxi
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact propext ⟨fun h => hxi.mp h.1, fun h => ⟨hxi.mpr h, (hx (hxi.mpr h)).differentiableAt⟩⟩

/-- The differentiability set has an image of full target measure. Its image
mass is computed by the monotone area formula, and AC makes that mass exactly
`F b - F a`. Thus no theorem about images of arbitrary null sets is needed. -/
lemma image_differentiability_set_ae (F : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hm : MonotoneOn F (Icc a b))
    (hAC : D11.Ch12.AbsolutelyContinuousOnInterval F a b) :
    (F '' (Ioo a b ∩ {x | DifferentiableAt ℝ F x}) : Set ℝ) =ᵐ[volume]
      Icc (F a) (F b) := by
  let s := Ioo a b ∩ {x | DifferentiableAt ℝ F x}
  have hs : MeasurableSet s := measurableSet_Ioo.inter
    (measurableSet_of_differentiableAt ℝ F)
  have hsub : s ⊆ Icc a b := fun _ hx => Ioo_subset_Icc_self hx.1
  have hmono : MonotoneOn F s := hm.mono hsub
  have hds : ∀ x ∈ s, HasDerivWithinAt F (deriv F x) s x :=
    fun _ hx => hx.2.hasDerivAt.hasDerivWithinAt
  have hsae : s =ᵐ[volume] Icc a b := differentiability_set_ae F hab hAC
  obtain ⟨_, hint, hr⟩ := (D11.Ch12.AcFtc.ftc_real F hab).2.1.mp hAC
  have hn : 0 ≤ᵐ[volume.restrict (Icc a b)] deriv F := by
    rw [EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ (fun x hx => derivative_nonneg hm hx)
  have hmass : (∫⁻ x in Icc a b, ENNReal.ofReal (deriv F x)) =
      ENNReal.ofReal (F b - F a) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    congr 1
    linarith [hr b (right_mem_Icc.mpr hab.le)]
  have himsub : F '' s ⊆ Icc (F a) (F b) := by
    rintro y ⟨x, hx, rfl⟩
    exact hm.mapsTo_Icc (hsub hx)
  apply ae_eq_of_subset_of_measure_ge himsub
  · rw [← lintegral_deriv_eq_volume_image_of_monotoneOn hs hds hmono,
      Measure.restrict_congr_set hsae, hmass, Real.volume_Icc]
  · exact (hs.image_of_monotoneOn hmono).nullMeasurableSet
  · exact measure_Icc_lt_top.ne

/-- Nonnegative substitution before imposing target measurability. -/
lemma lintegral_substitution (F : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hm : MonotoneOn F (Icc a b))
    (hAC : D11.Ch12.AbsolutelyContinuousOnInterval F a b) (h : ℝ → ℝ≥0∞) :
    (∫⁻ x in Icc a b, ENNReal.ofReal (deriv F x) * h (F x)) =
      ∫⁻ y in Icc (F a) (F b), h y := by
  let s := Ioo a b ∩ {x | DifferentiableAt ℝ F x}
  have hs : MeasurableSet s := measurableSet_Ioo.inter
    (measurableSet_of_differentiableAt ℝ F)
  have hsub : s ⊆ Icc a b := fun _ hx => Ioo_subset_Icc_self hx.1
  rw [← Measure.restrict_congr_set (differentiability_set_ae F hab hAC),
    ← lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs
      (fun x hx => hx.2.hasDerivAt.hasDerivWithinAt) (hm.mono hsub) h,
    Measure.restrict_congr_set (image_differentiability_set_ae F hab hm hAC)]

/-- The derivative density is transported to interval Lebesgue measure. The
map need only be measurable for that density, not for completed target sets. -/
lemma map_derivative_density (F : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hm : MonotoneOn F (Icc a b))
    (hAC : D11.Ch12.AbsolutelyContinuousOnInterval F a b) :
    Measure.map F ((volume.restrict (Icc a b)).withDensity
      (fun x => ENNReal.ofReal (deriv F x))) = volume.restrict (Icc (F a) (F b)) := by
  have hmF : AEMeasurable F (volume.restrict (Icc a b)) :=
    (D11.Ch12.AcBasic.uniformContinuousOn hab.le hAC).continuousOn.aemeasurable
      measurableSet_Icc
  have hdF := hmF.mono_ac (withDensity_absolutelyContinuous
    (volume.restrict (Icc a b)) (fun x => ENNReal.ofReal (deriv F x)))
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map' hh.aemeasurable hdF,
    lintegral_withDensity_eq_lintegral_mul₀'
      (measurable_deriv F).ennreal_ofReal.aemeasurable
      (hh.aemeasurable.comp_aemeasurable' hdF)]
  exact lintegral_substitution F hab hm hAC h

/-- Completion measurability of the weighted nonnegative composition follows
from transport in the derivative measure and multiplication by its density. -/
theorem nonnegative_substitution :
    Specs.D11.Ch09.MonotoneAcSubstitution.nonnegative_substitution := by
  intro F a b hab hm hAC h hh
  have hmF : AEMeasurable F (volume.restrict (Icc a b)) :=
    (D11.Ch12.AcBasic.uniformContinuousOn hab.le hAC).continuousOn.aemeasurable
      measurableSet_Icc
  have hdF := hmF.mono_ac (withDensity_absolutelyContinuous
    (volume.restrict (Icc a b)) (fun x => ENNReal.ofReal (deriv F x)))
  have hhmap : AEMeasurable h (Measure.map F ((volume.restrict (Icc a b)).withDensity
      (fun x => ENNReal.ofReal (deriv F x)))) := by
    rw [map_derivative_density F hab hm hAC]
    exact hh.aemeasurable
  have hw := (aemeasurable_withDensity_ennreal_iff
    (measurable_deriv F).real_toNNReal).mp (hhmap.comp_aemeasurable hdF)
  refine ⟨hw.nullMeasurable, lintegral_substitution F hab hm hAC h⟩

/-- A finite nonnegative multiplier expresses the exact zero branch. -/
lemma weightedScalar_eq_toNNReal {K : Type*} [RCLike K]
    (F : ℝ → ℝ) (h : ℝ → K) (x : ℝ) :
    Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar F h x =
      (Real.toNNReal (deriv F x) : ℝ) • h (F x) := by
  by_cases hp : 0 < deriv F x
  · simp [Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar, hp,
      Real.coe_toNNReal _ hp.le]
  · simp [Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar, hp,
      Real.toNNReal_of_nonpos (le_of_not_gt hp)]

theorem scalar_weight_measurable :
    Specs.D11.Ch09.MonotoneAcSubstitution.scalar_weight_measurable := by
  intro K _ _ _ F a b hab hm hAC h hh
  have hmF : AEMeasurable F (volume.restrict (Icc a b)) :=
    (D11.Ch12.AcBasic.uniformContinuousOn hab.le hAC).continuousOn.aemeasurable
      measurableSet_Icc
  have hdF := hmF.mono_ac (withDensity_absolutelyContinuous
    (volume.restrict (Icc a b)) (fun x => ENNReal.ofReal (deriv F x)))
  have hhmap : AEMeasurable h (Measure.map F ((volume.restrict (Icc a b)).withDensity
      (fun x => ENNReal.ofReal (deriv F x)))) := by
    rw [map_derivative_density F hab hm hAC]
    exact hh.aemeasurable
  have hw := (aemeasurable_withDensity_iff
    (measurable_deriv F).real_toNNReal).mp (hhmap.comp_aemeasurable hdF)
  simpa only [Function.comp_apply, ← weightedScalar_eq_toNNReal] using hw.nullMeasurable

/-- Scalar transport on the differentiability set, transferred across the
null source and target complements. The hypothesis asserts integrability. -/
lemma scalar_substitution_deriv {K : Type*} [RCLike K]
    (F : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hm : MonotoneOn F (Icc a b))
    (hAC : D11.Ch12.AbsolutelyContinuousOnInterval F a b)
    (h : ℝ → K) (hh : IntegrableOn h (Icc (F a) (F b))) :
    IntegrableOn (fun x => deriv F x • h (F x)) (Icc a b) ∧
    (∫ x in Icc a b, deriv F x • h (F x)) = ∫ y in Icc (F a) (F b), h y := by
  let s := Ioo a b ∩ {x | DifferentiableAt ℝ F x}
  have hs : MeasurableSet s := measurableSet_Ioo.inter
    (measurableSet_of_differentiableAt ℝ F)
  have hsub : s ⊆ Icc a b := fun _ hx => Ioo_subset_Icc_self hx.1
  have hds : ∀ x ∈ s, HasDerivWithinAt F (deriv F x) s x :=
    fun _ hx => hx.2.hasDerivAt.hasDerivWithinAt
  have hsae := Measure.restrict_congr_set (differentiability_set_ae F hab hAC)
  have htae := Measure.restrict_congr_set (image_differentiability_set_ae F hab hm hAC)
  constructor
  · change Integrable _ _
    rw [← hsae]
    apply (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs hds
      (hm.mono hsub) h).mp
    change Integrable _ _
    rwa [htae]
  · rw [← hsae, ← integral_image_eq_integral_deriv_smul_of_monotoneOn hs hds
      (hm.mono hsub) h, htae]

/-- The branch convention only changes the untruncated derivative product on
a source null set (the endpoints); the interior derivative is nonnegative. -/
lemma weightedScalar_ae {K : Type*} [RCLike K]
    (F : ℝ → ℝ) {a b : ℝ} (hm : MonotoneOn F (Icc a b)) (h : ℝ → K) :
    Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar F h =ᵐ[
      volume.restrict (Icc a b)] (fun x => deriv F x • h (F x)) := by
  rw [EventuallyEq, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
  apply ae_of_all
  intro x hx
  dsimp [Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar]
  split_ifs with hp
  · rfl
  · have hz : deriv F x = 0 := le_antisymm (le_of_not_gt hp) (derivative_nonneg hm hx)
    simp [hz]

/-- The pointwise absolute value is exactly the nonnegative weighted
composition, including where the derivative is zero or undefined. -/
lemma weightedScalar_norm {K : Type*} [RCLike K]
    (F : ℝ → ℝ) (h : ℝ → K) (x : ℝ) :
    ENNReal.ofReal ‖Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar F h x‖ =
      ENNReal.ofReal (deriv F x) * ENNReal.ofReal ‖h (F x)‖ := by
  by_cases hp : 0 < deriv F x
  · simp [Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar, hp,
      norm_smul, Real.norm_eq_abs, abs_of_pos hp, ENNReal.ofReal_mul hp.le]
  · simp [Specs.D11.Ch09.MonotoneAcSubstitution.weightedScalar, hp,
      ENNReal.ofReal_of_nonpos (le_of_not_gt hp)]

theorem scalar_substitution : Specs.D11.Ch09.MonotoneAcSubstitution.scalar_substitution := by
  intro K _ _ _ F a b hab hm hAC h _hhmeas hh
  obtain ⟨hi, heq⟩ := scalar_substitution_deriv F hab hm hAC h hh
  have hw := weightedScalar_ae F hm h
  have hiw := hi.congr hw.symm
  refine ⟨hiw.aemeasurable.nullMeasurable, hiw, ?_, (integral_congr_ae hw).trans heq⟩
  simp_rw [weightedScalar_norm]
  exact lintegral_substitution F hab hm hAC (fun y => ENNReal.ofReal ‖h y‖)

/-- For completion-measurable nonnegative functions, the Borel-measure
integral used above is exactly the completed-measure integral. -/
lemma lintegral_completion_eq (μ : Measure ℝ) (h : ℝ → ℝ≥0∞)
    (hh : NullMeasurable h μ) :
    (∫⁻ x : NullMeasurableSpace ℝ μ, h x ∂μ.completion) = ∫⁻ x, h x ∂μ := by
  let hm : (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ)) :=
    le_eventuallyMeasurableSpace
  have ht : μ.completion.trim hm = μ := by
    apply @Measure.ext ℝ
    intro s hs
    exact (trim_measurableSet_eq hm hs).trans (Measure.completion_apply μ s)
  have hh' : AEMeasurable h (μ.completion.trim hm) := ht.symm ▸ hh.aemeasurable
  exact (lintegral_trim_ae hm hh').symm.trans
    (congrArg (fun ν : Measure ℝ => ∫⁻ x, h x ∂ν) ht)

/-- The same bridge for the integrable scalar functions in the theorem. -/
lemma scalar_completion_eq {K : Type*} [RCLike K]
    (μ : Measure ℝ) (h : ℝ → K) (hh : Integrable h μ) :
    Integrable (fun x : NullMeasurableSpace ℝ μ => h x) μ.completion ∧
    (∫ x : NullMeasurableSpace ℝ μ, h x ∂μ.completion) = ∫ x, h x ∂μ := by
  let hm : (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ)) :=
    le_eventuallyMeasurableSpace
  have ht : μ.completion.trim hm = μ := by
    apply @Measure.ext ℝ
    intro s hs
    exact (trim_measurableSet_eq hm hs).trans (Measure.completion_apply μ s)
  have hh' : Integrable h (μ.completion.trim hm) := ht.symm ▸ hh
  refine ⟨integrable_of_integrable_trim hm hh', ?_⟩
  exact (integral_trim_ae hm hh'.aestronglyMeasurable).trans
    (congrArg (fun ν : Measure ℝ => ∫ x, h x ∂ν) ht)

end D11.Ch09.MonotoneAcSubstitution
