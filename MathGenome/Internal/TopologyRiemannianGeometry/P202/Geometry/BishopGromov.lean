import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.BishopGromov
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PolarDensityComparison
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PolarVolumeIntegration
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology ENNReal

namespace P202.Geometry.BishopGromov
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.CompletenessData
  P202.CutTimeData P202.PolarVolumeData P202.ConstantCurvaturePolarData
  P202.PolarComparisonData P202.PolarIntegrationData P202.BishopGromovData
  P202.SpaceFormData P202.ModelPolarData
open Set Filter MeasureTheory
universe u

/-- The intrinsic angular measure has the same total mass in every metric
fiber as the standard Euclidean sphere in the same dimension. -/
lemma sphere_mass {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M) :
    sphereMeasure g p univ = omega n := by
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_exists S g p
  have hh := PolarVolumeDensity.map_directionSphereHomeomorph g p E hE
    (PolarVolumeDensity.fiberVolume_orthonormal g p E hE)
  have hu := congrArg (fun μ => μ univ) hh
  simpa [omega, Measure.map_apply (PolarVolumeDensity.directionSphereHomeomorph g p E hE).measurable
    MeasurableSet.univ] using hu

/-- Normalized spherical average of the directionwise truncated ratio. -/
def sphericalAverage {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (k t : ℝ) : ℝ :=
  (∫ v, truncatedRatio g F p v k t ∂sphereMeasure g p) / (omega n).toReal

lemma omega_pos {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (hn : 2 ≤ n) (p : M) : 0 < (omega n).toReal := by
  rw [← sphere_mass g p]
  letI := PolarVolumeDensity.sphere_finite g p
  exact ENNReal.toReal_pos (PolarVolumeDensity.sphere_nonzero g hn p) (measure_ne_top _ _)



section SphericalAverage
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
  {S : SmoothManifold n .euclidean M}
  (g : RiemannianMetric S) (hn : 2 ≤ n) (hc : LengthMetricComplete g)
  (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
  (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
  (k : ℝ) (hk : RicciLowerBound g R k)
  (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)

include hn hc C hC R hR hF
lemma ratio_joint_measurable :
    Measurable (fun tv : ℝ × UnitDirection g p => truncatedRatio g F p tv.2 k tv.1) := by
  have hj := (PolarVolumeDensity.regularity S g hn hc C hC R hR F hF p).2.2.1
  change Measurable (fun tv : ℝ × UnitDirection g p =>
    truncatedDensity g F p tv / s k tv.1 ^ (n-1))
  have hs : Continuous (s k) := continuous_iff_continuousAt.mpr
    (fun t => (ConstantCurvaturePolar.s_derivative k t).continuousAt)
  exact hj.div ((hs.measurable.comp measurable_fst).pow_const (n-1))

include hk in
lemma ratio_integrable (t : ℝ) (ht : t ∈ comparisonInterval k) :
    Integrable (fun v => truncatedRatio g F p v k t) (sphereMeasure g p) := by
  letI := PolarVolumeDensity.sphere_finite g p
  have hm : Measurable (fun v : UnitDirection g p => truncatedRatio g F p v k t) :=
    (ratio_joint_measurable g hn hc C hC R hR k F hF p).comp
      ((measurable_const : Measurable (fun _ : UnitDirection g p => t)).prodMk measurable_id)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun v => by
    have hb := (PolarDensityComparison.truncated_comparison S g hn hc C hC R hR k hk F hF p v).2 t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

lemma sphericalAverage_measurable : Measurable (sphericalAverage g F p k) := by
  letI := PolarVolumeDensity.sphere_finite g p
  exact ((ratio_joint_measurable g hn hc C hC R hR k F hF p).stronglyMeasurable.integral_prod_right').measurable.div_const _

include hk
lemma sphericalAverage_bounds (t : ℝ) (ht : t ∈ comparisonInterval k) :
    0 ≤ sphericalAverage g F p k t ∧ sphericalAverage g F p k t ≤ 1 := by
  letI := PolarVolumeDensity.sphere_finite g p
  have hb (v : UnitDirection g p) :=
    (PolarDensityComparison.truncated_comparison S g hn hc C hC R hR k hk F hF p v).2 t ht
  have hp := omega_pos g hn p
  refine ⟨div_nonneg (integral_nonneg fun v => (hb v).1) hp.le, ?_⟩
  apply (div_le_one hp).mpr
  have hh := integral_mono (ratio_integrable g hn hc C hC R hR k hk F hF p t ht)
    (integrable_const (1 : ℝ)) (fun v => (hb v).2)
  simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def, sphere_mass g p] using hh

lemma sphericalAverage_antitone :
    AntitoneOn (sphericalAverage g F p k) (comparisonInterval k) := by
  intro a ha b hb hab
  apply div_le_div_of_nonneg_right _ (omega_pos g hn p).le
  apply integral_mono
    (ratio_integrable g hn hc C hC R hR k hk F hF p b hb)
    (ratio_integrable g hn hc C hC R hR k hk F hF p a ha)
  intro v
  exact (PolarDensityComparison.truncated_comparison S g hn hc C hC R hR k hk F hF p v).1 ha hb hab

lemma sphericalAverage_initial_limit :
    Tendsto (sphericalAverage g F p k) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  letI := PolarVolumeDensity.sphere_finite g p
  have hmeas := ratio_joint_measurable g hn hc C hC R hR k F hF p
  have hlim : Tendsto (fun t => ∫ v, truncatedRatio g F p v k t ∂sphereMeasure g p)
      (𝓝[>] (0 : ℝ)) (𝓝 ((omega n).toReal)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := sphereMeasure g p)
      (F := fun t v => truncatedRatio g F p v k t) (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      (Eventually.of_forall fun t => (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (by
        filter_upwards [PolarDensityComparison.comparisonInterval_eventually k] with t ht
        exact ae_of_all _ fun v => by
          have hb := (PolarDensityComparison.truncated_comparison S g hn hc C hC R hR k hk F hF p v).2 t ht
          simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)
      (integrable_const (1 : ℝ))
      (ae_of_all _ fun v =>
        (PolarDensityComparison.initial_limit S g hn hc C hC R hR k hk F hF p v).2)
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def, sphere_mass g p] using hh
  change Tendsto (fun t => (∫ v, truncatedRatio g F p v k t ∂sphereMeasure g p) /
    (omega n).toReal) (𝓝[>] (0 : ℝ)) (𝓝 1)
  simpa only [div_self (ne_of_gt (omega_pos g hn p))] using hlim.div_const ((omega n).toReal)

end SphericalAverage



/-- Weighted averages of an antitone function decrease when the interval grows. -/
lemma weighted_average_antitone {D : Set ℝ} {a w : ℝ → ℝ}
    (hD : ∀ r ∈ D, 0 < r)
    (hdown : ∀ r ∈ D, Ioo 0 r ⊆ D)
    (ha : AntitoneOn a D)
    (hi : ∀ r ∈ D, IntervalIntegrable (fun t => a t * w t) volume 0 r)
    (hw : ∀ r ∈ D, IntervalIntegrable w volume 0 r)
    (hwn : ∀ t ∈ D, 0 ≤ w t)
    (hwp : ∀ r ∈ D, 0 < ∫ t in (0 : ℝ)..r, w t) :
    AntitoneOn (fun r => (∫ t in (0 : ℝ)..r, a t * w t) /
      (∫ t in (0 : ℝ)..r, w t)) D := by
  intro r hr s hs hrs
  by_cases heq : r = s
  · subst s; rfl
  have hlt : r < s := hrs.lt_of_ne heq
  have h0r := hD r hr
  have h0s := hD s hs
  have hsub : uIcc r s ⊆ uIcc 0 s := by
    rw [uIcc_of_le hrs, uIcc_of_le h0s.le]
    exact Icc_subset_Icc h0r.le le_rfl
  have hi' := (hi s hs).mono_set hsub
  have hw' := (hw s hs).mono_set hsub
  have hleft : a r * (∫ t in (0 : ℝ)..r, w t) ≤ ∫ t in (0 : ℝ)..r, a t * w t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo h0r.le ((hw r hr).const_mul _) (hi r hr)
    intro t ht
    exact mul_le_mul_of_nonneg_right (ha (hdown r hr ht) hr ht.2.le) (hwn t (hdown r hr ht))
  have hright : (∫ t in r..s, a t * w t) ≤ a r * (∫ t in r..s, w t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hrs hi' (hw'.const_mul _)
    intro t ht
    have htD := hdown s hs ⟨h0r.trans ht.1, ht.2⟩
    exact mul_le_mul_of_nonneg_right (ha hr htD ht.1.le) (hwn t htD)
  have hnew : 0 ≤ ∫ t in r..s, w t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hrs
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    by_cases hts : t = s
    · subst t; exact hwn s hs
    · exact hwn t (hdown s hs ⟨h0r.trans_le ht.1, ht.2.lt_of_ne hts⟩)
  have hN := intervalIntegral.integral_add_adjacent_intervals (hi r hr) hi'
  have hW := intervalIntegral.integral_add_adjacent_intervals (hw r hr) hw'
  apply (div_le_div_iff₀ (hwp s hs) (hwp r hr)).mpr
  have hh := mul_le_mul_of_nonneg_right hleft hnew
  have hh' := mul_le_mul_of_nonneg_right hright (hwp r hr).le
  rw [← hN, ← hW]
  nlinarith only [hh, hh']



lemma weighted_average_sandwich {D : Set ℝ} {a w : ℝ → ℝ}
    (hdown : ∀ r ∈ D, Ioo 0 r ⊆ D)
    (ha : AntitoneOn a D) (ha1 : ∀ t ∈ D, a t ≤ 1)
    (hi : ∀ r ∈ D, IntervalIntegrable (fun t => a t * w t) volume 0 r)
    (hw : ∀ r ∈ D, IntervalIntegrable w volume 0 r)
    (hwn : ∀ t ∈ D, 0 ≤ w t)
    (hwp : ∀ r ∈ D, 0 < ∫ t in (0 : ℝ)..r, w t)
    {r : ℝ} (hr : r ∈ D) (hr0 : 0 < r) :
    a r ≤ (∫ t in (0 : ℝ)..r, a t * w t) / (∫ t in (0 : ℝ)..r, w t) ∧
    (∫ t in (0 : ℝ)..r, a t * w t) / (∫ t in (0 : ℝ)..r, w t) ≤ 1 := by
  constructor
  · apply (le_div_iff₀ (hwp r hr)).mpr
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hr0.le ((hw r hr).const_mul _) (hi r hr)
    intro t ht
    exact mul_le_mul_of_nonneg_right (ha (hdown r hr ht) hr ht.2.le) (hwn t (hdown r hr ht))
  · apply (div_le_one (hwp r hr)).mpr
    apply intervalIntegral.integral_mono_on_of_le_Ioo hr0.le (hi r hr) (hw r hr)
    intro t ht
    exact mul_le_of_le_one_left (hwn t (hdown r hr ht)) (ha1 t (hdown r hr ht))

lemma weighted_average_initial_limit {D : Set ℝ} {a w : ℝ → ℝ}
    (hDe : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ D)
    (hD : ∀ r ∈ D, 0 < r)
    (hdown : ∀ r ∈ D, Ioo 0 r ⊆ D)
    (ha : AntitoneOn a D) (ha1 : ∀ t ∈ D, a t ≤ 1)
    (halim : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hi : ∀ r ∈ D, IntervalIntegrable (fun t => a t * w t) volume 0 r)
    (hw : ∀ r ∈ D, IntervalIntegrable w volume 0 r)
    (hwn : ∀ t ∈ D, 0 ≤ w t)
    (hwp : ∀ r ∈ D, 0 < ∫ t in (0 : ℝ)..r, w t) :
    Tendsto (fun r => (∫ t in (0 : ℝ)..r, a t * w t) /
      (∫ t in (0 : ℝ)..r, w t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' halim tendsto_const_nhds
  · filter_upwards [hDe] with r hr
    exact (weighted_average_sandwich hdown ha ha1 hi hw hwn hwp hr (hD r hr)).1
  · filter_upwards [hDe] with r hr
    exact (weighted_average_sandwich hdown ha ha1 hi hw hwn hwp hr (hD r hr)).2



lemma bounded_mul_intervalIntegrable {a w : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (ha : Measurable a) (hw : Continuous w)
    (hab : ∀ t ∈ Ioo 0 r, 0 ≤ a t ∧ a t ≤ 1)
    (hwn : ∀ t ∈ Ioo 0 r, 0 ≤ w t) :
    IntervalIntegrable (fun t => a t * w t) volume 0 r := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr]
  have hwi : IntegrableOn w (Ioo 0 r) :=
    ((hw.intervalIntegrable 0 r).1).mono_set Ioo_subset_Ioc_self
  apply hwi.mono' ((ha.mul hw.measurable).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hab t ht).1 (hwn t ht))]
  exact mul_le_of_le_one_left (hwn t ht) (hab t ht).2


lemma spherical_radius {a : ℝ} (ha : 0 < a) :
    Real.pi / Real.sqrt ((a ^ 2)⁻¹) = Real.pi * a := by
  rw [Real.sqrt_inv, Real.sqrt_sq ha.le, div_inv_eq_mul]

lemma model_ball_formula
    (hm : P202Specs.Geometry.PolarVolumeIntegration.model_volumeType)
    {n : ℕ} (hn : 2 ≤ n) {k : ℝ} {V : ℝ → ℝ≥0∞}
    (hV : IsModelVolume n k V) (r : ℝ) (hr : 0 < r)
    (hrk : 0 < k → r ≤ Real.pi / Real.sqrt k) :
    V r = omega n * ENNReal.ofReal (∫ t in (0 : ℝ)..r, s k t ^ (n-1)) := by
  rcases hV with ⟨rfl, G, hG, p, rfl⟩ | ⟨a, ha, rfl, A, B, hB, p, rfl⟩ |
    ⟨a, ha, rfl, S, g, C, hchart, hg, hC, hc, p, rfl⟩
  · exact hm.1 n hn G hG p r hr
  · have hk : 0 < (a ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos ha)
    exact hm.2.1 n hn a ha A B hB p r hr (by simpa only [spherical_radius ha] using hrk hk)
  · exact hm.2.2 n hn a ha S g C hchart hg hC hc p r hr


/-- Comparison weights are globally continuous, even at their first zero. -/
lemma weight_continuous (n : ℕ) (k : ℝ) : Continuous (fun t => s k t ^ (n - 1)) := by
  exact (continuous_iff_continuousAt.mpr fun t =>
    (ConstantCurvaturePolar.s_derivative k t).continuousAt).pow _

lemma comparison_down {k r : ℝ} (hr : r ∈ comparisonInterval k) :
    Ioo 0 r ⊆ comparisonInterval k := by
  intro t ht
  exact ⟨ht.1, fun hk => ht.2.trans (hr.2 hk)⟩

lemma weight_integral_pos (n : ℕ) (k r : ℝ) (hr : 0 < r)
    (hrk : 0 < k → r ≤ Real.pi / Real.sqrt k) :
    0 < ∫ t in (0 : ℝ)..r, s k t ^ (n - 1) := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on ((weight_continuous n k).intervalIntegrable 0 r) _ hr
  intro t ht
  exact pow_pos (PolarDensityComparison.model_positive ⟨ht.1, fun hk => ht.2.trans_le (hrk hk)⟩) _

lemma weight_integral_continuous (n : ℕ) (k : ℝ) :
    Continuous (fun r => ∫ t in (0 : ℝ)..r, s k t ^ (n-1)) :=
  (intervalIntegral.differentiable_integral_of_continuous (weight_continuous n k)).continuous

lemma model_ball_toReal
    (hm : P202Specs.Geometry.PolarVolumeIntegration.model_volumeType)
    {n : ℕ} (hn : 2 ≤ n) {k : ℝ} {V : ℝ → ℝ≥0∞}
    (hV : IsModelVolume n k V) (r : ℝ) (hr : 0 < r)
    (hrk : 0 < k → r ≤ Real.pi / Real.sqrt k) :
    (V r).toReal = (omega n).toReal * (∫ t in (0 : ℝ)..r, s k t ^ (n-1)) := by
  rw [model_ball_formula hm hn hV r hr hrk, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (weight_integral_pos n k r hr hrk).le]

section BallIntegral
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
  {S : SmoothManifold n .euclidean M}
  (g : RiemannianMetric S) (hn : 2 ≤ n) (hc : LengthMetricComplete g)
  (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
  (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
  (k : ℝ) (hk : RicciLowerBound g R k)
  (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
include hn hc C hC R hR hk hF

lemma averaged_weight_integrable (r : ℝ) (hr : r ∈ comparisonInterval k) :
    IntervalIntegrable (fun t => sphericalAverage g F p k t * s k t ^ (n-1)) volume 0 r := by
  apply bounded_mul_intervalIntegrable hr.1.le
    (sphericalAverage_measurable g hn hc C hC R hR k F hF p) (weight_continuous n k)
  · intro t ht
    exact sphericalAverage_bounds g hn hc C hC R hR k hk F hF p t (comparison_down hr ht)
  · intro t ht
    exact (pow_pos (PolarDensityComparison.model_positive (comparison_down hr ht)) _).le

lemma angular_lintegral (t : ℝ) (ht : t ∈ comparisonInterval k) :
    (∫⁻ v, ENNReal.ofReal (truncatedDensity g F p (t,v)) ∂sphereMeasure g p) =
      ENNReal.ofReal ((omega n).toReal * (sphericalAverage g F p k t * s k t ^ (n-1))) := by
  have hw : s k t ^ (n-1) ≠ 0 := pow_ne_zero _ (PolarDensityComparison.model_positive ht).ne'
  have heq : (fun v => truncatedDensity g F p (t,v)) =
      (fun v => truncatedRatio g F p v k t * s k t ^ (n-1)) := by
    funext v
    exact (div_mul_cancel₀ _ hw).symm
  have hi : Integrable (fun v => truncatedDensity g F p (t,v)) (sphereMeasure g p) := by
    rw [heq]
    exact (ratio_integrable g hn hc C hC R hR k hk F hF p t ht).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun v => PolarVolumeDensity.truncatedDensity_nonneg g F p (t,v))]
  congr 1
  rw [heq, integral_mul_const]
  dsimp only [sphericalAverage]
  field_simp [(omega_pos g hn p).ne'] <;> ring

lemma ball_real_integral
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{u})
    (r : ℝ) (hr : r ∈ comparisonInterval k) :
    (ballVolume g p r).toReal = (omega n).toReal *
      (∫ t in (0 : ℝ)..r, sphericalAverage g F p k t * s k t ^ (n-1)) := by
  have hi := averaged_weight_integrable g hn hc C hC R hR k hk F hF p r hr
  have hi' : IntegrableOn (fun t => (omega n).toReal *
      (sphericalAverage g F p k t * s k t ^ (n-1))) (Ioo 0 r) :=
    (hi.1.mono_set Ioo_subset_Ioc_self).const_mul _
  have hnn : ∀ᵐ t ∂volume.restrict (Ioo 0 r), 0 ≤ (omega n).toReal *
      (sphericalAverage g F p k t * s k t ^ (n-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg ENNReal.toReal_nonneg (mul_nonneg
      (sphericalAverage_bounds g hn hc C hC R hR k hk F hF p t (comparison_down hr ht)).1
      (pow_pos (PolarDensityComparison.model_positive (comparison_down hr ht)) _).le)
  have heq : ballVolume g p r = ENNReal.ofReal ((omega n).toReal *
      (∫ t in (0 : ℝ)..r, sphericalAverage g F p k t * s k t ^ (n-1))) := by
    rw [hball S g hn hc C hC R hR F hF p r hr.1]
    calc
      _ = ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal ((omega n).toReal *
          (sphericalAverage g F p k t * s k t ^ (n-1))) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        exact angular_lintegral g hn hc C hC R hR k hk F hF p t (comparison_down hr ht)
      _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) r, (omega n).toReal *
          (sphericalAverage g F p k t * s k t ^ (n-1))) :=
        (ofReal_integral_eq_lintegral_ofReal hi' hnn).symm
      _ = _ := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hr.1.le]
  rw [heq, ENNReal.toReal_ofReal]
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hr.1.le,
    integral_Ioc_eq_integral_Ioo]
  exact integral_nonneg_of_ae hnn

end BallIntegral

/-- Conditional derivation of the complete original target. The four premises
are the frozen upstream interfaces, in their contract order. This declaration
is deliberately distinct from the still unclosed original target. -/
theorem bishop_gromov_conditional
    (hball : P202Specs.Geometry.PolarVolumeIntegration.ball_integralType.{u})
    (hfinite : P202Specs.Geometry.PolarVolumeIntegration.ball_volume_finiteType.{u})
    (hleft : P202Specs.Geometry.PolarVolumeIntegration.ball_volume_left_limitType.{u})
    (hmodel : P202Specs.Geometry.PolarVolumeIntegration.model_volumeType) :
    P202Specs.Geometry.BishopGromov.bishop_gromovType.{u} := by
  intro n M _ _ S g hn hc C hC R hR k hk V hV p
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  let a := sphericalAverage g F p k
  let w := fun t => s k t ^ (n-1)
  have hw := weight_continuous n k
  have hwp (r : ℝ) (hr : r ∈ comparisonInterval k) :
      0 < ∫ t in (0 : ℝ)..r, w t :=
    weight_integral_pos n k r hr.1 (fun h => (hr.2 h).le)
  have ha : AntitoneOn a (comparisonInterval k) :=
    sphericalAverage_antitone g hn hc C hC R hR k hk F hF p
  have ha1 (t : ℝ) (ht : t ∈ comparisonInterval k) : a t ≤ 1 :=
    (sphericalAverage_bounds g hn hc C hC R hR k hk F hF p t ht).2
  have hi (r : ℝ) (hr : r ∈ comparisonInterval k) :
      IntervalIntegrable (fun t => a t * w t) volume 0 r :=
    averaged_weight_integrable g hn hc C hC R hR k hk F hF p r hr
  have hwi (r : ℝ) (_hr : r ∈ comparisonInterval k) : IntervalIntegrable w volume 0 r :=
    hw.intervalIntegrable 0 r
  have hwn (t : ℝ) (ht : t ∈ comparisonInterval k) : 0 ≤ w t :=
    (pow_pos (PolarDensityComparison.model_positive ht) _).le
  have heq (r : ℝ) (hr : r ∈ comparisonInterval k) :
      volumeRatio g p V r = (∫ t in (0 : ℝ)..r, a t * w t) / (∫ t in (0 : ℝ)..r, w t) := by
    unfold volumeRatio
    rw [ball_real_integral g hn hc C hC R hR k hk F hF p hball r hr,
      model_ball_toReal hmodel hn hV r hr.1 (fun h => (hr.2 h).le)]
    exact mul_div_mul_left _ _ (omega_pos g hn p).ne'
  have havg := weighted_average_antitone (fun r hr => hr.1)
    (fun _ hr => comparison_down hr) ha hi hwi hwn hwp
  have hanti : AntitoneOn (volumeRatio g p V) (comparisonInterval k) := by
    intro r hr s hs hrs
    rw [heq r hr, heq s hs]
    exact havg hr hs hrs
  refine ⟨hanti, ?_, ?_⟩
  · have hh := weighted_average_initial_limit
      (PolarDensityComparison.comparisonInterval_eventually k) (fun r hr => hr.1)
      (fun _ hr => comparison_down hr) ha ha1
      (sphericalAverage_initial_limit g hn hc C hC R hR k hk F hF p) hi hwi hwn hwp
    apply hh.congr'
    filter_upwards [PolarDensityComparison.comparisonInterval_eventually k] with r hr
    exact (heq r hr).symm
  · intro hkp
    let b := Real.pi / Real.sqrt k
    have hb : 0 < b := div_pos Real.pi_pos (Real.sqrt_pos.mpr hkp)
    have hnearb : ∀ᶠ r in 𝓝[<] b, r ∈ comparisonInterval k := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hb)] with r hr h0r
      exact ⟨h0r, fun _ => hr⟩
    have hmodb := model_ball_toReal hmodel hn hV b hb (fun _ => le_rfl)
    have hdenpos : 0 < (V b).toReal := by
      rw [hmodb]
      exact mul_pos (omega_pos g hn p) (weight_integral_pos n k b hb (fun _ => le_rfl))
    have hmodlim : Tendsto (fun r => (V r).toReal) (𝓝[<] b) (𝓝 (V b).toReal) := by
      rw [hmodb]
      have hh : Tendsto (fun r => (omega n).toReal *
          (∫ t in (0 : ℝ)..r, s k t ^ (n-1))) (𝓝[<] b)
          (𝓝 ((omega n).toReal * (∫ t in (0 : ℝ)..b, s k t ^ (n-1)))) :=
        tendsto_const_nhds.mul
          (((weight_integral_continuous n k).tendsto b).mono_left nhdsWithin_le_nhds)
      apply hh.congr'
      filter_upwards [hnearb] with r hr
      exact (model_ball_toReal hmodel hn hV r hr.1 (fun h => (hr.2 h).le)).symm
    have hnumlim := (ENNReal.tendsto_toReal (hfinite S g hc p b).ne).comp
      (hleft S g p b hb)
    have hlim : Tendsto (volumeRatio g p V) (𝓝[<] b) (𝓝 (volumeRatio g p V b)) :=
      hnumlim.div hmodlim hdenpos.ne'
    refine ⟨hlim, ?_⟩
    intro r hr
    apply le_of_tendsto hlim
    filter_upwards [hnearb,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds (hr.2 hkp))] with t ht hrt
    exact hanti hr ht hrt.le

end P202.Geometry.BishopGromov

universe v8_closure_b82e2e46eb4db970_u0
theorem _root_.«P202».«Geometry».«BishopGromov».«bishop_gromov» : _root_.«P202Specs».«Geometry».«BishopGromov».«bishop_gromovType».{v8_closure_b82e2e46eb4db970_u0} :=
  @_root_.«P202».«Geometry».«BishopGromov».«bishop_gromov_conditional».{v8_closure_b82e2e46eb4db970_u0} (@_root_.«P202».«Geometry».«PolarVolumeIntegration».«ball_integral».{v8_closure_b82e2e46eb4db970_u0}) (@_root_.«P202».«Geometry».«PolarVolumeIntegration».«ball_volume_finite».{v8_closure_b82e2e46eb4db970_u0}) (@_root_.«P202».«Geometry».«PolarVolumeIntegration».«ball_volume_left_limit».{v8_closure_b82e2e46eb4db970_u0}) (@_root_.«P202».«Geometry».«PolarVolumeIntegration».«model_volume»)
