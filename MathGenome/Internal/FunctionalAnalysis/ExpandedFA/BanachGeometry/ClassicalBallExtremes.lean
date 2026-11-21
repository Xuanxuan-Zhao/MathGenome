import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.ClassicalBallExtremes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachGeometry.SequenceBallExtremes
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
universe u
namespace ExpandedFA.BanachGeometry.ClassicalBallExtremes

theorem sequence_ball_extremes : Spec.SequenceExtremes.{u} :=
  ⟨SequenceBallExtremes.infinity_ball_extremes,
   SequenceBallExtremes.convergent_ball_extremes,
   SequenceBallExtremes.c0_ball_no_extremes,
   SequenceBallExtremes.l1_ball_extremes,
   SequenceBallExtremes.lp_ball_extremes,
   SequenceBallExtremes.real_infinity_ball_extremes,
   SequenceBallExtremes.real_convergent_ball_extremes,
   SequenceBallExtremes.real_l1_ball_extremes⟩

/-- A continuous cumulative integral for a measure with null singletons.
On the real line this gives the genuine nonatomic splitting step. -/
lemma exists_half_integral {μ : Measure ℝ} [NullSingletonClass μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) (h : ∫ x, f x ∂μ = 1) :
    ∃ t : ℝ, ∫ x in Iic t, f x ∂μ = (1 / 2 : ℝ) := by
  let F : ℝ → ℝ := fun t => ∫ x in Iic t, f x ∂μ
  have hF : Continuous F := by
    have heq : F = fun t => F 0 + ∫ x in (0 : ℝ)..t, f x ∂μ := by
      funext t
      have ht := intervalIntegral.integral_Iic_sub_Iic
        (hf.integrableOn (s := Iic 0)) (hf.integrableOn (s := Iic t))
      dsimp [F]
      linarith
    rw [heq]
    exact continuous_const.add (hf.continuous_primitive 0)
  have hbot : Tendsto F atBot (𝓝 0) := tendsto_integral_Iic_zero tendsto_id
  have htop : Tendsto F atTop (𝓝 1) := by
    simpa [F, h] using
      (aecover_Iic (μ := μ) tendsto_id).integral_tendsto_of_countably_generated hf
  obtain ⟨t, _, ht⟩ := isPreconnected_univ.intermediate_value_Ioo
    (show (atBot : Filter ℝ) ≤ 𝓟 univ by simp)
    (show (atTop : Filter ℝ) ≤ 𝓟 univ by simp)
    hF.continuousOn hbot htop (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  exact ⟨t, ht⟩

/-- Restriction to a measurable set, still in the original L¹ space. -/
def restrictL1 {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : Lp E 1 μ) : Lp E 1 μ :=
  ((L1.integrable_coeFn f).indicator hs).toL1 (s.indicator f)

lemma norm_restrictL1 {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : Lp E 1 μ) :
    ‖restrictL1 s hs f‖ = ∫ x in s, ‖f x‖ ∂μ := by
  rw [restrictL1, L1.norm_of_fun_eq_integral_norm]
  simp_rw [norm_indicator_eq_indicator_norm]
  exact integral_indicator hs

lemma restrictL1_add_compl {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : Lp E 1 μ) :
    restrictL1 s hs f + restrictL1 sᶜ hs.compl f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (restrictL1 s hs f) (restrictL1 sᶜ hs.compl f),
    ((L1.integrable_coeFn f).indicator hs).coeFn_toL1,
    ((L1.integrable_coeFn f).indicator hs.compl).coeFn_toL1] with x hx ha hb
  change restrictL1 s hs f x = s.indicator f x at ha
  change restrictL1 sᶜ hs.compl f x = sᶜ.indicator f x at hb
  rw [hx, Pi.add_apply, ha, hb]
  by_cases hxs : x ∈ s <;> simp [hxs]


/-- Lebesgue L¹ has no extreme unit-ball points, over ℝ or ℂ.
A half-integral cut yields two disjoint restrictions, each of norm 1/2;
their doubles are distinct unit vectors with midpoint the given vector. -/
theorem lebesgue_l1_ball_no_extremes : Spec.LebesgueL1NoExtremes.{u} := by
  intro 𝕜 _
  let u : Lp 𝕜 1 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc (0 : ℝ) 1) 1 measurableSet_Icc (by simp [Real.volume_Icc]) (1 : 𝕜)
  have hu : ‖u‖ = 1 := by
    simp [u, norm_indicatorConstLp, Real.volume_real_Icc]
  have : Nontrivial (Lp 𝕜 1 (volume : Measure ℝ)) :=
    nontrivial_of_ne u 0 (by intro h; simp [h] at hu)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  have hnorm : ‖f‖ = 1 := by
    simpa using extremePoints_closedBall_subset_sphere hf
  have hfi := L1.integrable_coeFn f
  obtain ⟨t, ht⟩ := exists_half_integral hfi.norm
    ((L1.norm_eq_integral_norm f).symm.trans hnorm)
  let s := Iic t
  have hs : MeasurableSet s := measurableSet_Iic
  let a := restrictL1 s hs f
  let b := restrictL1 sᶜ hs.compl f
  have hab : a + b = f := restrictL1_add_compl s hs f
  have ha : ‖a‖ = (1 / 2 : ℝ) := (norm_restrictL1 s hs f).trans ht
  have hb : ‖b‖ = (1 / 2 : ℝ) := by
    rw [norm_restrictL1]
    have hsplit := integral_add_compl hs hfi.norm
    have htotal : ∫ x, ‖f x‖ = 1 := (L1.norm_eq_integral_norm f).symm.trans hnorm
    change (∫ x in s, ‖f x‖) = (1 / 2 : ℝ) at ht
    linarith
  have hna : ‖(2 : ℝ) • a‖ = 1 := by rw [norm_smul, ha]; norm_num
  have hnb : ‖(2 : ℝ) • b‖ = 1 := by rw [norm_smul, hb]; norm_num
  have hseg : f ∈ openSegment ℝ ((2 : ℝ) • a) ((2 : ℝ) • b) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] using hab
  have he : (2 : ℝ) • a = f := hf.2 (by simpa using hna.le) (by simpa using hnb.le) hseg
  have heab : a = b := by
    apply add_left_cancel (a := a)
    calc
      a + a = (2 : ℝ) • a := (two_smul ℝ a).symm
      _ = f := he
      _ = a + b := hab.symm
  have ha0 : a = 0 := by
    apply Lp.ext
    have hae := ((L1.integrable_coeFn f).indicator hs).coeFn_toL1
    have hbe := ((L1.integrable_coeFn f).indicator hs.compl).coeFn_toL1
    change a =ᵐ[volume] s.indicator f at hae
    change b =ᵐ[volume] sᶜ.indicator f at hbe
    filter_upwards [hae, hbe, Lp.coeFn_zero 𝕜 1 (volume : Measure ℝ)] with x hax hbx hzx
    rw [hzx]
    by_cases hxs : x ∈ s
    · rw [heab, hbx]
      simp [hxs]
    · rw [hax]
      simp [hxs]
  rw [ha0, norm_zero] at ha
  norm_num at ha

end ExpandedFA.BanachGeometry.ClassicalBallExtremes
