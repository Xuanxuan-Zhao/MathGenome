import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.MaximalStrongBoundsAndDifferentiation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.MaximalWeakBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.Marcinkiewicz
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
Strong maximal bounds and Lebesgue differentiation, paper.tex:18180–18210.
The adopted `20261105-maximal-dimension-errata` restricts only strong L¹
failure to positive dimension; the affirmative bounds and differentiation
below retain every natural dimension, including zero.
Finite truncations of the extended maximal function satisfy the accepted
Marcinkiewicz distribution estimate, uniformly in the truncation. Monotone
convergence gives the extended pth moment estimate; a.e. finiteness and the
ordinary real Lᵖ representative follow afterwards. The unit-ball indicator's
tail has divergent radial integral. Differentiation uses Mathlib's locally
integrable Vitali theorem and the nullity of positive-radius spheres.
-/
noncomputable section
open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology
universe v

namespace ExpandedFA.SingularIntegrals

/-- Passing between open and closed balls is legitimate also in dimension
zero, since the radii used here are positive. -/
lemma ball_ae_closedBall (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ball x r =ᵐ[volume] closedBall x r := by
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr ball_subset_closedBall]
    exact measure_empty
  · rw [closedBall_sdiff_ball]
    exact Measure.addHaar_sphere_of_ne_zero volume x hr.ne'

theorem lebesgue_differentiation :
    MaximalStrongBoundsAndDifferentiationSpec.LebesgueDifferentiation.{v} := by
  intro d F _ f hf
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hf 1] with x hx
  have h := hx (fun _ : ℝ => x) id tendsto_id
    (by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mem_closedBall_self (by simpa using hr.le))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [setAverage_eq, smul_eq_mul]
  rw [Measure.restrict_congr_set (ball_ae_closedBall d x hr),
    show volume.real (ball x r) = volume.real (closedBall x r) from
      congrArg ENNReal.toReal (measure_congr (ball_ae_closedBall d x hr))]
  rfl

theorem centeredMaximal_strong_infinity :
    MaximalStrongBoundsAndDifferentiationSpec.InfinityStrongBound.{v} :=
  centeredMaximal_infinity

/-- Subadditivity holds before any finiteness assertion. -/
lemma centeredMaximal_add_le {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f g : EuclideanSpace ℝ (Fin d) → F)
    (hf : AEStronglyMeasurable f volume) (_hg : AEStronglyMeasurable g volume)
    (x : EuclideanSpace ℝ (Fin d)) :
    centeredMaximal volume (f + g) x ≤ centeredMaximal volume f x + centeredMaximal volume g x := by
  dsimp only [centeredMaximal]
  apply iSup_le fun r => iSup_le fun hr => ?_
  calc
    _ ≤ ((∫⁻ y in ball x r, ‖f y‖ₑ) + ∫⁻ y in ball x r, ‖g y‖ₑ) / volume (ball x r) := by
      apply ENNReal.div_le_div_right
      exact (lintegral_mono fun y => enorm_add_le _ _).trans_eq
        (lintegral_add_left' hf.enorm.restrict _)
    _ = (∫⁻ y in ball x r, ‖f y‖ₑ) / volume (ball x r) +
        (∫⁻ y in ball x r, ‖g y‖ₑ) / volume (ball x r) := ENNReal.add_div
    _ ≤ centeredMaximal volume f x + centeredMaximal volume g x := by
      apply add_le_add
      · exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      · exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)

open MaximalStrongBoundsAndDifferentiationSpec in
theorem centeredMaximal_indicator_ball_tail :
    MaximalStrongBoundsAndDifferentiationSpec.IndicatorBallTail := by
  intro d x hx
  have hn : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hr : 0 < 2 * ‖x‖ := mul_pos (by norm_num) hn
  have hsub : ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ ball x (2 * ‖x‖) := by
    intro y hy
    have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    apply mem_ball.mpr
    calc
      dist y x ≤ ‖y‖ + ‖x‖ := dist_le_norm_add_norm _ _
      _ < 2 * ‖x‖ := by linarith
  have hint : (∫⁻ y in ball x (2 * ‖x‖), ‖unitBallIndicator d y‖ₑ) =
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    have heq : (fun y => ‖unitBallIndicator d y‖ₑ) =
        (ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext y
      classical
      by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 <;>
        simp [unitBallIndicator, hy]
    rw [heq, setLIntegral_indicator measurableSet_ball, inter_eq_left.mpr hsub]
    simp
  have hratio : (∫⁻ y in ball x (2 * ‖x‖), ‖unitBallIndicator d y‖ₑ) /
      volume (ball x (2 * ‖x‖)) = (ENNReal.ofReal (2 * ‖x‖) ^ d)⁻¹ := by
    rw [hint, volume.addHaar_ball_of_pos x hr]
    simp only [finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le]
    have hV0 := (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d))
      (by norm_num : (0 : ℝ) < 1)).ne'
    have hVt : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ∞ := measure_ball_lt_top.ne
    simpa using ENNReal.mul_div_mul_right 1 (ENNReal.ofReal (2 * ‖x‖) ^ d) hV0 hVt
  rw [← hratio]
  exact le_iSup_of_le (2 * ‖x‖) (le_iSup_of_le hr le_rfl)

/-- A finite truncation used only to establish extended moment bounds. -/
def finiteCap {X : Type*} (u : X → ℝ≥0∞) (n : ℕ) (x : X) : ℝ :=
  (min (u x) (n : ℝ≥0∞)).toReal

lemma enorm_finiteCap {X : Type*} (u : X → ℝ≥0∞) (n : ℕ) (x : X) :
    ‖finiteCap u n x‖ₑ = min (u x) (n : ℝ≥0∞) := by
  dsimp only [finiteCap]
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)

open Interpolation Interpolation.MarcinkiewiczSpec in
lemma centeredMaximal_cap_distribution {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    {p : ℝ} (hp : 1 < p) (f : EuclideanSpace ℝ (Fin d) → F)
    (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    distribution volume (finiteCap (centeredMaximal volume f) n) t ≤
      ENNReal.ofReal (t / 2) ^ (-(1 : ℝ)) * ((5 : ℝ≥0) ^ d : ℝ≥0∞) ^ (1 : ℝ) *
        (∫⁻ x, ‖highPart (infinityTruncationScale 1 * t) f x‖ₑ ^ (1 : ℝ)) := by
  let a := infinityTruncationScale 1 * t
  have ha : 0 < a := mul_pos (infinityTruncationScale_pos 1) ht
  have hh : Integrable (highPart a f) volume := by
    have := highPart_memLp ha zero_lt_one hp.le hf
    simpa using (memLp_one_iff_integrable.mp (by simpa using this))
  have hl : MemLp (lowPart a f) ∞ volume :=
    (lowPart_eLpNorm_top_le hf.aestronglyMeasurable ha.le).trans_lt ENNReal.ofReal_lt_top
  have hsmall : a ≤ t / 2 := by
    simpa [a] using infinityTruncationScale_small (1 : ℝ≥0) ht
  have hsub : {x | t < ‖finiteCap (centeredMaximal volume f) n x‖} ⊆
      {x | ENNReal.ofReal (t / 2) < centeredMaximal volume (highPart a f) x} := by
    intro x hx
    have htx : ENNReal.ofReal t < centeredMaximal volume f x := by
      have h := ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le |>.mpr hx
      rw [ofReal_norm, enorm_finiteCap] at h
      exact h.trans_le (min_le_left _ _)
    have hsum := centeredMaximal_add_le (highPart a f) (lowPart a f)
      hh.aestronglyMeasurable hl.aestronglyMeasurable x
    rw [highPart_add_lowPart] at hsum
    have hlo : centeredMaximal volume (lowPart a f) x ≤ ENNReal.ofReal (t / 2) :=
      (centeredMaximal_infinity_pointwise d _ hl x).trans
        ((lowPart_eLpNorm_top_le hf.aestronglyMeasurable ha.le).trans
          (ENNReal.ofReal_le_ofReal hsmall))
    change ENNReal.ofReal (t / 2) < centeredMaximal volume (highPart a f) x
    by_contra! hbad
    have hbound := hsum.trans (add_le_add hbad hlo)
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t / 2) (by positivity : 0 ≤ t / 2)] at hbound
    have heq : t / 2 + t / 2 = t := by ring
    rw [heq] at hbound
    exact (not_le_of_gt htx) hbound
  have hw := (measure_mono hsub).trans (centeredMaximal_weak d _ hh (t / 2) (by positivity))
  rw [ofReal_integral_norm_eq_lintegral_enorm hh] at hw
  simpa only [a, distribution, ENNReal.rpow_neg_one, ENNReal.rpow_one, ENNReal.coe_pow,
    ENNReal.coe_ofNat, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hw

open Interpolation in
lemma centeredMaximal_moment_le {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    {p : ℝ} (hp : 1 < p) (f : EuclideanSpace ℝ (Fin d) → F)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, centeredMaximal volume f x ^ p) ≤
      ((infinityInterpolationConstant 1 p ((5 : ℝ≥0) ^ d) 1 : ℝ≥0∞) *
        eLpNorm f (ENNReal.ofReal p) volume) ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hm : Measurable (centeredMaximal volume f) := centeredMaximal_measurable d f
  have hcap (n : ℕ) :
      (∫⁻ x, min (centeredMaximal volume f x) (n : ℝ≥0∞) ^ p) ≤
        ((infinityInterpolationConstant 1 p ((5 : ℝ≥0) ^ d) 1 : ℝ≥0∞) *
          eLpNorm f (ENNReal.ofReal p) volume) ^ p := by
    have hc : AEStronglyMeasurable (finiteCap (centeredMaximal volume f) n) volume :=
      (hm.min measurable_const).ennreal_toReal.aestronglyMeasurable
    have hb := strongType_of_distribution_truncation_bound_top zero_lt_one hp hf hc
      ((5 : ℝ≥0) ^ d) 1 (centeredMaximal_cap_distribution hp f hf n)
    have he := eLpNorm_ofReal_rpow hc hp0
    simp_rw [enorm_finiteCap] at he
    rw [← he]
    exact ENNReal.rpow_le_rpow hb.2 hp0.le
  have heq (x : EuclideanSpace ℝ (Fin d)) :
      centeredMaximal volume f x ^ p =
        ⨆ n : ℕ, min (centeredMaximal volume f x) (n : ℝ≥0∞) ^ p := by
    have hs : (⨆ n : ℕ, min (centeredMaximal volume f x) (n : ℝ≥0∞)) =
        centeredMaximal volume f x := by
      simp only [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    simpa only [ENNReal.orderIsoRpow_apply, hs] using
      (ENNReal.orderIsoRpow p hp0).map_iSup
        (fun n : ℕ => min (centeredMaximal volume f x) (n : ℝ≥0∞))
  simp_rw [heq]
  rw [lintegral_iSup]
  · exact iSup_le hcap
  · intro n
    exact (hm.min measurable_const).pow_const p
  · intro m n hmn x
    exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hmn)) hp0.le

open Interpolation in
theorem centeredMaximal_strong_finite :
    MaximalStrongBoundsAndDifferentiationSpec.FiniteStrongBound.{v} := by
  intro d p hp
  refine ⟨infinityInterpolationConstant 1 p ((5 : ℝ≥0) ^ d) 1, ?_⟩
  intro F _ f hf
  have hb := ENNReal.rpow_le_rpow (centeredMaximal_moment_le hp f hf)
    (show 0 ≤ 1 / p by positivity)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel (zero_lt_one.trans hp).ne', ENNReal.rpow_one] at hb

theorem centeredMaximal_strong_membership :
    MaximalStrongBoundsAndDifferentiationSpec.FiniteStrongMembership.{v} := by
  intro d p hp
  obtain ⟨C, hC⟩ := centeredMaximal_strong_finite d p hp
  refine ⟨C, ?_⟩
  intro F _ f hf
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hb := hC f hf
  have hbound : (∫⁻ x, centeredMaximal volume f x ^ p) ^ (1 / p) < ∞ :=
    hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf)
  have hint : (∫⁻ x, centeredMaximal volume f x ^ p) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hp0)).mp hbound
  have hm : Measurable (centeredMaximal volume f) := centeredMaximal_measurable d f
  have hfinite : ∀ᵐ x ∂volume, centeredMaximal volume f x < ∞ := by
    filter_upwards [ae_lt_top (hm.pow_const p) hint.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx
  have hg : AEStronglyMeasurable (fun x => (centeredMaximal volume f x).toReal) volume :=
    hm.ennreal_toReal.aestronglyMeasurable
  have heq : eLpNorm (fun x => (centeredMaximal volume f x).toReal) (ENNReal.ofReal p) volume =
      (∫⁻ x, centeredMaximal volume f x ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hg,
      ENNReal.toReal_ofReal hp0.le]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfinite] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hx.ne]
  refine ⟨hfinite, ?_, ?_⟩
  · exact heq.trans_lt hbound
  · exact heq.trans_le hb

/-- The radial tail has divergent logarithmic integral in positive dimension. -/
lemma radial_tail_not_integrable (d : ℕ) (hd : 0 < d) :
    ¬ Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (Ioi (1 : ℝ)).indicator (fun r => ((2 * r) ^ d)⁻¹) ‖x‖) volume := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  intro h
  have hi : IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      (Ioi (1 : ℝ)).indicator (fun r => ((2 * r) ^ d)⁻¹) r) (Ioi 0) := by
    simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
      (integrable_fun_norm_addHaar volume).mp h
  have hi' := (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).const_mul
    ((2 : ℝ) ^ d)
  apply not_integrableOn_Ioi_inv (a := 1)
  apply IntegrableOn.congr_fun hi' _ measurableSet_Ioi
  intro r (hr : 1 < r)
  simp only [mem_Ioi, hr, indicator_of_mem]
  have hp : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [mul_pow, hp]
  field_simp

open MaximalStrongBoundsAndDifferentiationSpec in
theorem centeredMaximal_not_strong_one :
    MaximalStrongBoundsAndDifferentiationSpec.NotStrongOne := by
  intro d hd
  have hi : Integrable (unitBallIndicator d) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_const measure_ball_lt_top.ne)
  refine ⟨hi, ?_⟩
  by_contra hfin
  let q : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun r => ((2 * r) ^ d)⁻¹)
  have hqm : Measurable (fun x : EuclideanSpace ℝ (Fin d) => q ‖x‖) := by
    exact ((measurable_const.mul measurable_id).pow_const d).inv.indicator measurableSet_Ioi
      |>.comp continuous_norm.measurable
  have hM : Measurable (centeredMaximal volume (unitBallIndicator d)) :=
    centeredMaximal_measurable d _
  have hMt : ∀ᵐ x ∂volume, centeredMaximal volume (unitBallIndicator d) x < ∞ :=
    ae_lt_top hM hfin
  have hMi : Integrable (fun x => (centeredMaximal volume (unitBallIndicator d) x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hM.aemeasurable hfin
  apply radial_tail_not_integrable d hd
  apply hMi.mono' hqm.aestronglyMeasurable
  filter_upwards [hMt] with x hx
  have hq0 : 0 ≤ q ‖x‖ := by
    apply indicator_nonneg
    intro r hr
    have hr0 : 0 ≤ r := (zero_lt_one.trans hr).le
    exact inv_nonneg.mpr (pow_nonneg (mul_nonneg (by norm_num) hr0) d)
  rw [Real.norm_eq_abs, abs_of_nonneg hq0]
  apply (ENNReal.ofReal_le_iff_le_toReal hx.ne).mp
  by_cases hxn : 1 < ‖x‖
  · have hb := centeredMaximal_indicator_ball_tail d x hxn.le
    change (ENNReal.ofReal (2 * ‖x‖) ^ d)⁻¹ ≤ centeredMaximal volume (unitBallIndicator d) x at hb
    simpa only [q, mem_Ioi, hxn, indicator_of_mem,
      ENNReal.ofReal_inv_of_pos (pow_pos (by positivity : 0 < 2 * ‖x‖) d),
      ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * ‖x‖)] using hb
  · simp [q, hxn]

end ExpandedFA.SingularIntegrals
