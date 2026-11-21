import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularCornerRounding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Complex MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace D12Complex.CircularCornerRounding

lemma hasDerivAt_smoothStep (t : ℝ) :
    HasDerivAt smoothStep (6 * t * (1 - t)) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul 3).sub
    (((hasDerivAt_id t).pow 3).const_mul 2) using 1 <;>
    simp [smoothStep, funext_iff] <;> ring

@[simp] lemma smoothStep_zero : smoothStep 0 = 0 := by norm_num [smoothStep]
@[simp] lemma smoothStep_one : smoothStep 1 = 1 := by norm_num [smoothStep]

lemma contDiff_smoothStep : ContDiff ℝ ∞ smoothStep := by
  unfold smoothStep
  fun_prop

lemma smoothStep_strictMonoOn : StrictMonoOn smoothStep (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) contDiff_smoothStep.continuous.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_smoothStep t).deriv]
  exact mul_pos (mul_pos (by norm_num) ht.1) (sub_pos.mpr ht.2)

lemma smoothStep_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    smoothStep t ∈ Icc (0 : ℝ) 1 := by
  have h0 := smoothStep_strictMonoOn.monotoneOn (by simp) ht ht.1
  have h1 := smoothStep_strictMonoOn.monotoneOn ht (by simp) ht.2
  simpa only [mem_Icc, mem_Ioo, smoothStep_zero, smoothStep_one] using And.intro h0 h1

lemma smoothStep_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    smoothStep t ∈ Ioo (0 : ℝ) 1 := by
  have h0 := smoothStep_strictMonoOn (by simp) (Ioo_subset_Icc_self ht) ht.1
  have h1 := smoothStep_strictMonoOn (Ioo_subset_Icc_self ht) (by simp) ht.2
  simpa only [mem_Icc, mem_Ioo, smoothStep_zero, smoothStep_one] using And.intro h0 h1

lemma radialProfile_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 2 ≤ radialProfile t ∧ radialProfile t ≤ 1 := by
  have hs : 0 ≤ Real.sin (Real.pi * t) := Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le ht.1) (by simpa using mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le)
  have hs' := Real.sin_le_one (Real.pi * t)
  dsimp [radialProfile]
  constructor <;> linarith

lemma radialProfile_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < radialProfile t := lt_of_lt_of_le (by norm_num) (radialProfile_bounds ht).1

lemma hasDerivAt_radialProfile (t : ℝ) :
    HasDerivAt radialProfile (-(Real.pi / 2) * Real.cos (Real.pi * t)) t := by
  convert (hasDerivAt_const t (1 : ℝ)).sub
    ((((hasDerivAt_id t).const_mul Real.pi).sin).div_const 2) using 1 <;>
    simp [radialProfile, funext_iff, div_eq_mul_inv] <;> ring

lemma contDiff_radialProfile : ContDiff ℝ ∞ radialProfile := by
  unfold radialProfile
  fun_prop

lemma norm_roundingArc {ε θ t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖roundingArc ε θ t‖ = ε * radialProfile t := by
  simp only [roundingArc, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hε, abs_of_pos (radialProfile_pos ht)]

lemma roundingArc_endpoints (ε θ : ℝ) :
    roundingArc ε θ 0 = (ε : ℂ) ∧
    roundingArc ε θ 1 = (ε : ℂ) * Complex.exp ((θ : ℂ) * I) := by
  constructor <;> simp [roundingArc, radialProfile]

lemma contDiff_roundingArc (ε θ : ℝ) : ContDiff ℝ ∞ (roundingArc ε θ) := by
  unfold roundingArc
  have hr : ContDiff ℝ ∞ (fun t : ℝ => ((ε * radialProfile t : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_radialProfile)
  have hs : ContDiff ℝ ∞ (fun t : ℝ => ((θ * smoothStep t : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_smoothStep)
  exact hr.mul (Complex.contDiff_exp.comp (hs.mul contDiff_const))

lemma hasDerivAt_roundingArc (ε θ t : ℝ) :
    HasDerivAt (roundingArc ε θ) (roundingVelocity ε θ t) t := by
  have hr := ((hasDerivAt_radialProfile t).const_mul ε).ofReal_comp
  have ha := (((hasDerivAt_smoothStep t).const_mul θ).ofReal_comp.mul_const I).cexp
  convert hr.mul ha using 1 <;>
    simp [roundingArc, roundingVelocity, funext_iff] <;> ring

lemma roundingArc_mem_sector {ε θ t : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : roundingArc ε θ t ∈ CircularExhaustion.sector θ := by
  have hs := smoothStep_mem_Ioo ht
  refine ⟨ε * radialProfile t, θ * smoothStep t,
    mul_pos hε (radialProfile_pos (Ioo_subset_Icc_self ht)), mul_pos hθ hs.1, ?_, rfl⟩
  simpa using mul_lt_mul_of_pos_left hs.2 hθ

lemma roundingArc_injOn {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) : InjOn (roundingArc ε θ) (Icc (0 : ℝ) 1) := by
  intro s hs t ht h
  have hr : ε * radialProfile s = ε * radialProfile t := by
    simpa only [norm_roundingArc hε.le hs, norm_roundingArc hε.le ht] using congrArg norm h
  have he : Complex.exp ((θ * smoothStep s : ℝ) * I) =
      Complex.exp ((θ * smoothStep t : ℝ) * I) := by
    unfold roundingArc at h
    rw [← hr] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
      (mul_pos hε (radialProfile_pos hs)).ne') h
  have hs' := smoothStep_mem_Icc hs
  have ht' := smoothStep_mem_Icc ht
  have ha : θ * smoothStep s = θ * smoothStep t := by
    apply eq_of_circleMap_eq (R := 1) (c := 0) (by norm_num) _
      (by simpa [circleMap] using he)
    rw [abs_lt]
    constructor <;> nlinarith [hs'.1, hs'.2, ht'.1, ht'.2]
  exact smoothStep_strictMonoOn.injOn hs ht (mul_left_cancel₀ hθ.ne' ha)

lemma roundingArc_deriv_endpoints (ε θ : ℝ) :
    deriv (roundingArc ε θ) 0 = (-(ε * Real.pi / 2) : ℝ) ∧
    deriv (roundingArc ε θ) 1 = (ε * Real.pi / 2 : ℝ) *
      Complex.exp ((θ : ℂ) * I) := by
  rw [(hasDerivAt_roundingArc ε θ 0).deriv, (hasDerivAt_roundingArc ε θ 1).deriv]
  constructor <;> simp [roundingVelocity, radialProfile]

lemma roundingArc_regular {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : deriv (roundingArc ε θ) t ≠ 0 := by
  by_cases h0 : t = 0
  · subst t
    rw [(roundingArc_deriv_endpoints ε θ).1]
    exact Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr (by positivity))
  by_cases h1 : t = 1
  · subst t
    rw [(roundingArc_deriv_endpoints ε θ).2]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Complex.exp_ne_zero _)
  rw [(hasDerivAt_roundingArc ε θ t).deriv, roundingVelocity]
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
    Complex.ofReal_re, zero_add, Complex.zero_im] at him
  have hp : 0 < ε * radialProfile t * (θ * (6 * t * (1 - t))) := by
    apply mul_pos (mul_pos hε (radialProfile_pos ht))
    exact mul_pos hθ (mul_pos (mul_pos (by norm_num) (lt_of_le_of_ne ht.1 (Ne.symm h0)))
      (sub_pos.mpr (lt_of_le_of_ne ht.2 h1)))
  exact hp.ne' him

lemma norm_deriv_roundingArc_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv (roundingArc ε θ) t‖ ≤ (Real.pi / 2 + 6 * θ) * ε := by
  have hr := radialProfile_bounds ht
  have ht' : 0 ≤ t * (1 - t) ∧ t * (1 - t) ≤ 1 := by
    constructor
    · exact mul_nonneg ht.1 (by linarith [ht.2])
    · nlinarith [sq_nonneg t]
  have hb0 : 0 ≤ ε * radialProfile t * (θ * (6 * t * (1 - t))) := by
    exact mul_nonneg (mul_nonneg hε.le (radialProfile_pos ht).le)
      (mul_nonneg hθ.le (by nlinarith [ht'.1]))
  have hb : ε * radialProfile t * (θ * (6 * t * (1 - t))) ≤ ε * (6 * θ) := by
    calc
      _ ≤ ε * radialProfile t * (6 * θ) := mul_le_mul_of_nonneg_left
        (by nlinarith [ht'.2]) (mul_nonneg hε.le (radialProfile_pos ht).le)
      _ ≤ ε * (6 * θ) := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hr.2)]
  have ha : |-(ε * Real.pi / 2) * Real.cos (Real.pi * t)| ≤ ε * Real.pi / 2 := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < ε * Real.pi / 2)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  rw [(hasDerivAt_roundingArc ε θ t).deriv, roundingVelocity, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  calc
    _ ≤ |((( -(ε * Real.pi / 2) * Real.cos (Real.pi * t) : ℝ) : ℂ) +
        ((ε * radialProfile t * (θ * (6 * t * (1 - t))) : ℝ) : ℂ) * I).re| +
        |((( -(ε * Real.pi / 2) * Real.cos (Real.pi * t) : ℝ) : ℂ) +
        ((ε * radialProfile t * (θ * (6 * t * (1 - t))) : ℝ) : ℂ) * I).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |-(ε * Real.pi / 2) * Real.cos (Real.pi * t)| +
        ε * radialProfile t * (θ * (6 * t * (1 - t))) := by
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add, abs_of_nonneg hb0]
    _ ≤ (Real.pi / 2 + 6 * θ) * ε := by nlinarith

lemma roundingArc_length_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (roundingArc ε θ) t‖) ≤
      (Real.pi / 2 + 6 * θ) * ε := by
  have hc : Continuous (fun t => ‖deriv (roundingArc ε θ) t‖) :=
    ((contDiff_roundingArc ε θ).continuous_deriv (by simp)).norm
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (hc.intervalIntegrable (μ := volume) 0 1) (intervalIntegrable_const (c := (Real.pi / 2 + 6 * θ) * ε))
    (fun t ht => norm_deriv_roundingArc_le hε hθ ht)
  simpa using hi

/-- The explicit curve construction is established without any domain certificate. -/
theorem rounding_arc : Specs.D12Complex.Ch14.CircularCornerRounding.rounding_arc_type := by
  intro ε θ hε hθ hθ'
  refine ⟨contDiff_roundingArc ε θ, (roundingArc_endpoints ε θ).1,
    (roundingArc_endpoints ε θ).2, ?_, ?_, roundingArc_injOn hε hθ hθ',
    hasDerivAt_roundingArc ε θ, ?_, (roundingArc_deriv_endpoints ε θ).1,
    (roundingArc_deriv_endpoints ε θ).2, ?_, roundingArc_length_le hε hθ⟩
  · intro t ht
    rw [norm_roundingArc hε.le ht]
    have hr := radialProfile_bounds ht
    constructor <;> nlinarith [hr.1, hr.2]
  · exact fun t ht => roundingArc_mem_sector hε hθ ht
  · exact fun t ht => roundingArc_regular hε hθ ht
  · exact fun t ht => norm_deriv_roundingArc_le hε hθ ht

/-- C1 gluing on a half-line, proved from the two one-sided derivatives rather
than a pictorial tangent assertion. -/
lemma hasDerivAt_piecewise_Iic {f g : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (deriv f x) x)
    (hg : ∀ x, HasDerivAt g (deriv g x) x)
    (hv : f a = g a) (hd : deriv f a = deriv g a) (x : ℝ) :
    HasDerivAt ((Iic a).piecewise f g) ((Iic a).piecewise (deriv f) (deriv g) x) x := by
  classical
  rcases lt_trichotomy x a with hx | rfl | hx
  · simp only [piecewise, mem_Iic, hx.le, ite_true]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [(show y < a from hy).le]
  · simp only [piecewise, mem_Iic, le_refl, ite_true]
    have hl : HasDerivWithinAt ((Iic x).piecewise f g) (deriv f x) (Iic x) x :=
      (hf x).hasDerivWithinAt.congr_of_mem (fun y hy => by simp [hy]) (by simp)
    have hr : HasDerivWithinAt ((Iic x).piecewise f g) (deriv f x) (Ici x) x := by
      rw [hd]
      apply (hg x).hasDerivWithinAt.congr_of_mem _ (by simp)
      intro y hy
      rcases eq_or_lt_of_le (show x ≤ y from hy) with rfl | hxy
      · simpa using hv
      · simp [not_le.mpr hxy]
    have hu := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hu
    exact hu
  · simp only [piecewise, mem_Iic, not_le.mpr hx, ite_false]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [not_le.mpr (show a < y from hy)]

lemma contDiff_piecewise_Iic {f g : ℝ → ℂ} {a : ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hv : f a = g a) (hd : deriv f a = deriv g a) :
    ContDiff ℝ 1 ((Iic a).piecewise f g) := by
  classical
  have hh := hasDerivAt_piecewise_Iic
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hg.differentiable (by norm_num) x).hasDerivAt) hv hd
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hh x).differentiableAt, ?_⟩
  have he : deriv ((Iic a).piecewise f g) = (Iic a).piecewise (deriv f) (deriv g) := by
    funext x
    exact (hh x).deriv
  rw [he]
  apply Continuous.piecewise _ hf.continuous_deriv_one hg.continuous_deriv_one
  intro x hx
  have : x = a := by simpa only [frontier_Iic, mem_singleton_iff] using hx
  simpa [this] using hd

lemma hasDerivAt_bottomRay (ε t : ℝ) :
    HasDerivAt (bottomRay ε) (-(ε * Real.pi / 2) : ℝ) t := by
  convert ((hasDerivAt_const t ε).sub
    ((hasDerivAt_id t).const_mul (ε * Real.pi / 2))).ofReal_comp using 1 <;>
    simp [bottomRay, funext_iff]

lemma hasDerivAt_topRay (ε θ t : ℝ) :
    HasDerivAt (topRay ε θ) ((ε * Real.pi / 2 : ℝ) *
      Complex.exp ((θ : ℂ) * I)) t := by
  convert (((hasDerivAt_const t ε).add
      (((hasDerivAt_id t).sub_const 1).const_mul (ε * Real.pi / 2))).ofReal_comp).mul_const
        (Complex.exp ((θ : ℂ) * I)) using 1 <;>
    simp [topRay, funext_iff]

lemma contDiff_bottomRay (ε : ℝ) : ContDiff ℝ 1 (bottomRay ε) := by
  have hc : ContDiff ℝ 1 (fun t : ℝ => ε - (ε * Real.pi / 2) * t) := by fun_prop
  exact ofRealCLM.contDiff.comp hc

lemma contDiff_topRay (ε θ : ℝ) : ContDiff ℝ 1 (topRay ε θ) := by
  have hc : ContDiff ℝ 1 (fun t : ℝ => ε + (ε * Real.pi / 2) * (t - 1)) := by fun_prop
  exact (ofRealCLM.contDiff.comp hc).mul contDiff_const

lemma contDiff_joinedRounding (ε θ : ℝ) : ContDiff ℝ 1 (joinedRounding ε θ) := by
  classical
  have hi : ContDiff ℝ 1 ((Iic (1 : ℝ)).piecewise (roundingArc ε θ) (topRay ε θ)) := by
    apply contDiff_piecewise_Iic ((contDiff_roundingArc ε θ).of_le (by simp))
      (contDiff_topRay ε θ)
    · simpa [topRay] using (roundingArc_endpoints ε θ).2
    · rw [(roundingArc_deriv_endpoints ε θ).2, (hasDerivAt_topRay ε θ 1).deriv]
  unfold joinedRounding
  apply contDiff_piecewise_Iic (contDiff_bottomRay ε) hi
  · simpa [bottomRay] using (roundingArc_endpoints ε θ).1.symm
  · rw [(hasDerivAt_bottomRay ε 0).deriv]
    have h := hasDerivAt_piecewise_Iic (a := 1)
      (fun t => (hasDerivAt_roundingArc ε θ t).differentiableAt.hasDerivAt)
      (fun t => (hasDerivAt_topRay ε θ t).differentiableAt.hasDerivAt)
      (by simpa [topRay] using (roundingArc_endpoints ε θ).2)
      (by rw [(roundingArc_deriv_endpoints ε θ).2, (hasDerivAt_topRay ε θ 1).deriv]) 0
    rw [h.deriv]
    simpa using (roundingArc_deriv_endpoints ε θ).1.symm

lemma hasDerivAt_piecewise_Iic_of_derivatives {f g df dg : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f a = g a) (hd : df a = dg a) (x : ℝ) :
    HasDerivAt ((Iic a).piecewise f g) ((Iic a).piecewise df dg x) x := by
  have hdf : deriv f = df := funext fun t => (hf t).deriv
  have hdg : deriv g = dg := funext fun t => (hg t).deriv
  have h := hasDerivAt_piecewise_Iic
    (fun t => (hf t).differentiableAt.hasDerivAt)
    (fun t => (hg t).differentiableAt.hasDerivAt) hv (by simpa only [hdf, hdg] using hd) x
  simpa only [hdf, hdg] using h

lemma hasDerivAt_joinedRounding (ε θ t : ℝ) :
    HasDerivAt (joinedRounding ε θ)
      (if t ≤ 0 then ((-(ε * Real.pi / 2) : ℝ) : ℂ)
       else if t ≤ 1 then roundingVelocity ε θ t
       else (ε * Real.pi / 2 : ℝ) * Complex.exp ((θ : ℂ) * I)) t := by
  classical
  have hi := hasDerivAt_piecewise_Iic_of_derivatives (a := 1)
    (hasDerivAt_roundingArc ε θ) (hasDerivAt_topRay ε θ)
    (by simpa [topRay] using (roundingArc_endpoints ε θ).2)
    (by rw [← (hasDerivAt_roundingArc ε θ 1).deriv,
      (roundingArc_deriv_endpoints ε θ).2])
  have ho := hasDerivAt_piecewise_Iic_of_derivatives (a := 0)
    (hasDerivAt_bottomRay ε) hi
    (by simpa [bottomRay] using (roundingArc_endpoints ε θ).1.symm)
    (by simpa only [piecewise, mem_Iic, zero_le_one, ite_true] using
      ((hasDerivAt_roundingArc ε θ 0).deriv.symm.trans
        (roundingArc_deriv_endpoints ε θ).1).symm) t
  simpa only [joinedRounding, piecewise, mem_Iic] using ho

lemma joinedRounding_regular {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (t : ℝ) :
    deriv (joinedRounding ε θ) t ≠ 0 := by
  rw [(hasDerivAt_joinedRounding ε θ t).deriv]
  split_ifs with h0 h1
  · exact Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr (by positivity))
  · rw [← (hasDerivAt_roundingArc ε θ t).deriv]
    exact roundingArc_regular hε hθ ⟨(not_le.mp h0).le, h1⟩
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Complex.exp_ne_zero _)

lemma hasDerivAt_positiveJoinedRounding (ε θ t : ℝ) :
    HasDerivAt (positiveJoinedRounding ε θ)
      (-(deriv (joinedRounding ε θ) (1 - t))) t := by
  have h := (hasDerivAt_joinedRounding ε θ (1 - t)).differentiableAt.hasDerivAt
  have hi : HasDerivAt (fun u : ℝ => 1 - u) (-1 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  simpa only [positiveJoinedRounding, neg_one_smul, Function.comp_def] using! h.scomp t hi

lemma contDiff_positiveJoinedRounding (ε θ : ℝ) :
    ContDiff ℝ 1 (positiveJoinedRounding ε θ) :=
  (contDiff_joinedRounding ε θ).comp (contDiff_const.sub contDiff_id)

lemma positiveJoinedRounding_regular {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (t : ℝ) :
    deriv (positiveJoinedRounding ε θ) t ≠ 0 := by
  rw [(hasDerivAt_positiveJoinedRounding ε θ t).deriv]
  exact neg_ne_zero.mpr (joinedRounding_regular hε hθ _)

lemma positiveJoinedRounding_on_top (ε θ : ℝ) {t : ℝ} (ht : t ≤ 0) :
    positiveJoinedRounding ε θ t = topRay ε θ (1 - t) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [positiveJoinedRounding, joinedRounding, (roundingArc_endpoints ε θ).2, topRay]
  · simp [positiveJoinedRounding, joinedRounding,
      show ¬ 1 - t ≤ 0 by linarith, show ¬ 1 - t ≤ 1 by linarith]

lemma positiveJoinedRounding_on_arc (ε θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    positiveJoinedRounding ε θ t = roundingArc ε θ (1 - t) := by
  by_cases h : 1 - t ≤ 0
  · have ht1 : t = 1 := by linarith [ht.2]
    subst t
    simp [positiveJoinedRounding, joinedRounding, (roundingArc_endpoints ε θ).1, bottomRay]
  · simp [positiveJoinedRounding, joinedRounding, h, show 1 - t ≤ 1 by linarith [ht.1]]

lemma positiveJoinedRounding_on_bottom (ε θ : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    positiveJoinedRounding ε θ t = bottomRay ε (1 - t) := by
  simp [positiveJoinedRounding, joinedRounding, show 1 - t ≤ 0 by linarith]

lemma positiveJoinedRounding_deriv_endpoints (ε θ : ℝ) :
    deriv (positiveJoinedRounding ε θ) 0 =
      (-(ε * Real.pi / 2) : ℝ) * Complex.exp ((θ : ℂ) * I) ∧
    deriv (positiveJoinedRounding ε θ) 1 = (ε * Real.pi / 2 : ℝ) := by
  rw [(hasDerivAt_positiveJoinedRounding ε θ 0).deriv,
    (hasDerivAt_positiveJoinedRounding ε θ 1).deriv]
  simp only [sub_zero, sub_self,
    (hasDerivAt_joinedRounding ε θ 1).deriv, (hasDerivAt_joinedRounding ε θ 0).deriv]
  simp only [show ¬ (1 : ℝ) ≤ 0 by norm_num, le_refl, ite_false, ite_true]
  rw [← (hasDerivAt_roundingArc ε θ 1).deriv,
    (roundingArc_deriv_endpoints ε θ).2]
  constructor <;> simp

lemma norm_polar {r : ℝ} (hr : 0 ≤ r) (a : ℝ) :
    ‖(r : ℂ) * Complex.exp ((a : ℂ) * I)‖ = r := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hr]

lemma angle_eq_of_polar_eq {r s a b θ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ha : a ∈ Icc (0 : ℝ) θ) (hb : b ∈ Icc (0 : ℝ) θ) (hθ : θ < 2 * Real.pi)
    (h : (r : ℂ) * Complex.exp ((a : ℂ) * I) =
      (s : ℂ) * Complex.exp ((b : ℂ) * I)) : a = b := by
  have hrs : r = s := by
    simpa only [norm_polar hr.le, norm_polar hs.le] using congrArg norm h
  rw [hrs] at h
  have he := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hs.ne') h
  apply eq_of_circleMap_eq (R := 1) (c := 0) (by norm_num) _ (by simpa [circleMap] using he)
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma norm_bottomRay {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) :
    ‖bottomRay ε t‖ = ε - (ε * Real.pi / 2) * t := by
  rw [bottomRay, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ ε * Real.pi / 2) ht]

lemma norm_topRay {ε θ t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t) :
    ‖topRay ε θ t‖ = ε + (ε * Real.pi / 2) * (t - 1) := by
  apply norm_polar
  nlinarith [mul_nonneg (by positivity : 0 ≤ ε * Real.pi / 2) (sub_nonneg.mpr ht)]

lemma joinedRounding_ne_of_lt {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) {s t : ℝ} (hst : s < t) :
    joinedRounding ε θ s ≠ joinedRounding ε θ t := by
  intro he
  have hk : 0 < ε * Real.pi / 2 := by positivity
  by_cases hs0 : s ≤ 0
  · by_cases ht0 : t ≤ 0
    · have hn := congrArg norm he
      simp only [joinedRounding, piecewise, mem_Iic, hs0, ht0, ite_true] at hn
      rw [norm_bottomRay hε hs0, norm_bottomRay hε ht0] at hn
      nlinarith
    · by_cases ht1 : t ≤ 1
      · have he' : bottomRay ε s = roundingArc ε θ t := by
          simpa [joinedRounding, hs0, ht0, ht1] using he
        have hst' : 0 < smoothStep t := by
          simpa only [smoothStep_zero] using
            smoothStep_strictMonoOn (by simp) ⟨(not_le.mp ht0).le, ht1⟩ (not_le.mp ht0)
        have htstep := smoothStep_mem_Icc ⟨(not_le.mp ht0).le, ht1⟩
        have hpa := angle_eq_of_polar_eq
          (r := ε - ε * Real.pi / 2 * s) (s := ε * radialProfile t)
          (a := 0) (b := θ * smoothStep t) (θ := θ)
          (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hk.le hs0])
          (mul_pos hε (radialProfile_pos ⟨(not_le.mp ht0).le, ht1⟩))
          ⟨le_rfl, hθ.le⟩
          ⟨mul_nonneg hθ.le htstep.1, by nlinarith [htstep.2]⟩ hθ'
          (by simpa [bottomRay, roundingArc] using he')
        exact (mul_pos hθ hst').ne' hpa.symm
      · have he' : bottomRay ε s = topRay ε θ t := by
          simpa [joinedRounding, hs0, ht0, ht1] using he
        have hpa := angle_eq_of_polar_eq
          (r := ε - ε * Real.pi / 2 * s) (s := ε + ε * Real.pi / 2 * (t - 1))
          (a := 0) (b := θ) (θ := θ)
          (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hk.le hs0])
          (by nlinarith [mul_nonneg hk.le (sub_nonneg.mpr (not_le.mp ht1).le)])
          ⟨le_rfl, hθ.le⟩ ⟨hθ.le, le_rfl⟩ hθ'
          (by simpa [bottomRay, topRay] using he')
        exact hθ.ne' hpa.symm
  · have ht0 : ¬ t ≤ 0 := not_le.mpr (lt_trans (not_le.mp hs0) hst)
    by_cases hs1 : s ≤ 1
    · by_cases ht1 : t ≤ 1
      · have he' : roundingArc ε θ s = roundingArc ε θ t := by
          simpa [joinedRounding, hs0, hs1, ht0, ht1] using he
        exact hst.ne (roundingArc_injOn hε hθ hθ'
          ⟨(not_le.mp hs0).le, hs1⟩ ⟨(not_le.mp ht0).le, ht1⟩ he')
      · have hn := congrArg norm he
        simp only [joinedRounding, piecewise, mem_Iic, hs0, hs1, ht0, ht1, ite_true, ite_false] at hn
        rw [norm_topRay hε (not_le.mp ht1).le,
          norm_roundingArc hε.le ⟨(not_le.mp hs0).le, hs1⟩] at hn
        have hr := (radialProfile_bounds ⟨(not_le.mp hs0).le, hs1⟩).2
        have heps := mul_le_of_le_one_right hε.le hr
        nlinarith [mul_pos hk (sub_pos.mpr (not_le.mp ht1))]
    · have ht1 : ¬ t ≤ 1 := not_le.mpr (lt_trans (not_le.mp hs1) hst)
      have hn := congrArg norm he
      simp only [joinedRounding, piecewise, mem_Iic, hs0, hs1, ht0, ht1, ite_false] at hn
      rw [norm_topRay hε (not_le.mp hs1).le, norm_topRay hε (not_le.mp ht1).le] at hn
      nlinarith

lemma joinedRounding_injective {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) : Function.Injective (joinedRounding ε θ) := by
  intro s t h
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact False.elim (joinedRounding_ne_of_lt hε hθ hθ' hst h)
  · rfl
  · exact False.elim (joinedRounding_ne_of_lt hε hθ hθ' hts h.symm)

lemma positiveJoinedRounding_injective {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) : Function.Injective (positiveJoinedRounding ε θ) := by
  intro s t h
  have he := joinedRounding_injective hε hθ hθ' h
  linarith

/-- Explicit C1 gluing, including the correctly oriented endpoint velocities. -/
theorem joined_rounding : Specs.D12Complex.Ch14.CircularCornerRounding.joined_rounding_type := by
  intro ε θ hε hθ hθ'
  exact ⟨contDiff_positiveJoinedRounding ε θ, positiveJoinedRounding_injective hε hθ hθ',
    positiveJoinedRounding_regular hε hθ,
    fun _ ht => positiveJoinedRounding_on_top ε θ ht,
    fun _ ht => positiveJoinedRounding_on_arc ε θ ht,
    fun _ ht => positiveJoinedRounding_on_bottom ε θ ht,
    (positiveJoinedRounding_deriv_endpoints ε θ).1,
    (positiveJoinedRounding_deriv_endpoints ε θ).2⟩

lemma isCompact_sectorTip (ε θ : ℝ) : IsCompact (sectorTip ε θ) := by
  apply (isCompact_Icc.prod isCompact_Icc).image
  exact (continuous_snd.smul ((contDiff_roundingArc ε θ).continuous.comp continuous_fst))

lemma sectorTip_subset_closedBall {ε θ : ℝ} (hε : 0 < ε) :
    sectorTip ε θ ⊆ closedBall (0 : ℂ) ε := by
  rintro z ⟨p, hp, rfl⟩
  have ha : ‖roundingArc ε θ p.1‖ ≤ ε := by
    rw [norm_roundingArc hε.le hp.1]
    exact mul_le_of_le_one_right hε.le (radialProfile_bounds hp.1).2
  have hn : ‖p.2 • roundingArc ε θ p.1‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp.2.1]
    simpa using mul_le_mul hp.2.2 ha (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mem_closedBall, dist_zero_right] using hn

lemma zero_mem_sectorTip (ε θ : ℝ) : (0 : ℂ) ∈ sectorTip ε θ := by
  refine ⟨(0, 0), ?_, ?_⟩ <;> simp

lemma roundingArc_image_subset_sectorTip (ε θ : ℝ) :
    roundingArc ε θ '' Icc (0 : ℝ) 1 ⊆ sectorTip ε θ := by
  rintro z ⟨t, ht, rfl⟩
  exact ⟨(t, 1), ⟨ht, by simp⟩, one_smul ℝ _⟩

lemma volume_sectorTip_le {ε θ : ℝ} (hε : 0 < ε) :
    volume (sectorTip ε θ) ≤ ENNReal.ofReal (Real.pi * ε ^ 2) := by
  calc
    _ ≤ volume (closedBall (0 : ℂ) ε) := measure_mono (sectorTip_subset_closedBall hε)
    _ = ENNReal.ofReal (Real.pi * ε ^ 2) := by
      rw [Complex.volume_closedBall]
      rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hε.le]
      simp [mul_comm, ← NNReal.coe_real_pi]

lemma hausdorffMeasure_roundingArc_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    Measure.hausdorffMeasure 1 (roundingArc ε θ '' Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ((Real.pi / 2 + 6 * θ) * ε) := by
  let K : ℝ≥0 := ⟨(Real.pi / 2 + 6 * θ) * ε, by positivity⟩
  have hL : LipschitzOnWith K (roundingArc ε θ) (Icc (0 : ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t _ => (hasDerivAt_roundingArc ε θ t).differentiableAt) _ (convex_Icc _ _)
    intro t ht
    change ‖deriv (roundingArc ε θ) t‖ ≤ (Real.pi / 2 + 6 * θ) * ε
    exact norm_deriv_roundingArc_le hε hθ ht
  have h := hL.hausdorffMeasure_image_le (d := 1) (by norm_num)
  change Measure.hausdorffMeasure 1 (roundingArc ε θ '' Icc (0 : ℝ) 1) ≤
    ENNReal.ofReal (K : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  simpa [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc] using h

/-- The removed tip contains a full sector neighborhood of the old vertex. -/
lemma sector_inter_ball_subset_sectorTip {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    CircularExhaustion.sector θ ∩ ball (0 : ℂ) (ε / 2) ⊆ sectorTip ε θ := by
  rintro z ⟨⟨ρ, α, hρ, hα, hαθ, rfl⟩, hz⟩
  have hρ' : ρ < ε / 2 := by
    simpa only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos hρ] using hz
  have ha : α / θ ∈ Icc (smoothStep 0) (smoothStep 1) := by
    simp only [smoothStep_zero, smoothStep_one, mem_Icc]
    exact ⟨(div_pos hα hθ).le, ((div_lt_one hθ).mpr hαθ).le⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    contDiff_smoothStep.continuous.continuousOn ha
  have hangle : θ * smoothStep t = α := by rw [he]; field_simp
  have hd : 0 < ε * radialProfile t := mul_pos hε (radialProfile_pos ht)
  have hρd : ρ ≤ ε * radialProfile t := by
    have hr := (radialProfile_bounds ht).1
    nlinarith
  refine ⟨(t, ρ / (ε * radialProfile t)), ⟨ht, ?_⟩, ?_⟩
  · exact ⟨(div_pos hρ hd).le, (div_le_one hd).mpr hρd⟩
  · dsimp only
    rw [roundingArc, hangle, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      div_mul_cancel₀ ρ hd.ne']

/-- Quantitative estimates for the actual removed tip and actual new curve. -/
theorem sector_tip : Specs.D12Complex.Ch14.CircularCornerRounding.sector_tip_type := by
  intro ε θ hε hθ _
  refine ⟨isCompact_sectorTip ε θ, sectorTip_subset_closedBall hε,
    zero_mem_sectorTip ε θ, roundingArc_image_subset_sectorTip ε θ,
    sector_inter_ball_subset_sectorTip hε hθ,
    volume_sectorTip_le hε, hausdorffMeasure_roundingArc_le hε hθ, ?_⟩
  intro U hU
  have hs : U \ (U \ sectorTip ε θ) ⊆ sectorTip ε θ := by
    intro z hz
    by_contra hn
    exact hz.2 ⟨hz.1, hn⟩
  exact ⟨hU.sdiff (isCompact_sectorTip ε θ).isClosed,
    hs.trans (sectorTip_subset_closedBall hε),
    (measure_mono hs).trans (volume_sectorTip_le hε)⟩

lemma chart_tip_estimates {g : ℂ → ℂ} {L : ℝ≥0} {R ε θ : ℝ}
    (hg : LipschitzOnWith L g (closedBall (0 : ℂ) R)) (hε : 0 < ε)
    (hεR : ε ≤ R) (hθ : 0 < θ) :
    IsCompact (g '' sectorTip ε θ) ∧
    g '' sectorTip ε θ ⊆ closedBall (g 0) (L * ε) ∧
    volume (g '' sectorTip ε θ) ≤ ENNReal.ofReal (Real.pi * ((L : ℝ) * ε) ^ 2) ∧
    Measure.hausdorffMeasure 1 (g '' (roundingArc ε θ '' Icc (0 : ℝ) 1)) ≤
      ENNReal.ofReal ((L : ℝ) * (Real.pi / 2 + 6 * θ) * ε) := by
  have hs : sectorTip ε θ ⊆ closedBall (0 : ℂ) R :=
    (sectorTip_subset_closedBall hε).trans (closedBall_subset_closedBall hεR)
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self (hε.le.trans hεR)
  have hi : g '' sectorTip ε θ ⊆ closedBall (g 0) (L * ε) := by
    rintro z ⟨y, hy, rfl⟩
    apply (hg.dist_le_mul y (hs hy) 0 h0).trans
    exact mul_le_mul_of_nonneg_left (sectorTip_subset_closedBall hε hy) L.coe_nonneg
  refine ⟨(isCompact_sectorTip ε θ).image_of_continuousOn (hg.continuousOn.mono hs),
    hi, ?_, ?_⟩
  · calc
      _ ≤ volume (closedBall (g 0) ((L : ℝ) * ε)) := measure_mono hi
      _ = ENNReal.ofReal (Real.pi * ((L : ℝ) * ε) ^ 2) := by
        rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le,
          ENNReal.ofReal_pow (mul_nonneg L.coe_nonneg hε.le)]
        simp [mul_comm, ← NNReal.coe_real_pi]
  · have ha : roundingArc ε θ '' Icc (0 : ℝ) 1 ⊆ closedBall (0 : ℂ) R :=
      (roundingArc_image_subset_sectorTip ε θ).trans hs
    have hh := (hg.mono ha).hausdorffMeasure_image_le (d := 1) (by norm_num)
    simp only [ENNReal.rpow_one] at hh
    calc
      _ ≤ (L : ℝ≥0∞) * Measure.hausdorffMeasure 1
          (roundingArc ε θ '' Icc (0 : ℝ) 1) := hh
      _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal ((Real.pi / 2 + 6 * θ) * ε) :=
        mul_le_mul_right (hausdorffMeasure_roundingArc_le hε hθ) _
      _ = ENNReal.ofReal ((L : ℝ) * (Real.pi / 2 + 6 * θ) * ε) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg]
        congr 1
        ring

/-- The constants are chosen once for the fixed chart and work at every
sufficiently small positive rounding scale. -/
theorem chart_estimates : Specs.D12Complex.Ch14.CircularCornerRounding.chart_estimates_type := by
  intro g hg
  let L : ℝ≥0 := ‖fderiv ℝ g 0‖₊ + 1
  obtain ⟨W, hW, hgW⟩ := hg.exists_lipschitzOnWith_of_nnnorm_lt L (by simp [L])
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hW
  have hball : closedBall (0 : ℂ) (r / 2) ⊆ W := by
    apply Subset.trans _ hrW
    exact closedBall_subset_ball (by linarith)
  refine ⟨r / 2, (L : ℝ), by positivity, by simp [L]; positivity, ?_⟩
  intro ε θ hε hεR hθ _
  exact chart_tip_estimates (hgW.mono hball) hε hεR hθ


/-- Exact membership on every ray of the closed angular interval. This includes
both boundary rays, so it also describes the points at the new joins. -/
lemma polar_mem_sectorTip_iff {ε θ r t : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) :
    (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) ∈ sectorTip ε θ ↔
      r ≤ ε * radialProfile t := by
  have hd : 0 < ε * radialProfile t := mul_pos hε (radialProfile_pos ht)
  constructor
  · rintro ⟨⟨u, s⟩, ⟨hu, hs⟩, he⟩
    have hn := congrArg norm he
    dsimp only at he hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1,
      norm_roundingArc hε.le hu, norm_polar hr] at hn
    by_cases hr0 : r = 0
    · simpa [hr0] using hd.le
    have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hsp : 0 < s := by
      by_contra h
      have : s = 0 := le_antisymm (not_lt.mp h) hs.1
      simp [this] at hn
      exact hr0 hn.symm
    have he' : ((s * (ε * radialProfile u) : ℝ) : ℂ) *
        Complex.exp ((θ * smoothStep u : ℝ) * I) =
      (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) := by
      simpa only [roundingArc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul] using he
    have ha := angle_eq_of_polar_eq (mul_pos hsp (mul_pos hε (radialProfile_pos hu))) hrp
      ⟨mul_nonneg hθ.le (smoothStep_mem_Icc hu).1,
        by nlinarith [(smoothStep_mem_Icc hu).2]⟩
      ⟨mul_nonneg hθ.le (smoothStep_mem_Icc ht).1,
        by nlinarith [(smoothStep_mem_Icc ht).2]⟩ hθ' he'
    have hut := smoothStep_strictMonoOn.injOn hu ht (mul_left_cancel₀ hθ.ne' ha)
    change u = t at hut
    subst u
    rw [← hn]
    exact mul_le_of_le_one_left hd.le hs.2
  · intro hrle
    refine ⟨(t, r / (ε * radialProfile t)),
      ⟨ht, ⟨div_nonneg hr hd.le, (div_le_one hd).mpr hrle⟩⟩, ?_⟩
    dsimp only
    rw [roundingArc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      div_mul_cancel₀ r hd.ne']

/-- The sector is an actual open subset of the plane, proved from the open
complex exponential rather than from an assumed geometric certificate. -/
lemma isOpen_sector (θ : ℝ) : IsOpen (CircularExhaustion.sector θ) := by
  have he : CircularExhaustion.sector θ =
      Complex.exp '' {z : ℂ | 0 < z.im ∧ z.im < θ} := by
    ext z
    constructor
    · rintro ⟨r, a, hr, ha, haθ, rfl⟩
      refine ⟨(Real.log r : ℂ) + (a : ℂ) * I, ?_, ?_⟩
      · simpa using And.intro ha haθ
      · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨Real.exp w.re, w.im, Real.exp_pos _, hw.1, hw.2, ?_⟩
      rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
  rw [he]
  exact Complex.isOpenMap_exp _ ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const))

lemma isOpen_roundedSector (ε θ : ℝ) : IsOpen (roundedSector ε θ) :=
  (isOpen_sector θ).sdiff (isCompact_sectorTip ε θ).isClosed

/-- The old vertex is absent even from the closure of the actual rounded set. -/
lemma roundedSector_disjoint_small_ball {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    Disjoint (roundedSector ε θ) (ball (0 : ℂ) (ε / 2)) := by
  rw [Set.disjoint_left]
  intro z hz hb
  exact hz.2 (sector_inter_ball_subset_sectorTip hε hθ ⟨hz.1, hb⟩)

lemma zero_not_mem_closure_roundedSector {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    (0 : ℂ) ∉ closure (roundedSector ε θ) := by
  intro hz
  obtain ⟨z, hz, hb⟩ := Metric.mem_closure_iff.mp hz (ε / 2) (by positivity)
  exact Set.disjoint_left.mp (roundedSector_disjoint_small_ball hε hθ) hz
    (by simpa [mem_ball, dist_comm] using hb)

/-- A radial test for the actual open set after cutting off the tip. -/
lemma polar_mem_roundedSector_iff {ε θ r t : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 < r) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) ∈ roundedSector ε θ ↔
      ε * radialProfile t < r := by
  have hsector : (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) ∈
      CircularExhaustion.sector θ :=
    ⟨r, θ * smoothStep t, hr, mul_pos hθ (smoothStep_mem_Ioo ht).1,
      by nlinarith [(smoothStep_mem_Ioo ht).2], rfl⟩
  simp only [roundedSector, mem_sdiff, hsector, true_and,
    polar_mem_sectorTip_iff hε hθ hθ' hr.le (Ioo_subset_Icc_self ht), not_le]


/-- Outside a closed removed set the original and new boundaries agree, with
an actual common open neighborhood on which their set sides agree. -/
lemma closed_removal_locality {U K : Set ℂ} (hK : IsClosed K) :
    (∀ z ∉ K, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ U ∩ W = (U \ K) ∩ W) ∧
    frontier U \ frontier (U \ K) ⊆ K ∧
    frontier (U \ K) \ frontier U ⊆ K := by
  have he := frontier_inter_open_inter (s := U) hK.isOpen_compl
  change frontier (U \ K) ∩ Kᶜ = frontier U ∩ Kᶜ at he
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    refine ⟨Kᶜ, hK.isOpen_compl, hz, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  · intro z hz
    by_contra h
    exact hz.2 ((Set.ext_iff.mp he z).mpr ⟨hz.1, h⟩).1
  · intro z hz
    by_contra h
    exact hz.2 ((Set.ext_iff.mp he z).mp ⟨hz.1, h⟩).1

lemma roundingArc_interior_mem_frontier {ε θ t : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (ht : t ∈ Ioo (0 : ℝ) 1) :
    roundingArc ε θ t ∈ frontier (roundedSector ε θ) := by
  have hb : 0 < ε * radialProfile t := mul_pos hε (radialProfile_pos (Ioo_subset_Icc_self ht))
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closure_iff]
    intro δ hδ
    let r := ε * radialProfile t + δ / 2
    have hr : 0 < r := by dsimp [r]; linarith
    refine ⟨(r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I),
      (polar_mem_roundedSector_iff hε hθ hθ' hr ht).mpr (by dsimp [r]; linarith), ?_⟩
    rw [dist_eq_norm, roundingArc, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
    have he : ε * radialProfile t - r = -(δ / 2) := by dsimp [r]; ring
    rw [he, abs_neg, abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  · intro hi
    exact (interior_subset hi).2
      (roundingArc_image_subset_sectorTip ε θ ⟨t, Ioo_subset_Icc_self ht, rfl⟩)

/-- Every point of the actual added arc, including both joins, belongs to the
frontier of the actual rounded set. Endpoint membership follows by closure. -/
lemma roundingArc_image_subset_frontier {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    roundingArc ε θ '' Icc (0 : ℝ) 1 ⊆ frontier (roundedSector ε θ) := by
  have hi : Ioo (0 : ℝ) 1 ⊆ (roundingArc ε θ) ⁻¹' frontier (roundedSector ε θ) :=
    fun t ht => roundingArc_interior_mem_frontier hε hθ hθ' ht
  have hc := closure_minimal hi
    (isClosed_frontier.preimage (contDiff_roundingArc ε θ).continuous)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  rintro z ⟨t, ht, rfl⟩
  exact hc ht

/-- Only the two short ray segments of the old frontier can meet the removed
tip. This uses openness of the actual sector and the literal tip parametrization. -/
lemma frontier_sector_inter_tip_subset_shortRays {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    frontier (CircularExhaustion.sector θ) ∩ sectorTip ε θ ⊆ shortRays ε θ := by
  rintro z ⟨hz, ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩⟩
  change t ∈ Icc (0 : ℝ) 1 at ht
  change s ∈ Icc (0 : ℝ) 1 at hs
  have hr : s * ε ∈ Icc (0 : ℝ) ε :=
    ⟨mul_nonneg hs.1 hε.le, mul_le_of_le_one_left hε.le hs.2⟩
  by_cases hs0 : s = 0
  · subst s
    exact Or.inl ⟨0, ⟨le_rfl, hε.le⟩, by simp⟩
  by_cases ht0 : t = 0
  · subst t
    exact Or.inl ⟨s * ε, hr, by simp [roundingArc, radialProfile, Complex.real_smul]⟩
  by_cases ht1 : t = 1
  · subst t
    exact Or.inr ⟨s * ε, hr, by simp [roundingArc, radialProfile, Complex.real_smul, mul_assoc]⟩
  have hti : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hmem : s • roundingArc ε θ t ∈ CircularExhaustion.sector θ := by
    refine ⟨s * (ε * radialProfile t), θ * smoothStep t,
      mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0)) (mul_pos hε (radialProfile_pos ht)),
      mul_pos hθ (smoothStep_mem_Ioo hti).1,
      by nlinarith [(smoothStep_mem_Ioo hti).2], ?_⟩
    simp only [roundingArc, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  exact False.elim (hz.2 (by simpa only [(isOpen_sector θ).interior_eq] using hmem))

lemma removed_sector_frontier_subset_shortRays {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    frontier (CircularExhaustion.sector θ) \ frontier (roundedSector ε θ) ⊆ shortRays ε θ := by
  intro z hz
  exact frontier_sector_inter_tip_subset_shortRays hε hθ
    ⟨hz.1, (closed_removal_locality (isCompact_sectorTip ε θ).isClosed).2.1 hz⟩


/-- A continuous increasing extension is used only to prove openness of polar
coordinates; no extra smoothness at the two joins is asserted. -/
private def extendedStep (t : ℝ) : ℝ :=
  if t ≤ 0 then t else if t ≤ 1 then smoothStep t else t

private lemma extendedStep_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extendedStep t = smoothStep t := by
  by_cases h : t ≤ 0
  · have : t = 0 := le_antisymm h ht.1
    simp [extendedStep, this]
  · simp [extendedStep, h, ht.2]

private lemma strictMono_extendedStep : StrictMono extendedStep := by
  intro s t hst
  by_cases hs0 : s ≤ 0
  · by_cases ht0 : t ≤ 0
    · simpa [extendedStep, hs0, ht0] using hst
    · by_cases ht1 : t ≤ 1
      · have ht : t ∈ Ioo (0 : ℝ) 1 ∨ t = 1 := by
          rcases lt_or_eq_of_le ht1 with h | h
          · exact Or.inl ⟨not_le.mp ht0, h⟩
          · exact Or.inr h
        have hp : 0 < smoothStep t := by
          rcases ht with ht | rfl
          · exact (smoothStep_mem_Ioo ht).1
          · simp
        simp only [extendedStep, hs0, ht0, ht1, ite_true, ite_false]
        linarith
      · simp only [extendedStep, hs0, ht0, ht1, ite_true, ite_false]
        exact hst
  · have ht0 : ¬ t ≤ 0 := by linarith
    by_cases hs1 : s ≤ 1
    · by_cases ht1 : t ≤ 1
      · simpa only [extendedStep, hs0, ht0, hs1, ht1, ite_true, ite_false] using
          smoothStep_strictMonoOn ⟨(not_le.mp hs0).le, hs1⟩
            ⟨(not_le.mp ht0).le, ht1⟩ hst
      · have hb := (smoothStep_mem_Icc ⟨(not_le.mp hs0).le, hs1⟩).2
        simp only [extendedStep, hs0, ht0, hs1, ht1, ite_true, ite_false]
        linarith
    · have ht1 : ¬ t ≤ 1 := by linarith
      simpa [extendedStep, hs0, ht0, hs1, ht1] using hst

private lemma surjective_extendedStep : Function.Surjective extendedStep := by
  intro y
  by_cases h0 : y ≤ 0
  · exact ⟨y, by simp [extendedStep, h0]⟩
  by_cases h1 : y ≤ 1
  · obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      contDiff_smoothStep.continuous.continuousOn
      (show y ∈ Icc (smoothStep 0) (smoothStep 1) by
        simpa only [smoothStep_zero, smoothStep_one, mem_Icc] using And.intro (not_le.mp h0).le h1)
    exact ⟨t, (extendedStep_eq ht).trans he⟩
  · exact ⟨y, by simp [extendedStep, h0, h1]⟩

private def angularHomeomorph (θ : ℝ) (hθ : 0 < θ) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective extendedStep strictMono_extendedStep
    surjective_extendedStep).toHomeomorph.trans (Homeomorph.mulLeft₀ θ hθ.ne')

private def polarLogHomeomorph (θ : ℝ) (hθ : 0 < θ) : ℂ ≃ₜ ℂ :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((Homeomorph.prodCongr (Homeomorph.refl ℝ) (angularHomeomorph θ hθ)).trans
      Complex.equivRealProdCLM.symm.toHomeomorph)

private lemma polarLogHomeomorph_apply (θ : ℝ) (hθ : 0 < θ) (z : ℂ) :
    polarLogHomeomorph θ hθ z = (z.re : ℂ) + (θ * extendedStep z.im : ℝ) * I := by
  simp [polarLogHomeomorph, angularHomeomorph, Complex.equivRealProdCLM_symm_apply]

/-- A point strictly below the new arc and strictly between the sector rays is
an interior point of the literal swept-out tip. Openness follows from an actual
angular homeomorphism and the open complex exponential. -/
lemma polar_mem_interior_sectorTip {ε θ r t : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 < r) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hrle : r < ε * radialProfile t) :
    (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) ∈ interior (sectorTip ε θ) := by
  let A : Set ℂ := {z | 0 < z.im ∧ z.im < 1 ∧ Real.exp z.re < ε * radialProfile z.im}
  have hA : IsOpen A := by
    exact (isOpen_lt continuous_const Complex.continuous_im).inter
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (Real.continuous_exp.comp Complex.continuous_re)
          (continuous_const.mul (contDiff_radialProfile.continuous.comp Complex.continuous_im))))
  let F : ℂ → ℂ := Complex.exp ∘ polarLogHomeomorph θ hθ
  have hopen : IsOpen (F '' A) :=
    (Complex.isOpenMap_exp.comp (polarLogHomeomorph θ hθ).isOpenMap) A hA
  have hsub : F '' A ⊆ sectorTip ε θ := by
    rintro z ⟨w, hw, rfl⟩
    have hwi : w.im ∈ Icc (0 : ℝ) 1 := ⟨hw.1.le, hw.2.1.le⟩
    have he : F w = (Real.exp w.re : ℂ) *
        Complex.exp ((θ * smoothStep w.im : ℝ) * I) := by
      dsimp [F, Function.comp_def]
      rw [polarLogHomeomorph_apply, extendedStep_eq hwi,
        Complex.exp_add, ← Complex.ofReal_exp]
    rw [he]
    exact (polar_mem_sectorTip_iff hε hθ hθ' (Real.exp_pos _).le hwi).mpr hw.2.2.le
  apply (interior_maximal hsub hopen)
  refine ⟨(Real.log r : ℂ) + (t : ℂ) * I, ?_, ?_⟩
  · simpa only [A, mem_ofPred_eq, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add,
      add_re, mul_I_re, neg_zero, add_zero, Real.exp_log hr] using
        And.intro ht.1 (And.intro ht.2 hrle)
  · dsimp [F, Function.comp_def]
    rw [polarLogHomeomorph_apply]
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add, extendedStep_eq (Ioo_subset_Icc_self ht),
      Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]


lemma zero_not_mem_sector (θ : ℝ) : (0 : ℂ) ∉ CircularExhaustion.sector θ := by
  rintro ⟨r, a, hr, _, _, he⟩
  have hn := congrArg norm he
  rw [norm_zero, norm_polar hr.le] at hn
  linarith

lemma polar_mem_sector_iff {r a θ : ℝ} (hr : 0 < r) (ha : a ∈ Icc (0 : ℝ) θ)
    (hθ' : θ < 2 * Real.pi) :
    (r : ℂ) * Complex.exp ((a : ℂ) * I) ∈ CircularExhaustion.sector θ ↔
      0 < a ∧ a < θ := by
  constructor
  · rintro ⟨s, b, hs, hb, hbθ, he⟩
    have hab := angle_eq_of_polar_eq hr hs ha ⟨hb.le, hbθ.le⟩ hθ' he
    simpa only [hab] using And.intro hb hbθ
  · exact fun h => ⟨r, a, hr, h.1, h.2, rfl⟩

/-- No spurious added frontier is hidden in the interior of the swept-out tip. -/
lemma added_sector_frontier_subset_roundingArc {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    frontier (roundedSector ε θ) \ frontier (CircularExhaustion.sector θ) ⊆
      roundingArc ε θ '' Icc (0 : ℝ) 1 := by
  intro z hz
  have hzcl : z ∈ closure (CircularExhaustion.sector θ) :=
    closure_mono sdiff_subset hz.1.1
  have hzsector : z ∈ CircularExhaustion.sector θ := by
    by_contra h
    exact hz.2 ⟨hzcl, by simpa only [(isOpen_sector θ).interior_eq] using h⟩
  have hztip := (closed_removal_locality (isCompact_sectorTip ε θ).isClosed).2.2 hz
  rcases hztip with ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
  change t ∈ Icc (0 : ℝ) 1 at ht
  change s ∈ Icc (0 : ℝ) 1 at hs
  have hs0 : s ≠ 0 := by
    intro he
    exact zero_not_mem_sector θ (by simpa [he] using hzsector)
  have hr : 0 < s * (ε * radialProfile t) :=
    mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0)) (mul_pos hε (radialProfile_pos ht))
  have hp : s • roundingArc ε θ t =
      ((s * (ε * radialProfile t) : ℝ) : ℂ) *
        Complex.exp ((θ * smoothStep t : ℝ) * I) := by
    simp only [roundingArc, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  have ha := (polar_mem_sector_iff hr
    ⟨mul_nonneg hθ.le (smoothStep_mem_Icc ht).1,
      by nlinarith [(smoothStep_mem_Icc ht).2]⟩ hθ').mp (hp ▸ hzsector)
  have hti : t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · by_contra h
      have he : t = 0 := le_antisymm (not_lt.mp h) ht.1
      simp [he] at ha
    · by_contra h
      have he : t = 1 := le_antisymm ht.2 (not_lt.mp h)
      simp [he] at ha
  have hs1 : s = 1 := by
    by_contra h
    have hlt : s * (ε * radialProfile t) < ε * radialProfile t :=
      mul_lt_of_lt_one_left (mul_pos hε (radialProfile_pos ht))
        (lt_of_le_of_ne hs.2 h)
    have hi := polar_mem_interior_sectorTip hε hθ hθ' hr hti hlt
    rw [← hp] at hi
    have hd : Disjoint (roundedSector ε θ) (interior (sectorTip ε θ)) := by
      rw [Set.disjoint_left]
      exact fun _ hx hi => hx.2 (interior_subset hi)
    exact Set.disjoint_left.mp (hd.closure_left isOpen_interior) hz.1.1 hi
  exact ⟨t, ht, by simp [hs1]⟩

lemma hausdorffMeasure_shortRays_le {ε θ : ℝ} (hε : 0 ≤ ε) :
    Measure.hausdorffMeasure 1 (shortRays ε θ) ≤ ENNReal.ofReal (2 * ε) := by
  have hbase : Measure.hausdorffMeasure 1
      ((fun r : ℝ => (r : ℂ)) '' Icc 0 ε) ≤ ENNReal.ofReal ε := by
    have hh := Complex.isometry_ofReal.lipschitzWith.hausdorffMeasure_image_le
      (d := 1) (by norm_num) (Icc 0 ε)
    simpa [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc] using hh
  have hrot : LipschitzWith 1 (fun z : ℂ => z * Complex.exp ((θ : ℂ) * I)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [dist_eq_norm, ← sub_mul]
  have htop : Measure.hausdorffMeasure 1
      ((fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I)) '' Icc 0 ε) ≤
        ENNReal.ofReal ε := by
    have hh := hrot.hausdorffMeasure_image_le (d := 1) (by norm_num)
      ((fun r : ℝ => (r : ℂ)) '' Icc 0 ε)
    rw [Set.image_image] at hh
    have hh' : Measure.hausdorffMeasure 1
        ((fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I)) '' Icc 0 ε) ≤
          Measure.hausdorffMeasure 1 ((fun r : ℝ => (r : ℂ)) '' Icc 0 ε) := by
      simpa only [ENNReal.rpow_one, ENNReal.coe_one, one_mul, Function.comp_def] using hh
    exact hh'.trans hbase
  calc
    _ ≤ Measure.hausdorffMeasure 1 ((fun r : ℝ => (r : ℂ)) '' Icc 0 ε) +
      Measure.hausdorffMeasure 1
        ((fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I)) '' Icc 0 ε) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hbase htop
    _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε hε]; congr 1; ring

lemma hausdorffMeasure_removed_sector_frontier_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    Measure.hausdorffMeasure 1
      (frontier (CircularExhaustion.sector θ) \ frontier (roundedSector ε θ)) ≤
        ENNReal.ofReal (2 * ε) :=
  (measure_mono (removed_sector_frontier_subset_shortRays hε hθ)).trans
    (hausdorffMeasure_shortRays_le hε.le)

lemma hausdorffMeasure_added_sector_frontier_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    Measure.hausdorffMeasure 1
      (frontier (roundedSector ε θ) \ frontier (CircularExhaustion.sector θ)) ≤
        ENNReal.ofReal ((Real.pi / 2 + 6 * θ) * ε) :=
  (measure_mono (added_sector_frontier_subset_roundingArc hε hθ hθ')).trans
    (hausdorffMeasure_roundingArc_le hε hθ)


/-- A full set-side description of the rounded sector in polar coordinates.
The quantifier over the angular parameter is existential, with no chosen branch
or unproved inverse assumed. -/
lemma mem_roundedSector_iff_exists {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (z : ℂ) :
    z ∈ roundedSector ε θ ↔ ∃ (r t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧
      ε * radialProfile t < r ∧
      z = (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) := by
  constructor
  · rintro ⟨⟨r, a, hr, ha, haθ, rfl⟩, hz⟩
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      contDiff_smoothStep.continuous.continuousOn
      (show a / θ ∈ Icc (smoothStep 0) (smoothStep 1) by
        simpa only [smoothStep_zero, smoothStep_one, mem_Icc] using
          And.intro (div_pos ha hθ).le ((div_lt_one hθ).mpr haθ).le)
    have hangle : θ * smoothStep t = a := by rw [he]; field_simp
    have ht0 : t ≠ 0 := by intro h; simp [h] at he; linarith [div_pos ha hθ]
    have ht1 : t ≠ 1 := by intro h; simp [h] at he; linarith [(div_lt_one hθ).mpr haθ]
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    refine ⟨r, t, hti, ?_, by rw [hangle]⟩
    apply lt_of_not_ge
    intro hrle
    apply hz
    rw [← hangle]
    exact (polar_mem_sectorTip_iff hε hθ hθ' hr.le ht).mpr hrle
  · rintro ⟨r, t, ht, hr, rfl⟩
    have hrp : 0 < r := (mul_pos hε (radialProfile_pos (Ioo_subset_Icc_self ht))).trans hr
    exact (polar_mem_roundedSector_iff hε hθ hθ' hrp ht).mpr hr

/-- Compact polar caps control all limiting points, including those on the
retained rays. This closes the endpoint gap in a purely interior polar test. -/
lemma mem_closure_roundedSector_polar {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) {z : ℂ} (hz : z ∈ closure (roundedSector ε θ)) :
    ∃ (r t : ℝ), t ∈ Icc (0 : ℝ) 1 ∧ ε * radialProfile t ≤ r ∧
      z = (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) := by
  let R := ‖z‖ + 1
  let K : Set (ℝ × ℝ) := (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1) ∩
    {p | ε * radialProfile p.2 ≤ p.1}
  let F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) *
    Complex.exp ((θ * smoothStep p.2 : ℝ) * I)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le (continuous_const.mul (contDiff_radialProfile.continuous.comp continuous_snd))
      continuous_fst)
  have hF : Continuous F := by dsimp [F, smoothStep]; fun_prop
  have hzK : z ∈ closure (F '' K) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hz (min δ 1) (by positivity)
    obtain ⟨r, t, ht, hr, he⟩ := (mem_roundedSector_iff_exists hε hθ hθ' w).mp hw
    have hr0 : 0 < r := (mul_pos hε (radialProfile_pos (Ioo_subset_Icc_self ht))).trans hr
    have hn : ‖w‖ = r := by rw [he, norm_polar hr0.le]
    have hrR : r ≤ R := by
      have hd : dist w z < 1 := by rw [dist_comm]; exact hzw.trans_le (min_le_right _ _)
      have ht := dist_triangle w z 0
      simp only [dist_zero_right] at ht
      dsimp [R]
      linarith
    refine ⟨w, ⟨(r, t), ⟨⟨⟨hr0.le, hrR⟩, Ioo_subset_Icc_self ht⟩, hr.le⟩, he.symm⟩,
      hzw.trans_le (min_le_left _ _)⟩
  obtain ⟨⟨r, t⟩, hrt, he⟩ := (hK.image hF).isClosed.closure_subset hzK
  exact ⟨r, t, hrt.1.2, hrt.2, he.symm⟩

/-- The literal new curve together with the two retained radial tails is the
entire model frontier. In particular it is the range of the already proved
regular injective C1 joined parametrization. -/
lemma frontier_roundedSector_subset_joined_range {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    frontier (roundedSector ε θ) ⊆ Set.range (joinedRounding ε θ) := by
  intro z hz
  obtain ⟨r, t, ht, hr, he⟩ := mem_closure_roundedSector_polar hε hθ hθ' hz.1
  have hr0 : 0 < r := (mul_pos hε (radialProfile_pos ht)).trans_le hr
  have hk : 0 < ε * Real.pi / 2 := by positivity
  by_cases ht0 : t = 0
  · have hre : ε ≤ r := by simpa [ht0, radialProfile] using hr
    refine ⟨(ε - r) / (ε * Real.pi / 2), ?_⟩
    have hu : (ε - r) / (ε * Real.pi / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hk.le
    rw [he]
    simp only [ht0, smoothStep_zero, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one, joinedRounding, piecewise, mem_Iic, hu, ite_true, bottomRay]
    congr 1
    field_simp
    <;> ring
  by_cases ht1 : t = 1
  · have hre : ε ≤ r := by simpa [ht1, radialProfile] using hr
    let u : ℝ := 1 + (r - ε) / (ε * Real.pi / 2)
    have hu : 1 ≤ u := by dsimp [u]; exact le_add_of_nonneg_right (div_nonneg (by linarith) hk.le)
    refine ⟨u, ?_⟩
    have hj : joinedRounding ε θ u = topRay ε θ u := by
      have hh := positiveJoinedRounding_on_top ε θ (t := 1 - u) (by linarith)
      simpa only [positiveJoinedRounding, sub_sub_cancel] using hh
    have hrad : ε + (ε * Real.pi / 2) * (u - 1) = r := by
      dsimp [u]
      rw [add_sub_cancel_left, mul_div_cancel₀ _ hk.ne']
      ring
    rw [hj, he]
    simp only [ht1, smoothStep_one, mul_one, topRay, hrad]
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have heq : r = ε * radialProfile t := by
    by_contra h
    have hr' : ε * radialProfile t < r := lt_of_le_of_ne hr (Ne.symm h)
    have hmem : z ∈ roundedSector ε θ := by rw [he]; exact (polar_mem_roundedSector_iff hε hθ hθ' hr0 hti).mpr hr'
    exact hz.2 (by simpa only [(isOpen_roundedSector ε θ).interior_eq] using hmem)
  refine ⟨t, ?_⟩
  rw [heq] at he
  simpa only [joinedRounding, piecewise, mem_Iic, not_le.mpr hti.1, ht.2,
    ite_false, ite_true, roundingArc] using he.symm


lemma polarTail_mem_closure_roundedSector {ε θ r t : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : ε < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * I) ∈ closure (roundedSector ε θ) := by
  let f : ℝ → ℂ := fun u => (r : ℂ) * Complex.exp ((θ * smoothStep u : ℝ) * I)
  have hf : Continuous f := by dsimp [f, smoothStep]; fun_prop
  have hi : Ioo (0 : ℝ) 1 ⊆ f ⁻¹' closure (roundedSector ε θ) := by
    intro u hu
    apply subset_closure
    apply (polar_mem_roundedSector_iff hε hθ hθ' (hε.trans hr) hu).mpr
    exact (mul_le_of_le_one_right hε.le (radialProfile_bounds (Ioo_subset_Icc_self hu)).2).trans_lt hr
  have hc := closure_minimal hi (isClosed_closure.preimage hf)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  exact hc ht

lemma bottomTail_mem_frontier_roundedSector {ε θ r : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : ε ≤ r) :
    (r : ℂ) ∈ frontier (roundedSector ε θ) := by
  rcases eq_or_lt_of_le hr with he | he
  · rw [← he, ← (roundingArc_endpoints ε θ).1]
    exact roundingArc_image_subset_frontier hε hθ hθ' ⟨0, by simp, rfl⟩
  · refine ⟨?_, ?_⟩
    · simpa using polarTail_mem_closure_roundedSector hε hθ hθ' he (by simp : (0 : ℝ) ∈ Icc 0 1)
    · intro hi
      have hm := (interior_subset hi).1
      have hn := (polar_mem_sector_iff (hε.trans he) ⟨le_rfl, hθ.le⟩ hθ').mp
        (show (r : ℂ) * Complex.exp ((0 : ℂ) * I) ∈ CircularExhaustion.sector θ by simpa using hm)
      exact (lt_irrefl (0 : ℝ)) hn.1

lemma topTail_mem_frontier_roundedSector {ε θ r : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : ε ≤ r) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ frontier (roundedSector ε θ) := by
  rcases eq_or_lt_of_le hr with he | he
  · rw [← he, ← (roundingArc_endpoints ε θ).2]
    exact roundingArc_image_subset_frontier hε hθ hθ' ⟨1, by simp, rfl⟩
  · refine ⟨?_, ?_⟩
    · simpa using polarTail_mem_closure_roundedSector hε hθ hθ' he (by simp : (1 : ℝ) ∈ Icc 0 1)
    · intro hi
      have hm := (interior_subset hi).1
      have hn := (polar_mem_sector_iff (hε.trans he) ⟨hθ.le, le_rfl⟩ hθ').mp hm
      exact (lt_irrefl θ) hn.2

lemma frontier_roundedSector_eq_range {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    frontier (roundedSector ε θ) = Set.range (joinedRounding ε θ) := by
  apply Subset.antisymm (frontier_roundedSector_subset_joined_range hε hθ hθ')
  rintro z ⟨t, rfl⟩
  by_cases ht0 : t ≤ 0
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ite_true, bottomRay]
    apply bottomTail_mem_frontier_roundedSector hε hθ hθ'
    have : ε * Real.pi / 2 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) ht0
    linarith
  by_cases ht1 : t ≤ 1
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ht1, ite_false, ite_true]
    exact roundingArc_image_subset_frontier hε hθ hθ' ⟨t, ⟨(not_le.mp ht0).le, ht1⟩, rfl⟩
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ht1, ite_false, topRay]
    apply topTail_mem_frontier_roundedSector hε hθ hθ'
    have : 0 ≤ ε * Real.pi / 2 * (t - 1) := mul_nonneg (by positivity) (by linarith)
    linarith

/-- The straight tails prevent remote branches from accumulating on a local
parametrized boundary patch. -/
lemma abs_le_one_add_norm_joinedRounding {ε θ : ℝ} (hε : 0 < ε) (t : ℝ) :
    |t| ≤ 1 + ‖joinedRounding ε θ t‖ / (ε * Real.pi / 2) := by
  have hk : 0 < ε * Real.pi / 2 := by positivity
  by_cases ht0 : t ≤ 0
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ite_true]
    rw [norm_bottomRay hε ht0, abs_of_nonpos ht0]
    have he : -t ≤ (ε - ε * Real.pi / 2 * t) / (ε * Real.pi / 2) := by
      rw [le_div_iff₀ hk]
      nlinarith
    linarith
  by_cases ht1 : t ≤ 1
  · rw [abs_of_pos (not_le.mp ht0)]
    have : 0 ≤ ‖joinedRounding ε θ t‖ / (ε * Real.pi / 2) := div_nonneg (norm_nonneg _) hk.le
    linarith
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ht1, ite_false]
    rw [norm_topRay hε (not_le.mp ht1).le, abs_of_pos (not_le.mp ht0)]
    have he : t - 1 ≤ (ε + ε * Real.pi / 2 * (t - 1)) / (ε * Real.pi / 2) := by
      rw [le_div_iff₀ hk]
      nlinarith
    linarith

lemma isClosedEmbedding_joinedRounding {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) : Topology.IsClosedEmbedding (joinedRounding ε θ) := by
  have hc := (contDiff_joinedRounding ε θ).continuous
  have hp : IsProperMap (joinedRounding ε θ) := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hc, ?_⟩
    intro K hK
    obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    let B : ℝ := 1 + M / (ε * Real.pi / 2)
    have hsub : (joinedRounding ε θ) ⁻¹' K ⊆ Icc (-B) B := by
      intro t ht
      have hn := abs_le_one_add_norm_joinedRounding hε (θ := θ) t
      have hm : ‖joinedRounding ε θ t‖ / (ε * Real.pi / 2) ≤ M / (ε * Real.pi / 2) :=
        div_le_div_of_nonneg_right (hM _ ht) (by positivity)
      exact abs_le.mp (hn.trans (by dsimp [B]; linarith))
    exact isCompact_Icc.of_isClosed_subset (hK.isClosed.preimage hc) hsub
  exact .of_continuous_injective_isClosedMap hc
    (joinedRounding_injective hε hθ hθ') hp.isClosedMap


lemma roundedSector_hasRegularBoundaryParametrizations {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) : HasRegularBoundaryParametrizations (roundedSector ε θ) := by
  intro p hp
  rw [frontier_roundedSector_eq_range hε hθ hθ'] at hp
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨W, hW, hpre⟩ := (isClosedEmbedding_joinedRounding hε hθ hθ').isInducing.isOpen_iff.mp
    (isOpen_Ioo : IsOpen (Ioo (a - 1) (a + 1)))
  let γ : ℝ → ℂ := fun t => joinedRounding ε θ (a + t)
  have hγ : ContDiff ℝ 1 γ := (contDiff_joinedRounding ε θ).comp (contDiff_const.add contDiff_id)
  have hderiv (t : ℝ) : HasDerivAt γ (deriv (joinedRounding ε θ) (a + t)) t := by
    have hh := ((contDiff_joinedRounding ε θ).differentiable (by norm_num) (a + t)).hasDerivAt
    simpa only [Function.comp_def, one_smul] using
      hh.scomp t ((hasDerivAt_id t).const_add a)
  refine ⟨1, W, γ, by norm_num, hW, ?_, by simp [γ], hγ.contDiffOn, ?_, ?_, ?_⟩
  · have ha : a ∈ (joinedRounding ε θ) ⁻¹' W := by rw [hpre]; constructor <;> linarith
    exact ha
  · intro t _
    rw [(hderiv t).deriv]
    exact joinedRounding_regular hε hθ _
  · intro s _ t _ he
    have := joinedRounding_injective hε hθ hθ' he
    linarith
  · rw [frontier_roundedSector_eq_range hε hθ hθ']
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨a + t, rfl⟩, ?_⟩
      have ha : a + t ∈ (joinedRounding ε θ) ⁻¹' W := by
        rw [hpre]
        constructor <;> linarith [ht.1, ht.2]
      exact ha
    · rintro ⟨⟨t, rfl⟩, htW⟩
      have ht : t ∈ Ioo (a - 1) (a + 1) := by
        rw [← hpre]
        exact htW
      exact ⟨t - a, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by dsimp [γ]; congr 1; ring⟩


lemma contDiff_normalChartMap (ε θ a : ℝ) : ContDiff ℝ 1 (normalChartMap ε θ a) :=
  ((contDiff_positiveJoinedRounding ε θ).comp Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.smul contDiff_const)

lemma hasFDerivAt_normalChartMap (ε θ a : ℝ) :
    HasFDerivAt (normalChartMap ε θ a)
      (ContinuousLinearMap.mul ℝ ℂ (deriv (positiveJoinedRounding ε θ) a)) (a : ℂ) := by
  have hγ := ((contDiff_positiveJoinedRounding ε θ).differentiable (by norm_num) a).hasDerivAt
  have hre := hγ.hasFDerivAt.comp (a : ℂ) Complex.reCLM.hasFDerivAt
  have him := (Complex.imCLM.hasFDerivAt (x := (a : ℂ))).smul_const
    (I * deriv (positiveJoinedRounding ε θ) a)
  have hh := hre.add him
  have hd : (ContinuousLinearMap.toSpanSingleton ℝ (deriv (positiveJoinedRounding ε θ) a)).comp Complex.reCLM +
      Complex.imCLM.smulRight (I * deriv (positiveJoinedRounding ε θ) a) =
        ContinuousLinearMap.mul ℝ ℂ (deriv (positiveJoinedRounding ε θ) a) := by
    ext z
    change (z.re : ℂ) * deriv (positiveJoinedRounding ε θ) a +
      (z.im : ℂ) * (I * deriv (positiveJoinedRounding ε θ) a) =
        deriv (positiveJoinedRounding ε θ) a * z
    conv_rhs => rw [← Complex.re_add_im z]
    ring
  rw [hd] at hh
  exact hh

/-- A genuine C1 inverse function theorem at every point of the literal joined
curve, including both joins. The map uses a constant normal, so no C2 premise
has been introduced. -/
lemma exists_normal_coordinates {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (a : ℝ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (e : ℂ → ℂ) = normalChartMap ε θ a ∧ (a : ℂ) ∈ e.source ∧
      positiveJoinedRounding ε θ a ∈ e.target ∧
      e.symm (positiveJoinedRounding ε θ a) = (a : ℂ) ∧
      ContDiffAt ℝ 1 e.symm (positiveJoinedRounding ε θ a) := by
  let v := deriv (positiveJoinedRounding ε θ) a
  have hv : v ≠ 0 := positiveJoinedRounding_regular hε hθ a
  let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 v hv)
  have hd : HasFDerivAt (normalChartMap ε θ a) (L : ℂ →L[ℝ] ℂ) (a : ℂ) := by
    convert hasFDerivAt_normalChartMap ε θ a using 1
    ext z
    simp [L, v, ContinuousLinearMap.mul_apply']
  have hc := (contDiff_normalChartMap ε θ a).contDiffAt (x := (a : ℂ))
  let e := hc.toOpenPartialHomeomorph (f' := L) (normalChartMap ε θ a) hd (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hsym : (e.symm : ℂ → ℂ) = hc.localInverse (f' := L) hd (by norm_num) := rfl
  have heq : normalChartMap ε θ a (a : ℂ) = positiveJoinedRounding ε θ a := by
    simp [normalChartMap]
  refine ⟨e, rfl, hc.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_, ?_, ?_⟩
  · simpa only [heq] using hc.image_mem_toOpenPartialHomeomorph_target hd (by norm_num)
  · rw [hsym]
    simpa only [heq] using hc.localInverse_apply_image (f' := L) hd (by norm_num)
  · rw [hsym]
    simpa only [heq] using hc.to_localInverse (f' := L) hd (by norm_num)


lemma isClosedEmbedding_positiveJoinedRounding {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) : Topology.IsClosedEmbedding (positiveJoinedRounding ε θ) := by
  let h : ℝ ≃ₜ ℝ :=
    { toFun := fun t => 1 - t
      invFun := fun t => 1 - t
      left_inv := fun t => sub_sub_cancel 1 t
      right_inv := fun t => sub_sub_cancel 1 t
      continuous_toFun := continuous_const.sub continuous_id
      continuous_invFun := continuous_const.sub continuous_id }
  exact (isClosedEmbedding_joinedRounding hε hθ hθ').comp h.isClosedEmbedding

lemma frontier_roundedSector_eq_positive_range {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    frontier (roundedSector ε θ) = Set.range (positiveJoinedRounding ε θ) := by
  rw [frontier_roundedSector_eq_range hε hθ hθ']
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨1 - t, by simp [positiveJoinedRounding]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨1 - t, rfl⟩

/-- A C1 coordinate function whose actual zero set is exactly the model
frontier near each point. The negative-side condition required by D04 is a
separate obligation; it is not assumed or asserted by this lemma. -/
lemma exists_model_zero_homeomorph {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (a : ℝ) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ) (W : Set ℂ),
      IsOpen W ∧ positiveJoinedRounding ε θ a ∈ W ∧ W ⊆ e.target ∧
      ContDiffOn ℝ 1 e.symm W ∧
      (∀ z ∈ W, fderiv ℝ (fun w => (e.symm w).im) z ≠ 0) ∧
      e.symm (positiveJoinedRounding ε θ a) = (a : ℂ) ∧
      ∀ z ∈ W, z ∈ frontier (roundedSector ε θ) ↔ (e.symm z).im = 0 := by
  obtain ⟨e, he, hea, hep, heinv, hc⟩ := exists_normal_coordinates hε hθ a
  let v := deriv (positiveJoinedRounding ε θ) a
  have hv : v ≠ 0 := positiveJoinedRounding_regular hε hθ a
  let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 v hv)
  have hd : HasFDerivAt e (L : ℂ →L[ℝ] ℂ) (e.symm (positiveJoinedRounding ε θ a)) := by
    rw [heinv, he]
    convert hasFDerivAt_normalChartMap ε θ a using 1
    ext z
    simp [L, v, ContinuousLinearMap.mul_apply']
  have hdinv := e.hasFDerivAt_symm hep hd
  let φ : ℂ → ℝ := fun z => (e.symm z).im
  have hφd : HasFDerivAt φ (Complex.imCLM.comp (L.symm : ℂ →L[ℝ] ℂ))
      (positiveJoinedRounding ε θ a) := Complex.imCLM.hasFDerivAt.comp _ hdinv
  have hφne : fderiv ℝ φ (positiveJoinedRounding ε θ a) ≠ 0 := by
    rw [hφd.fderiv]
    intro h
    have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f (L I)) h
    simpa using hh
  have hφc : ContDiffAt ℝ 1 φ (positiveJoinedRounding ε θ a) := Complex.imCLM.contDiff.contDiffAt.comp _ hc
  have hNd : {z | fderiv ℝ φ z ≠ 0} ∈ 𝓝 (positiveJoinedRounding ε θ a) :=
    (hφc.continuousAt_fderiv (by norm_num)).preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hφne)
  obtain ⟨N₁, hN₁d, hN₁, hpN₁⟩ := _root_.mem_nhds_iff.mp hNd
  have hreal : ((↑) : ℝ → ℂ) ⁻¹' e.source ∈ 𝓝 a :=
    Complex.continuous_ofReal.continuousAt (e.open_source.mem_nhds hea)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hreal
  obtain ⟨W₀, hW₀, hpre⟩ := (isClosedEmbedding_positiveJoinedRounding hε hθ hθ').isInducing.isOpen_iff.mp
    (isOpen_ball : IsOpen (ball a r))
  obtain ⟨N, hN, hcN⟩ := hc.contDiffOn (m := 1) le_rfl (by norm_num)
  obtain ⟨N₀, hN₀N, hN₀, hpN₀⟩ := _root_.mem_nhds_iff.mp hN
  let W := (e.target ∩ W₀ ∩ N₀) ∩ N₁
  have hpW₀ : positiveJoinedRounding ε θ a ∈ W₀ := by
    have ha : a ∈ (positiveJoinedRounding ε θ) ⁻¹' W₀ := by
      rw [hpre]
      exact mem_ball_self hr
    exact ha
  refine ⟨e, W, ((e.open_target.inter hW₀).inter hN₀).inter hN₁,
    ⟨⟨⟨hep, hpW₀⟩, hpN₀⟩, hpN₁⟩, (fun z hz => hz.1.1.1), hcN.mono (fun z hz => hN₀N hz.1.2),
    (fun z hz => hN₁d hz.2), heinv, ?_⟩
  intro z hz
  constructor
  · intro hzfront
    rw [frontier_roundedSector_eq_positive_range hε hθ hθ'] at hzfront
    obtain ⟨t, rfl⟩ := hzfront
    have ht : t ∈ (positiveJoinedRounding ε θ) ⁻¹' W₀ := hz.1.1.2
    rw [hpre] at ht
    have htS : (t : ℂ) ∈ e.source := hball ht
    have hinv := e.left_inv htS
    rw [he] at hinv
    simpa only [normalChartMap, Complex.ofReal_re, Complex.ofReal_im, zero_smul,
      add_zero, hinv, Complex.ofReal_im] using congrArg Complex.im hinv
  · intro hz0
    have hzx := e.right_inv hz.1.1.1
    have hez : e (e.symm z) = positiveJoinedRounding ε θ (e.symm z).re := by
      rw [he]
      simp only [normalChartMap, hz0, zero_smul, add_zero]
    rw [frontier_roundedSector_eq_positive_range hε hθ hθ']
    exact ⟨(e.symm z).re, hez.symm.trans hzx⟩

/-- Zero-level version of the stronger inverse-homeomorphism construction. -/
lemma exists_model_zero_chart {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (a : ℝ) :
    ∃ (W : Set ℂ) (ψ : ℂ → ℂ), IsOpen W ∧ positiveJoinedRounding ε θ a ∈ W ∧
      ContDiffOn ℝ 1 ψ W ∧
      (∀ z ∈ W, fderiv ℝ (fun w => (ψ w).im) z ≠ 0) ∧
      ψ (positiveJoinedRounding ε θ a) = (a : ℂ) ∧
      ∀ z ∈ W, z ∈ frontier (roundedSector ε θ) ↔ (ψ z).im = 0 := by
  obtain ⟨e, W, hW, hpW, _, hc, hd, he, hf⟩ :=
    exists_model_zero_homeomorph hε hθ hθ' a
  exact ⟨W, e.symm, hW, hpW, hc, hd, he, hf⟩

/-- Points strictly between the two complementary rays are genuinely exterior,
including with respect to closure. The angular interval still has width < 2π. -/
lemma complementary_polar_not_mem_closure {ε θ r b : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) (hr : 0 < r)
    (hb : θ < b) (hb' : b < 2 * Real.pi) :
    (r : ℂ) * Complex.exp ((b : ℂ) * I) ∉ closure (roundedSector ε θ) := by
  intro hz
  obtain ⟨s, t, ht, hs, he⟩ := mem_closure_roundedSector_polar hε hθ hθ' hz
  have hs0 : 0 < s := (mul_pos hε (radialProfile_pos ht)).trans_le hs
  have hst := smoothStep_mem_Icc ht
  have ha : θ * smoothStep t ∈ Icc (0 : ℝ) b :=
    ⟨mul_nonneg hθ.le hst.1, (mul_le_of_le_one_right hθ.le hst.2).trans hb.le⟩
  have hh := angle_eq_of_polar_eq hr hs0 ⟨(hθ.trans hb).le, le_rfl⟩ ha hb' he
  linarith [ha.2, mul_le_of_le_one_right hθ.le hst.2]

/-- Both retained rays are approached from the open exterior of the rounded set. -/
lemma rays_mem_closure_interior_compl {ε θ r : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) (hr : 0 < r) :
    (r : ℂ) ∈ closure (interior (roundedSector ε θ)ᶜ) ∧
    (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈
      closure (interior (roundedSector ε θ)ᶜ) := by
  let f : ℝ → ℂ := fun b => (r : ℂ) * Complex.exp ((b : ℂ) * I)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hi : Ioo θ (2 * Real.pi) ⊆
      f ⁻¹' closure (interior (roundedSector ε θ)ᶜ) := by
    intro b hb
    apply subset_closure
    rw [interior_compl]
    exact complementary_polar_not_mem_closure hε hθ hθ' hr hb.1 hb.2
  have hc := closure_minimal hi (isClosed_closure.preimage hf)
  rw [closure_Ioo hθ'.ne] at hc
  have htop := hc (left_mem_Icc.mpr hθ'.le)
  have hbot := hc (right_mem_Icc.mpr hθ'.le)
  constructor
  · simpa [f, Complex.exp_mul_I, Real.cos_two_pi, Real.sin_two_pi] using hbot
  · exact htop

/-- Strict radial subtip points give exterior points approaching the entire
new arc. Two closure arguments retain both endpoint joins. -/
lemma roundingArc_mem_closure_interior_compl {ε θ : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    roundingArc ε θ '' Icc (0 : ℝ) 1 ⊆
      closure (interior (roundedSector ε θ)ᶜ) := by
  have htip : interior (sectorTip ε θ) ⊆ interior (roundedSector ε θ)ᶜ :=
    interior_mono (fun z hz h => h.2 hz)
  have hinner : Ioo (0 : ℝ) 1 ⊆
      (roundingArc ε θ) ⁻¹' closure (interior (roundedSector ε θ)ᶜ) := by
    intro t ht
    let f : ℝ → ℂ := fun s => (s * ε * radialProfile t : ℝ) *
      Complex.exp ((θ * smoothStep t : ℝ) * I)
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hi : Ioo (0 : ℝ) 1 ⊆ f ⁻¹' closure (interior (roundedSector ε θ)ᶜ) := by
      intro s hs
      apply subset_closure
      apply htip
      have hp := radialProfile_pos (Ioo_subset_Icc_self ht)
      apply polar_mem_interior_sectorTip hε hθ hθ' (mul_pos (mul_pos hs.1 hε) hp) ht
      simpa only [mul_assoc, one_mul] using
        mul_lt_mul_of_pos_right hs.2 (mul_pos hε hp)
    have hc := closure_minimal hi (isClosed_closure.preimage hf)
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
    simpa [f, roundingArc] using hc (by simp : (1 : ℝ) ∈ Icc 0 1)
  have hc := closure_minimal hinner
    (isClosed_closure.preimage (contDiff_roundingArc ε θ).continuous)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  rintro z ⟨t, ht, rfl⟩
  exact hc ht

/-- The model has no slit boundary: every boundary point is approached by
points in the interior of the complement. -/
lemma frontier_roundedSector_subset_closure_interior_compl {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    frontier (roundedSector ε θ) ⊆ closure (interior (roundedSector ε θ)ᶜ) := by
  rw [frontier_roundedSector_eq_range hε hθ hθ']
  rintro z ⟨t, rfl⟩
  by_cases ht0 : t ≤ 0
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ite_true, bottomRay]
    exact (rays_mem_closure_interior_compl hε hθ hθ' (by
      have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ ε * Real.pi / 2 by positivity) ht0
      linarith)).1
  by_cases ht1 : t ≤ 1
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ht1, ite_false, ite_true]
    exact roundingArc_mem_closure_interior_compl hε hθ hθ'
      ⟨t, ⟨(not_le.mp ht0).le, ht1⟩, rfl⟩
  · simp only [joinedRounding, piecewise, mem_Iic, ht0, ht1, ite_false, topRay]
    exact (rays_mem_closure_interior_compl hε hθ hθ' (by
      have hh := mul_nonneg (show 0 ≤ ε * Real.pi / 2 by positivity)
        (show 0 ≤ t - 1 by linarith [not_le.mp ht1])
      linarith)).2

/-- A connected subset missing the boundary of an open set lies entirely
inside it or entirely in the open exterior. -/
lemma preconnected_subset_one_side {S U : Set ℂ} (hU : IsOpen U)
    (hS : IsPreconnected S) (hfront : ∀ z ∈ S, z ∉ frontier U) :
    S ⊆ U ∨ S ⊆ interior Uᶜ := by
  apply IsPreconnected.subset_or_subset hU isOpen_interior
    (Set.disjoint_left.mpr (fun z hz he => (show z ∈ Uᶜ from interior_subset he) hz)) _ hS
  intro z hz
  by_cases hi : z ∈ U
  · exact Or.inl hi
  · right
    rw [interior_compl]
    intro hc
    exact hfront z hz (by rw [hU.frontier_eq]; exact ⟨hc, hi⟩)

/-- A local boundary chart has exactly one inside half if both the open set
and the interior of its complement approach the center. In particular a slit
is excluded by an explicit hypothesis, rather than by parametrization alone. -/
lemma side_of_boundary_chart {U : Set ℂ} (hU : IsOpen U)
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hS : ball a r ⊆ e.source)
    (hfront : ∀ w ∈ ball a r, e w ∈ frontier U ↔ w.im = 0)
    (hin : e a ∈ closure U) (hout : e a ∈ closure (interior Uᶜ)) :
    (∀ w ∈ ball a r, e w ∈ U ↔ w.im < 0) ∨
      (∀ w ∈ ball a r, e w ∈ U ↔ 0 < w.im) := by
  let P : Set ℂ := ball a r ∩ {w | 0 < w.im}
  let N : Set ℂ := ball a r ∩ {w | w.im < 0}
  have hPS : P ⊆ e.source := fun w hw => hS hw.1
  have hNS : N ⊆ e.source := fun w hw => hS hw.1
  have hP : IsPreconnected (e '' P) :=
    ((convex_ball a r).inter
      (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear (0 : ℝ))).isPreconnected.image e
      (e.continuousOn.mono hPS)
  have hN : IsPreconnected (e '' N) :=
    ((convex_ball a r).inter
      (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear (0 : ℝ))).isPreconnected.image e
      (e.continuousOn.mono hNS)
  have hPf : ∀ z ∈ e '' P, z ∉ frontier U := by
    rintro z ⟨w, hw, rfl⟩ hh
    exact hw.2.ne' ((hfront w hw.1).mp hh)
  have hNf : ∀ z ∈ e '' N, z ∉ frontier U := by
    rintro z ⟨w, hw, rfl⟩ hh
    exact hw.2.ne ((hfront w hw.1).mp hh)
  have hW := e.isOpen_image_of_subset_source isOpen_ball hS
  have haW : e a ∈ e '' ball a r := ⟨a, mem_ball_self hr, rfl⟩
  obtain ⟨zi, ⟨wi, hwi, rfl⟩, hzi⟩ := mem_closure_iff.mp hin _ hW haW
  obtain ⟨zo, ⟨wo, hwo, rfl⟩, hzo⟩ := mem_closure_iff.mp hout _ hW haW
  have hzne : ∀ w ∈ ball a r, e w ∈ U → w.im ≠ 0 := by
    intro w hw hi he
    have hf := (hfront w hw).mpr he
    exact hf.2 (by simpa only [hU.interior_eq] using hi)
  have hzone : wo.im ≠ 0 := by
    intro he
    have hf := (hfront wo hwo).mpr he
    rw [interior_compl] at hzo
    exact hzo hf.1
  have hcover : ∀ w ∈ ball a r, w.im ≠ 0 → e w ∈ e '' P ∪ e '' N := by
    intro w hw hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inr ⟨w, ⟨hw, h⟩, rfl⟩
    · exact Or.inl ⟨w, ⟨hw, h⟩, rfl⟩
  rcases preconnected_subset_one_side hU hP hPf with hPi | hPo <;>
    rcases preconnected_subset_one_side hU hN hNf with hNi | hNo
  · obtain hh | hh := hcover wo hwo hzone
    · exact False.elim ((interior_subset hzo) (hPi hh))
    · exact False.elim ((interior_subset hzo) (hNi hh))
  · right
    intro w hw
    constructor
    · intro hi
      rcases lt_or_gt_of_ne (hzne w hw hi) with hn | hp
      · exact False.elim ((interior_subset (hNo ⟨w, ⟨hw, hn⟩, rfl⟩)) hi)
      · exact hp
    · intro hp
      exact hPi ⟨w, ⟨hw, hp⟩, rfl⟩
  · left
    intro w hw
    constructor
    · intro hi
      rcases lt_or_gt_of_ne (hzne w hw hi) with hn | hp
      · exact hn
      · exact False.elim ((interior_subset (hPo ⟨w, ⟨hw, hp⟩, rfl⟩)) hi)
    · intro hn
      exact hNi ⟨w, ⟨hw, hn⟩, rfl⟩
  · obtain hh | hh := hcover wi hwi (hzne wi hwi hzi)
    · exact False.elim ((interior_subset (hPo hh)) hzi)
    · exact False.elim ((interior_subset (hNo hh)) hzi)

/-- Genuine negative-side functions for the entire rounded model, including
both tangent-matched joins. The sign is selected by the proved set side. -/
lemma roundedSector_hasC1DefiningFunctions {ε θ : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    HasC1DefiningFunctions (roundedSector ε θ) := by
  intro p hp
  obtain ⟨a, rfl⟩ := (frontier_roundedSector_eq_positive_range hε hθ hθ' ▸ hp)
  let p := positiveJoinedRounding ε θ a
  obtain ⟨e, W, hW, hpW, hWe, hc, hd, he, hf⟩ :=
    exists_model_zero_homeomorph hε hθ hθ' a
  have hpt : p ∈ e.target := hWe hpW
  have hea : (a : ℂ) ∈ e.source := by rw [← he]; exact e.map_target hpt
  have heap : e (a : ℂ) = p := by rw [← he]; exact e.right_inv hpt
  have haS : (a : ℂ) ∈ e.source ∩ e ⁻¹' W := ⟨hea, by change e (a : ℂ) ∈ W; rw [heap]; exact hpW⟩
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp
    ((e.isOpen_inter_preimage hW).mem_nhds haS)
  have hrsource : ball (a : ℂ) r ⊆ e.source := fun z hz => (hrS hz).1
  let W' := e '' ball (a : ℂ) r
  have hW' : IsOpen W' := e.isOpen_image_of_subset_source isOpen_ball hrsource
  have hW'W : W' ⊆ W := by
    rintro z ⟨w, hw, rfl⟩
    exact (hrS hw).2
  have hpW' : p ∈ W' := ⟨(a : ℂ), mem_ball_self hr, heap⟩
  have hside := side_of_boundary_chart (isOpen_roundedSector ε θ) e hr hrsource
    (fun w hw => by rw [hf _ ((hrS hw).2), e.left_inv (hrsource hw)])
    (by rw [heap]; exact hp.1)
    (by rw [heap]; exact frontier_roundedSector_subset_closure_interior_compl hε hθ hθ' hp)
  let φ : ℂ → ℝ := fun z => (e.symm z).im
  have hφ : ContDiffOn ℝ 1 φ W' :=
    Complex.imCLM.contDiff.comp_contDiffOn (hc.mono hW'W)
  have hφside : (∀ z ∈ W', z ∈ roundedSector ε θ ↔ φ z < 0) ∨
      (∀ z ∈ W', z ∈ roundedSector ε θ ↔ 0 < φ z) := by
    rcases hside with hs | hs
    · left
      rintro z ⟨w, hw, rfl⟩
      simpa only [φ, e.left_inv (hrsource hw)] using hs w hw
    · right
      rintro z ⟨w, hw, rfl⟩
      simpa only [φ, e.left_inv (hrsource hw)] using hs w hw
  rcases hφside with hs | hs
  · exact ⟨W', φ, hW', hpW', hφ, hs, fun z hz => hf z (hW'W hz),
      fun z hz _ => hd z (hW'W hz)⟩
  · refine ⟨W', -φ, hW', hpW', hφ.neg, ?_, ?_, ?_⟩
    · intro z hz
      simpa only [Pi.neg_apply, neg_lt_zero] using hs z hz
    · intro z hz
      simpa only [Pi.neg_apply, neg_eq_zero] using hf z (hW'W hz)
    · intro z hz _
      rw [fderiv_neg]
      exact neg_ne_zero.mpr (hd z (hW'W hz))

/-- The complete local model defining-function result, as an independent Spec. -/
theorem model_defining_functions :
    Specs.D12Complex.Ch14.CircularCornerRounding.model_defining_functions_type := by
  exact fun ε θ hε hθ hθ' => roundedSector_hasC1DefiningFunctions hε hθ hθ'

/-- Local functions expressed on ℂ transport to exactly the Euclidean plane
used by D04. Surjectivity of the real isometry preserves nonzero differentials. -/
theorem classical_domain_bridge :
    Specs.D12Complex.Ch14.CircularCornerRounding.classical_domain_bridge_type := by
  intro V hb ho hd
  let e := realPlane.toHomeomorph
  refine ⟨by norm_num, ?_, e.isOpenMap V ho, ?_⟩
  · exact realPlane.lipschitzWith.isBounded_image hb
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := (e.image_frontier V ▸ hp)
    obtain ⟨W, ρ, hW, hzW, hc, hneg, hzero, hne⟩ := hd z hz
    let U := e '' W
    let σ := ρ ∘ realPlane.symm
    have hU : IsOpen U := e.isOpenMap W hW
    have hσ : ContDiffOn ℝ 1 σ U := by
      apply hc.comp realPlane.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      rintro x ⟨w, hw, rfl⟩
      change realPlane.symm (realPlane w) ∈ W
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hw
    have hmem : ∀ x, x ∈ realPlane '' V ↔ realPlane.symm x ∈ V := by
      intro x
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [LinearIsometryEquiv.symm_apply_apply] using hw
      · intro hx
        exact ⟨realPlane.symm x, hx, realPlane.apply_symm_apply x⟩
    have hfr : ∀ x, x ∈ frontier (realPlane '' V) ↔ realPlane.symm x ∈ frontier V := by
      intro x
      change x ∈ frontier (e '' V) ↔ e.symm x ∈ frontier V
      rw [← e.image_frontier]
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [Homeomorph.symm_apply_apply] using hw
      · intro hx
        exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    have hUW : ∀ x ∈ U, realPlane.symm x ∈ W := by
      rintro x ⟨w, hw, rfl⟩
      change realPlane.symm (realPlane w) ∈ W
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hw
    refine ⟨U, σ, ⟨z, hzW, rfl⟩, hU, hσ, ?_, ?_, ?_⟩
    · intro x hx
      exact (hmem x).trans (hneg _ (hUW x hx))
    · intro x hx
      exact (hfr x).trans (hzero _ (hUW x hx))
    · intro x hx hσx
      have hh := hne _ (hUW x hx) hσx
      change fderiv ℝ (ρ ∘ realPlane.symm.toContinuousLinearEquiv) x ≠ 0
      rw [ContinuousLinearEquiv.comp_right_fderiv]
      intro h
      apply hh
      ext w
      have hw := congrArg (fun f => (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (realPlane w)) h
      change (fderiv ℝ ρ (realPlane.symm x)) (realPlane.symm (realPlane w)) = 0 at hw
      simpa only [LinearIsometryEquiv.symm_apply_apply, zero_apply] using hw

/-- Defining functions pull back through a genuine C1 diffeomorphism on
its open source. The chart relation carries the actual set side and frontier. -/
lemma local_defining_function_of_chart {U V : Set ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (he : e.IsImage U V)
    (hc : ContDiffOn ℝ 1 e e.source) (hci : ContDiffOn ℝ 1 e.symm e.target)
    (hV : HasC1DefiningFunctions V) {p : ℂ} (hp : p ∈ e.source) (hpf : p ∈ frontier U) :
    ∃ (W : Set ℂ) (ρ : ℂ → ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ 1 ρ W ∧
      (∀ z ∈ W, z ∈ U ↔ ρ z < 0) ∧
      (∀ z ∈ W, z ∈ frontier U ↔ ρ z = 0) ∧
      ∀ z ∈ W, ρ z = 0 → fderiv ℝ ρ z ≠ 0 := by
  obtain ⟨W, ρ, hW, hpW, hρ, hn, hz, hd⟩ := hV _ ((he.frontier hp).mpr hpf)
  let N := e.source ∩ e ⁻¹' W
  have hN : IsOpen N := e.isOpen_inter_preimage hW
  have hρc : ContDiffOn ℝ 1 (ρ ∘ e) N :=
    hρ.comp (hc.mono inter_subset_left) (fun z hz => hz.2)
  refine ⟨N, ρ ∘ e, hN, ⟨hp, hpW⟩, hρc, ?_, ?_, ?_⟩
  · intro z hzN
    exact (he hzN.1).symm.trans (hn _ hzN.2)
  · intro z hzN
    exact (he.frontier hzN.1).symm.trans (hz _ hzN.2)
  · intro z hzN hz0
    have hρne := hd _ hzN.2 hz0
    have hez := (hc.contDiffAt (e.open_source.mem_nhds hzN.1)).differentiableAt (by norm_num)
    have heiz := (hci.contDiffAt (e.open_target.mem_nhds (e.map_source hzN.1))).differentiableAt (by norm_num)
    have hρz := (hρ.contDiffAt (hW.mem_nhds hzN.2)).differentiableAt (by norm_num)
    have hinv : (fderiv ℝ e z).comp (fderiv ℝ e.symm (e z)) =
        ContinuousLinearMap.id ℝ ℂ := by
      have hez' : HasFDerivAt e (fderiv ℝ e z) (e.symm (e z)) := by
        simpa only [e.left_inv hzN.1] using hez.hasFDerivAt
      have hcomp := hez'.comp (e z) heiz.hasFDerivAt
      have heq : (id : ℂ → ℂ) =ᶠ[𝓝 (e z)] (e ∘ e.symm) :=
        (e.eventually_right_inverse (e.map_source hzN.1)).mono (fun y hy => hy.symm)
      have hi := hcomp.congr_of_eventuallyEq heq
      exact hi.unique (hasFDerivAt_id (e z))
    rw [fderiv_comp z hρz hez]
    intro h
    apply hρne
    have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f.comp (fderiv ℝ e.symm (e z))) h
    simpa only [ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.zero_comp] using hh

/-- The angle-π sector is exactly the upper half-plane, not merely a set
with a straight parametrized boundary. -/
lemma sector_pi_eq_halfplane : CircularExhaustion.sector Real.pi = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨r, t, hr, ht, htπ, rfl⟩
    change 0 < ((r : ℂ) * Complex.exp ((t : ℂ) * I)).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.exp_ofReal_mul_I_im] using mul_pos hr (Real.sin_pos_of_mem_Ioo ⟨ht, htπ⟩)
  · intro hz
    change 0 < z.im at hz
    have hz0 : z ≠ 0 := by intro he; simpa only [he, Complex.zero_im, lt_self_iff_false] using hz
    have harg : 0 < z.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) (by
      intro h
      have hi := Complex.norm_mul_sin_arg z
      rw [← h, Real.sin_zero, mul_zero] at hi
      linarith)
    exact ⟨‖z‖, z.arg, norm_pos_iff.mpr hz0, harg,
      Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne'), (Complex.norm_mul_exp_arg_mul_I z).symm⟩

/-- At the original smooth boundary charts a single literal defining function
suffices; no boundedness of the model half-plane is asserted. -/
lemma sector_pi_hasC1DefiningFunctions : HasC1DefiningFunctions (CircularExhaustion.sector Real.pi) := by
  have hhalf : CircularExhaustion.sector Real.pi = Complex.imCLM ⁻¹' Ioi (0 : ℝ) :=
    sector_pi_eq_halfplane
  have hsurj : Function.Surjective Complex.imCLM := fun r =>
    ⟨(r : ℂ) * I, by simp⟩
  have hfront : frontier (CircularExhaustion.sector Real.pi) = {z : ℂ | z.im = 0} := by
    rw [hhalf, Complex.imCLM.frontier_preimage hsurj, frontier_Ioi]
    rfl
  intro p hp
  refine ⟨univ, fun z => -z.im, isOpen_univ, mem_univ _, Complex.imCLM.contDiff.neg.contDiffOn,
    ?_, ?_, ?_⟩
  · intro z _
    rw [sector_pi_eq_halfplane]
    change 0 < z.im ↔ -z.im < 0
    exact neg_lt_zero.symm
  · intro z _
    rw [hfront]
    exact neg_eq_zero.symm
  · intro z _ _
    have hd : HasFDerivAt (fun z : ℂ => -z.im) (-Complex.imCLM) z :=
      (Complex.imCLM.hasFDerivAt (x := z)).neg
    rw [hd.fderiv]
    intro h
    have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f I) h
    norm_num at hh

/-- A nonzero real scalar differential on the complex plane can be completed
to an invertible planar differential without choosing a manifold certificate. -/
lemma scalar_flattening_chart {ρ : ℂ → ℝ} {p : ℂ} {W : Set ℂ}
    (hW : IsOpen W) (hpW : p ∈ W) (hc : ContDiffOn ℝ 1 ρ W)
    (hd : fderiv ℝ ρ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      p ∈ e.source ∧ ContDiffAt ℝ 1 e.symm (e p) ∧
      (∀ z : ℂ, (e z).im = ρ z) ∧ ContDiffOn ℝ 1 e W := by
  let d := fderiv ℝ ρ p
  have heval (z : ℂ) : d z = z.re * d 1 + z.im * d I := by
    have hz : z = z.re • (1 : ℂ) + z.im • I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
  let c : ℂ := (d I : ℂ) + (d 1 : ℂ) * I
  have hcn : c ≠ 0 := by
    intro hc0
    have h1 : d 1 = 0 := by simpa only [c, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, zero_im] using congrArg Complex.im hc0
    have hi : d I = 0 := by simpa only [c, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, zero_re] using congrArg Complex.re hc0
    apply hd
    ext z
    change d z = 0
    rw [heval z, h1, hi]; simp
  let M : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ I
  let F : ℂ → ℂ := fun z => (d (I * z) : ℂ) + (ρ z : ℂ) * I
  let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hcn)
  have hcFOn : ContDiffOn ℝ 1 F W :=
    ((Complex.ofRealCLM.comp (d.comp M)).contDiff.contDiffOn).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hc).mul contDiffOn_const)
  have hcF : ContDiffAt ℝ 1 F p := hcFOn.contDiffAt (hW.mem_nhds hpW)
  have hdF : HasFDerivAt F (L : ℂ →L[ℝ] ℂ) p := by
    have h1 := (Complex.ofRealCLM.comp (d.comp M)).hasFDerivAt (x := p)
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp p
      ((hc.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by norm_num)).hasFDerivAt).mul_const I
    convert h1.add h2 using 1
    · rfl
    · ext z
      change c * z = (d (I * z) : ℂ) + I * (d z : ℂ)
      rw [heval (I * z), heval z]
      simp only [mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, zero_add,
        ofReal_add, ofReal_mul, ofReal_neg, c]
      conv_lhs => rw [← Complex.re_add_im z]
      ring_nf
      simp only [Complex.I_sq]
      ring
  let e := hcF.toOpenPartialHomeomorph F hdF (by norm_num : (1 : ℕ∞ω) ≠ 0)
  refine ⟨e, hcF.mem_toOpenPartialHomeomorph_source hdF (by norm_num), ?_, ?_, hcFOn⟩
  · exact hcF.to_localInverse (f' := L) hdF (by norm_num)
  · intro z
    change (F z).im = ρ z
    simp [F]

/-- A proved defining function gives a regular C1 parametrization of the
actual frontier. This supplies the parametrizations after finite chart gluing. -/
lemma hasRegularBoundaryParametrizations_of_defining_functions {V : Set ℂ}
    (hV : HasC1DefiningFunctions V) : HasRegularBoundaryParametrizations V := by
  intro p hp
  obtain ⟨W, ρ, hW, hpW, hc, _, hz, hd⟩ := hV p hp
  have hρp : ρ p = 0 := (hz p hpW).mp hp
  obtain ⟨e, hpe, hci, heim, hce⟩ := scalar_flattening_chart hW hpW hc (hd p hpW hρp)
  have hep := e.map_source hpe
  have hepim : (e p).im = 0 := (heim p).trans hρp
  obtain ⟨N, hN, hcN⟩ := hci.contDiffOn (m := 1) le_rfl (by norm_num)
  obtain ⟨N₀, hN₀N, hN₀, hepN₀⟩ := _root_.mem_nhds_iff.mp hN
  let T := (e.target ∩ e.symm ⁻¹' W) ∩ N₀
  have hT : IsOpen T := (e.symm.isOpen_inter_preimage hW).inter hN₀
  have hepT : e p ∈ T := ⟨⟨hep, by change e.symm (e p) ∈ W; simpa only [e.left_inv hpe] using hpW⟩, hepN₀⟩
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hepT)
  let A := e.symm '' ball (e p) δ
  have hballtarget : ball (e p) δ ⊆ e.target := fun z hz => (hδT hz).1.1
  have hA : IsOpen A := e.symm.isOpen_image_of_subset_source isOpen_ball hballtarget
  have hAW : A ⊆ W := by rintro z ⟨y, hy, rfl⟩; exact (hδT hy).1.2
  let η : ℝ → ℂ := fun t => e p + (t : ℂ)
  let γ : ℝ → ℂ := e.symm ∘ η
  have hη (t : ℝ) : HasDerivAt η 1 t := (Complex.ofRealCLM.hasDerivAt (x := t)).const_add (e p)
  have hηball : ∀ t ∈ Ioo (-δ) δ, η t ∈ ball (e p) δ := by
    intro t ht
    simpa only [η, mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using ht
  have hγc : ContDiffOn ℝ 1 γ (Ioo (-δ) δ) := by
    apply hcN.comp (contDiff_const.add Complex.ofRealCLM.contDiff).contDiffOn
    exact fun t ht => hN₀N (hδT (hηball t ht)).2
  have hγe (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : e (γ t) = η t :=
    e.right_inv (hballtarget (hηball t ht))
  have hγW (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : γ t ∈ W := (hδT (hηball t ht)).1.2
  refine ⟨δ, A, γ, hδ, hA, ?_, ?_, hγc, ?_, ?_, ?_⟩
  · exact ⟨e p, mem_ball_self hδ, e.left_inv hpe⟩
  · simpa only [γ, Function.comp_apply, η, ofReal_zero, add_zero] using e.left_inv hpe
  · intro t ht
    have hcd := (hγc.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
    have heg := (hce.contDiffAt (hW.mem_nhds (hγW t ht))).differentiableAt (by norm_num)
    have hcomp := heg.hasFDerivAt.comp_hasDerivAt t hcd.hasDerivAt
    have heq : η =ᶠ[𝓝 t] (e ∘ γ) :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun s hs => (hγe s hs).symm)
    have heqd := hcomp.congr_of_eventuallyEq heq
    have heqval := heqd.unique (hη t)
    intro hzero
    rw [hzero, map_zero] at heqval
    exact zero_ne_one heqval
  · intro s hs t ht hst
    have heq := (hγe s hs).symm.trans ((congrArg e hst).trans (hγe t ht))
    have hh := congrArg Complex.re heq
    simpa [η] using hh
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(hz _ (hγW t ht)).mpr ?_, ⟨η t, hηball t ht, rfl⟩⟩
      rw [← heim, hγe t ht]
      simp [η, hepim]
    · rintro ⟨hzf, y, hy, rfl⟩
      have hyim : y.im = 0 := by
        rw [← e.right_inv (hballtarget hy), heim]
        exact (hz _ ((hδT hy).1.2)).mp hzf
      let t := y.re - (e p).re
      have hyη : η t = y := by
        apply Complex.ext <;> simp [η, t, hepim, hyim]
      have ht : t ∈ Ioo (-δ) δ := by
        have hh := hy
        rw [← hyη] at hh
        simpa only [η, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real,
          Real.norm_eq_abs, abs_lt, mem_Ioo] using hh
      exact ⟨t, ht, by simp only [γ, Function.comp_apply, hyη]⟩

/-- The source's actual biholomorphic sector charts give genuine C1
partial diffeomorphisms; no regular-domain certificate is a premise. -/
lemma sectorChart_diffeomorph {U : Set ℂ} {p : ℂ} {θ : ℝ}
    (h : CircularExhaustion.SectorChart U p θ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      e.IsImage U (CircularExhaustion.sector θ) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target := by
  obtain ⟨A, B, f, g, hp, hf, hf0, _, hside⟩ := h
  let e : OpenPartialHomeomorph ℂ ℂ := {
    toFun := f
    invFun := g
    source := A
    target := B
    map_source' := hf.2.2.1
    map_target' := hf.2.2.2.1
    left_inv' := hf.2.2.2.2.1
    right_inv' := hf.2.2.2.2.2
    continuousOn_toFun := fun z hz => (hf.1.2 z hz).continuousAt.continuousWithinAt
    continuousOn_invFun := fun z hz => (hf.2.1.2 z hz).continuousAt.continuousWithinAt
    open_source := hf.1.1
    open_target := hf.2.1.1 }
  have hfc : DifferentiableOn ℂ f A := fun z hz => (hf.1.2 z hz).differentiableWithinAt
  have hgc : DifferentiableOn ℂ g B := fun z hz => (hf.2.1.2 z hz).differentiableWithinAt
  exact ⟨e, hp, hf0, fun z hz => (hside z hz).symm,
    (hfc.contDiffOn hf.1.1).restrict_scalars ℝ,
    (hgc.contDiffOn hf.2.1.1).restrict_scalars ℝ⟩

/-- Local defining functions on the retained original smooth boundary. -/
lemma defining_function_at_smooth_sector {U : Set ℂ} {p : ℂ}
    (h : CircularExhaustion.SectorChart U p Real.pi) (hp : p ∈ frontier U) :
    ∃ (W : Set ℂ) (ρ : ℂ → ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ 1 ρ W ∧
      (∀ z ∈ W, z ∈ U ↔ ρ z < 0) ∧
      (∀ z ∈ W, z ∈ frontier U ↔ ρ z = 0) ∧
      ∀ z ∈ W, ρ z = 0 → fderiv ℝ ρ z ≠ 0 := by
  obtain ⟨e, he, _, hside, hc, hci⟩ := sectorChart_diffeomorph h
  exact local_defining_function_of_chart e hside hc hci sector_pi_hasC1DefiningFunctions he hp

/-- The literal finite removal has the rounded model side in every disjoint
join chart. This is an equality about actual sets, before any regularity claim. -/
lemma chart_surgery_isImage {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) (ε : ℝ)
    (hside : ∀ p ∈ J, (e p).IsImage U (CircularExhaustion.sector (θ p)))
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target) :
    ∀ p ∈ J, (e p).IsImage
      (U \ ⋃ q ∈ J, (e q).symm '' sectorTip ε (θ q)) (roundedSector ε (θ p)) := by
  let K := ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
  have hKsrc : ∀ p ∈ J, (e p).symm '' sectorTip ε (θ p) ⊆ (e p).source := by
    rintro p hp z ⟨w, hw, rfl⟩
    exact (e p).map_target (htip p hp hw)
  have hlocal : ∀ p ∈ J, (e p).IsImage (U \ K) (roundedSector ε (θ p)) := by
    intro p hpJ z hz
    have hzK : z ∈ K ↔ e p z ∈ sectorTip ε (θ p) := by
      constructor
      · intro hzK
        obtain ⟨q, hqJ, w, hw, heq⟩ := mem_iUnion₂.mp hzK
        have hqp : q = p := by
          by_contra hne
          exact (Set.disjoint_left.mp (hdisj p hpJ q hqJ (Ne.symm hne))) hz
            (hKsrc q hqJ ⟨w, hw, heq⟩)
        subst q
        rw [← heq, (e p).right_inv (htip p hpJ hw)]
        exact hw
      · intro hw
        exact mem_iUnion₂.mpr ⟨p, hpJ, e p z, hw, (e p).left_inv hz⟩
    change (e p z ∈ CircularExhaustion.sector (θ p) ∧ e p z ∉ sectorTip ε (θ p)) ↔
      z ∈ U ∧ z ∉ K
    exact (hside p hpJ hz).and (not_congr hzK.symm)
  exact hlocal

/-- Finite chart surgery gives actual defining functions on the rounded open
set. All chart assumptions are ordinary local diffeomorphism and set-side data;
compact tips and regularity of their boundary are proved above. -/
lemma finite_chart_surgery {U : Set ℂ} {J : Finset ℂ} (hgeom : RoundingGeometry U J)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (CircularExhaustion.sector (θ p)))
    (hc : ∀ p ∈ J, ContDiffOn ℝ 1 (e p) (e p).source ∧
      ContDiffOn ℝ 1 (e p).symm (e p).target)
    (hp : ∀ p ∈ J, p ∈ (e p).source ∧ e p p = 0)
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target) :
    let K := ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
    IsCompact K ∧ IsOpen (U \ K) ∧ HasC1DefiningFunctions (U \ K) ∧
      Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain (realPlane '' (U \ K)) ∧
      HasRegularBoundaryParametrizations (U \ K) := by
  let K := ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
  have hK : IsCompact K := J.isCompact_biUnion fun p hp =>
    (isCompact_sectorTip ε (θ p)).image_of_continuousOn ((e p).symm.continuousOn.mono (htip p hp))
  have hKsrc : ∀ p ∈ J, (e p).symm '' sectorTip ε (θ p) ⊆ (e p).source := by
    rintro p hp z ⟨w, hw, rfl⟩
    exact (e p).map_target (htip p hp hw)
  have hJK : (↑J : Set ℂ) ⊆ K := by
    intro p hpJ
    refine mem_iUnion₂.mpr ⟨p, hpJ, ?_⟩
    refine ⟨0, zero_mem_sectorTip ε (θ p), ?_⟩
    rw [← (hp p hpJ).2]
    exact (e p).left_inv (hp p hpJ).1
  have hlocal := chart_surgery_isImage e θ ε hside hdisj htip
  have hdef : HasC1DefiningFunctions (U \ K) := by
    intro p hpf
    by_cases hpK : p ∈ K
    · obtain ⟨q, hqJ, hpq⟩ := mem_iUnion₂.mp hpK
      exact local_defining_function_of_chart (e q) (hlocal q hqJ) (hc q hqJ).1 (hc q hqJ).2
        (roundedSector_hasC1DefiningFunctions hε (hθ q hqJ).1 (hθ q hqJ).2)
        (hKsrc q hqJ hpq) hpf
    · have hpU : p ∈ frontier U := by
        by_contra h
        exact hpK ((closed_removal_locality (U := U) hK.isClosed).2.2 ⟨hpf, h⟩)
      have hpJ : p ∉ J := fun h => hpK (hJK h)
      obtain ⟨W, ρ, hW, hpW, hρ, hn, hz, hd⟩ :=
        defining_function_at_smooth_sector (hgeom.2.2.2.2.1 p hpU hpJ) hpU
      have hfeq := frontier_inter_open_inter (s := U) hK.isClosed.isOpen_compl
      change frontier (U \ K) ∩ Kᶜ = frontier U ∩ Kᶜ at hfeq
      refine ⟨W ∩ Kᶜ, ρ, hW.inter hK.isClosed.isOpen_compl, ⟨hpW, hpK⟩,
        hρ.mono inter_subset_left, ?_, ?_, fun z hz' => hd z hz'.1⟩
      · intro z hz'
        exact (and_iff_left hz'.2).trans (hn z hz'.1)
      · intro z hz'
        have hh : z ∈ frontier (U \ K) ↔ z ∈ frontier U := by
          exact ⟨fun h => ((Set.ext_iff.mp hfeq z).mp ⟨h, hz'.2⟩).1,
            fun h => ((Set.ext_iff.mp hfeq z).mpr ⟨h, hz'.2⟩).1⟩
        exact hh.trans (hz z hz'.1)
  have hopen := hgeom.1.sdiff hK.isClosed
  exact ⟨hK, hopen, hdef, classical_domain_bridge _ (hgeom.2.1.subset sdiff_subset) hopen hdef,
    hasRegularBoundaryParametrizations_of_defining_functions hdef⟩

/-- One positive lower bound works for any finite family of positive scales. -/
lemma finite_positive_lower_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ r : ℝ, 0 < r ∧ ∀ a ∈ s, r ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨r, hr, hrs⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨min (f a) r, lt_min (hf a (Finset.mem_insert_self _ _)) hr, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hrs b hb)

/-- Finite distinct join points have pairwise disjoint fixed-radius balls. -/
lemma finite_disjoint_join_balls (J : Finset ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (ball p r) (ball q r) := by
  classical
  let f : ℂ × ℂ → ℝ := fun x => if x.1 = x.2 then 1 else dist x.1 x.2
  have hf : ∀ x ∈ J.product J, 0 < f x := by
    intro x _
    dsimp [f]
    split_ifs with h
    · norm_num
    · exact dist_pos.mpr h
  obtain ⟨d, hd, hdist⟩ := finite_positive_lower_bound (J.product J) f hf
  refine ⟨d / 3, by positivity, ?_⟩
  intro p hp q hq hpq
  apply ball_disjoint_ball
  have hh := hdist (p, q) (Finset.mem_product.mpr ⟨hp, hq⟩)
  simp only [f, hpq, if_false] at hh
  linarith

/-- Choose all original join charts with disjoint physical sources and one
coordinate scale and inverse Lipschitz bound. Constants depend only on U,J. -/
lemma exists_uniform_corner_charts {U : Set ℂ} {J : Finset ℂ}
    (hgeom : RoundingGeometry U J) :
    ∃ (θ : ℂ → ℝ) (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (R : ℝ) (L : ℝ≥0),
      0 < R ∧ 0 < L ∧
      (∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi) ∧
      (∀ p ∈ J, (e p).IsImage U (CircularExhaustion.sector (θ p))) ∧
      (∀ p ∈ J, ContDiffOn ℝ 1 (e p) (e p).source ∧
        ContDiffOn ℝ 1 (e p).symm (e p).target) ∧
      (∀ p ∈ J, p ∈ (e p).source ∧ e p p = 0) ∧
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source) ∧
      (∀ p ∈ J, closedBall (0 : ℂ) R ⊆ (e p).target ∧
        LipschitzOnWith L (e p).symm (closedBall (0 : ℂ) R)) := by
  classical
  have hchoice : ∀ p : ℂ, ∃ (θ : ℝ) (e : OpenPartialHomeomorph ℂ ℂ), p ∈ J →
      (0 < θ ∧ θ < 2 * Real.pi) ∧ p ∈ e.source ∧ e p = 0 ∧
      e.IsImage U (CircularExhaustion.sector θ) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target := by
    intro p
    by_cases hp : p ∈ J
    · obtain ⟨θ, hθ, hθ', hs⟩ := hgeom.2.2.2.2.2 p hp
      obtain ⟨e, he, he0, hside, hc, hci⟩ := sectorChart_diffeomorph hs
      exact ⟨θ, e, fun _ => ⟨⟨hθ, hθ'⟩, he, he0, hside, hc, hci⟩⟩
    · exact ⟨Real.pi, OpenPartialHomeomorph.refl ℂ, fun h => (hp h).elim⟩
  choose θ e hdata using hchoice
  obtain ⟨r, hr, hdisj⟩ := finite_disjoint_join_balls J
  let E : ℂ → OpenPartialHomeomorph ℂ ℂ := fun p => (e p).restrOpen (ball p r) isOpen_ball
  have hE : ∀ p ∈ J, (0 < θ p ∧ θ p < 2 * Real.pi) ∧ p ∈ (E p).source ∧ E p p = 0 ∧
      (E p).IsImage U (CircularExhaustion.sector (θ p)) ∧
      ContDiffOn ℝ 1 (E p) (E p).source ∧ ContDiffOn ℝ 1 (E p).symm (E p).target := by
    intro p hp
    obtain ⟨hθ, hps, he0, hs, hc, hci⟩ := hdata p hp
    exact ⟨hθ, ⟨hps, mem_ball_self hr⟩, he0, fun z hz => hs hz.1,
      hc.mono inter_subset_left, hci.mono inter_subset_left⟩
  have hbound : ∀ p : ℂ, ∃ (R : ℝ) (L : ℝ≥0), 0 < R ∧ 0 < L ∧ (p ∈ J →
      closedBall (0 : ℂ) R ⊆ (E p).target ∧
      LipschitzOnWith L (E p).symm (closedBall (0 : ℂ) R)) := by
    intro p
    by_cases hp : p ∈ J
    · have ht : (0 : ℂ) ∈ (E p).target := by
        rw [← (hE p hp).2.2.1]
        exact (E p).map_source (hE p hp).2.1
      have hg := ((hE p hp).2.2.2.2.2.contDiffAt ((E p).open_target.mem_nhds ht))
      let L : ℝ≥0 := ‖fderiv ℝ (E p).symm 0‖₊ + 1
      obtain ⟨W, hW, hLip⟩ := hg.exists_lipschitzOnWith_of_nnnorm_lt L (by simp [L])
      obtain ⟨s, hs, hsW⟩ := Metric.mem_nhds_iff.mp
        (Filter.inter_mem hW ((E p).open_target.mem_nhds ht))
      have hsub : closedBall (0 : ℂ) (s / 2) ⊆ W ∩ (E p).target :=
        (closedBall_subset_ball (by linarith)).trans hsW
      exact ⟨s / 2, L, by positivity, by simp [L],
        fun _ => ⟨fun z hz => (hsub hz).2, hLip.mono (fun z hz => (hsub hz).1)⟩⟩
    · exact ⟨1, 1, by norm_num, by norm_num, fun h => (hp h).elim⟩
  choose Rp Lp hRp hLp hLip using hbound
  obtain ⟨R, hR, hRR⟩ := finite_positive_lower_bound J Rp (fun p _ => hRp p)
  let L : ℝ≥0 := (∑ p ∈ J, Lp p) + 1
  have hLL : ∀ p ∈ J, Lp p ≤ L := by
    intro p hp
    exact (Finset.single_le_sum (fun q _ => show (0 : ℝ≥0) ≤ Lp q from bot_le) hp).trans (le_add_of_nonneg_right (by norm_num))
  refine ⟨θ, E, R, L, hR, by dsimp [L]; positivity, (fun p hp => (hE p hp).1),
    (fun p hp => (hE p hp).2.2.2.1), (fun p hp => (hE p hp).2.2.2.2),
    (fun p hp => ⟨(hE p hp).2.1, (hE p hp).2.2.1⟩), ?_, ?_⟩
  · intro p hp q hq hpq
    exact (hdisj p hp q hq hpq).mono inter_subset_right inter_subset_right
  · intro p hp
    exact ⟨(closedBall_subset_closedBall (hRR p hp)).trans (hLip p hp).1,
      ((hLip p hp).2.mono (closedBall_subset_closedBall (hRR p hp))).weaken (hLL p hp)⟩

/-- Actual old and new frontier differences are contained in the literal
short original rays and added arc images of the chosen charts. -/
lemma chart_surgery_frontier_differences {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (CircularExhaustion.sector (θ p)))
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target) :
    let V := U \ ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
    (frontier U \ frontier V ⊆ ⋃ p ∈ J, (e p).symm '' shortRays ε (θ p)) ∧
    (frontier V \ frontier U ⊆ ⋃ p ∈ J,
      (e p).symm '' (roundingArc ε (θ p) '' Icc (0 : ℝ) 1)) := by
  let K := ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
  have hK : IsClosed K := (J.isCompact_biUnion fun p hp =>
    (isCompact_sectorTip ε (θ p)).image_of_continuousOn ((e p).symm.continuousOn.mono (htip p hp))).isClosed
  have hlocal := chart_surgery_isImage e θ ε hside hdisj htip
  constructor
  · intro z hz
    have hzK := (closed_removal_locality (U := U) hK).2.1 hz
    obtain ⟨p, hp, w, hw, hzw⟩ := mem_iUnion₂.mp hzK
    have hzs : z ∈ (e p).source := hzw ▸ (e p).map_target (htip p hp hw)
    have hs : e p z ∈ frontier (CircularExhaustion.sector (θ p)) :=
      ((hside p hp).frontier hzs).mpr hz.1
    have hn : e p z ∉ frontier (roundedSector ε (θ p)) :=
      fun h => hz.2 (((hlocal p hp).frontier hzs).mp h)
    exact mem_iUnion₂.mpr ⟨p, hp, e p z,
      removed_sector_frontier_subset_shortRays hε (hθ p hp).1 ⟨hs, hn⟩,
      (e p).left_inv hzs⟩
  · intro z hz
    have hzK := (closed_removal_locality (U := U) hK).2.2 hz
    obtain ⟨p, hp, w, hw, hzw⟩ := mem_iUnion₂.mp hzK
    have hzs : z ∈ (e p).source := hzw ▸ (e p).map_target (htip p hp hw)
    have hs : e p z ∈ frontier (roundedSector ε (θ p)) :=
      ((hlocal p hp).frontier hzs).mpr hz.1
    have hn : e p z ∉ frontier (CircularExhaustion.sector (θ p)) :=
      fun h => hz.2 (((hside p hp).frontier hzs).mp h)
    exact mem_iUnion₂.mpr ⟨p, hp, e p z,
      added_sector_frontier_subset_roundingArc hε (hθ p hp).1 (hθ p hp).2 ⟨hs, hn⟩,
      (e p).left_inv hzs⟩

lemma shortRays_subset_closedBall {ε θ : ℝ} (hε : 0 ≤ ε) :
    shortRays ε θ ⊆ closedBall (0 : ℂ) ε := by
  intro z hz
  rcases hz with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · simpa only [mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr.1] using hr.2
  · simpa only [mem_closedBall, dist_zero_right, norm_polar hr.1] using hr.2

lemma hausdorffMeasure_chart_shortRays_le {g : ℂ → ℂ} {L : ℝ≥0} {R ε θ : ℝ}
    (hg : LipschitzOnWith L g (closedBall (0 : ℂ) R)) (hε : 0 ≤ ε) (hεR : ε ≤ R) :
    Measure.hausdorffMeasure 1 (g '' shortRays ε θ) ≤ ENNReal.ofReal (2 * (L : ℝ) * ε) := by
  have ha : shortRays ε θ ⊆ closedBall (0 : ℂ) R :=
    (shortRays_subset_closedBall hε).trans (closedBall_subset_closedBall hεR)
  have hh := (hg.mono ha).hausdorffMeasure_image_le (d := 1) (by norm_num)
  simp only [ENNReal.rpow_one] at hh
  calc
    _ ≤ (L : ℝ≥0∞) * Measure.hausdorffMeasure 1 (shortRays ε θ) := hh
    _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (2 * ε) :=
      mul_le_mul_right (hausdorffMeasure_shortRays_le hε) _
    _ = ENNReal.ofReal (2 * (L : ℝ) * ε) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg]
      congr 1
      ring

/-- A finite sum of uniformly bounded actual measures. No measurability of
boundary difference sets needs to be assumed. -/
lemma measure_finite_union_uniform_bound (μ : Measure ℂ) (J : Finset ℂ)
    (s : ℂ → Set ℂ) (b : ℝ) (h : ∀ p ∈ J, μ (s p) ≤ ENNReal.ofReal b) :
    μ (⋃ p ∈ J, s p) ≤ ENNReal.ofReal ((J.card : ℝ) * b) := by
  calc
    _ ≤ ∑ p ∈ J, μ (s p) := measure_biUnion_finset_le J s
    _ ≤ ∑ p ∈ J, ENNReal.ofReal b := Finset.sum_le_sum h
    _ = ENNReal.ofReal ((J.card : ℝ) * b) := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Round all finitely many actual joins, using fixed disjoint conformal
charts. The same constants control support, both actual changed boundary
lengths, and removed area at every sufficiently small positive scale. -/
theorem circular_corner_rounding :
    Specs.D12Complex.Ch14.CircularCornerRounding.circular_corner_rounding_type := by
  classical
  intro U J hgeom
  obtain ⟨θ, e, R, L, hR, hL, hθ, hside, hc, hp, hdisj, hLip⟩ :=
    exists_uniform_corner_charts hgeom
  have hg0 : ∀ p ∈ J, (e p).symm 0 = p := by
    intro p hpJ
    rw [← (hp p hpJ).2]
    exact (e p).left_inv (hp p hpJ).1
  let n : ℝ := J.card
  let A : ℝ := n * Real.pi * (L : ℝ) ^ 2
  let B : ℝ := n * (2 * (L : ℝ))
  let D : ℝ := n * (13 * Real.pi * (L : ℝ))
  let C : ℝ := (L : ℝ) + 1 + A + B + D
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hLC : (L : ℝ) < C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith [L.coe_nonneg]
  have hBC : B ≤ C := by dsimp [C]; linarith [L.coe_nonneg]
  have hDC : D ≤ C := by dsimp [C]; linarith [L.coe_nonneg]
  obtain ⟨r, hr, hrdisj⟩ := finite_disjoint_join_balls J
  refine ⟨C, min R (r / C), hC, lt_min hR (div_pos hr hC), ?_⟩
  intro ε hε hεsmall
  have hεR : ε ≤ R := (hεsmall.trans_le (min_le_left _ _)).le
  have hCr : C * ε < r := by
    have hh := (lt_div_iff₀ hC).mp (hεsmall.trans_le (min_le_right _ _))
    simpa only [mul_comm] using hh
  have htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target := by
    intro p hpJ
    exact (sectorTip_subset_closedBall hε).trans
      ((closedBall_subset_closedBall hεR).trans (hLip p hpJ).1)
  let K := ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
  let V := U \ K
  obtain ⟨hK, hV, hdef, hclass, hparam⟩ :=
    finite_chart_surgery hgeom e θ hε hθ hside hc hp hdisj htip
  have hbounds : ∀ p ∈ J,
      (e p).symm '' sectorTip ε (θ p) ⊆ closedBall p ((L : ℝ) * ε) ∧
      volume ((e p).symm '' sectorTip ε (θ p)) ≤
        ENNReal.ofReal (Real.pi * ((L : ℝ) * ε) ^ 2) ∧
      Measure.hausdorffMeasure 1
        ((e p).symm '' (roundingArc ε (θ p) '' Icc (0 : ℝ) 1)) ≤
          ENNReal.ofReal (13 * Real.pi * (L : ℝ) * ε) := by
    intro p hpJ
    obtain ⟨_, hs, ha, hl⟩ := chart_tip_estimates (hLip p hpJ).2 hε hεR (hθ p hpJ).1
    rw [hg0 p hpJ] at hs
    refine ⟨hs, ha, hl.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hθle : Real.pi / 2 + 6 * θ p ≤ 13 * Real.pi := by
      linarith [(hθ p hpJ).2, Real.pi_pos]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hθle L.coe_nonneg) hε.le
    nlinarith
  have hKsupport : K ⊆ joinNeighborhoods J (C * ε) := by
    intro z hz
    obtain ⟨p, hpJ, hzp⟩ := mem_iUnion₂.mp hz
    apply mem_iUnion₂.mpr
    exact ⟨p, hpJ, (closedBall_subset_ball (mul_lt_mul_of_pos_right hLC hε)) ((hbounds p hpJ).1 hzp)⟩
  have hremoved : U \ V ⊆ K := by
    intro z hz
    by_contra hzK
    exact hz.2 ⟨hz.1, hzK⟩
  have hfront := chart_surgery_frontier_differences e θ hε hθ hside hdisj htip
  have hlengthOld : Measure.hausdorffMeasure 1 (frontier U \ frontier V) ≤ ENNReal.ofReal (B * ε) := by
    apply (measure_mono hfront.1).trans
    have hh := measure_finite_union_uniform_bound (Measure.hausdorffMeasure 1) J
      (fun p => (e p).symm '' shortRays ε (θ p)) (2 * (L : ℝ) * ε)
      (fun p hpJ => hausdorffMeasure_chart_shortRays_le (hLip p hpJ).2 hε.le hεR)
    convert hh using 1 <;> dsimp [B, n] <;> congr 1 <;> ring
  have hlengthNew : Measure.hausdorffMeasure 1 (frontier V \ frontier U) ≤ ENNReal.ofReal (D * ε) := by
    apply (measure_mono hfront.2).trans
    have hh := measure_finite_union_uniform_bound (Measure.hausdorffMeasure 1) J
      (fun p => (e p).symm '' (roundingArc ε (θ p) '' Icc (0 : ℝ) 1))
      (13 * Real.pi * (L : ℝ) * ε) (fun p hpJ => (hbounds p hpJ).2.2)
    convert hh using 1 <;> dsimp [D, n] <;> congr 1 <;> ring
  have harea : volume (U \ V) ≤ ENNReal.ofReal (A * ε ^ 2) := by
    apply (measure_mono hremoved).trans
    have hh := measure_finite_union_uniform_bound volume J
      (fun p => (e p).symm '' sectorTip ε (θ p)) (Real.pi * ((L : ℝ) * ε) ^ 2)
      (fun p hpJ => (hbounds p hpJ).2.1)
    convert hh using 1 <;> dsimp [A, n] <;> congr 1 <;> ring
  refine ⟨V, hV, sdiff_subset, hclass, hparam, ?_, hremoved.trans hKsupport, ?_,
    (closed_removal_locality (U := U) hK.isClosed).2.1.trans hKsupport,
    (closed_removal_locality (U := U) hK.isClosed).2.2.trans hKsupport,
    hlengthOld.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hBC hε.le)),
    hlengthNew.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDC hε.le)),
    harea.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAC (sq_nonneg ε)))⟩
  · intro p hpJ q hqJ hpq
    exact (hrdisj p hpJ q hqJ hpq).mono
      (ball_subset_ball hCr.le) (ball_subset_ball hCr.le)
  · intro z hz
    exact (closed_removal_locality (U := U) hK.isClosed).1 z (fun h => hz (hKsupport h))

/-- Complete model frontier, set-side formula, regular parametrizations and
bounds on both actual changed frontier portions. -/
theorem model_sector_geometry :
    Specs.D12Complex.Ch14.CircularCornerRounding.model_sector_geometry_type := by
  intro ε θ hε hθ hθ'
  exact ⟨isOpen_roundedSector ε θ, frontier_roundedSector_eq_positive_range hε hθ hθ',
    roundedSector_hasRegularBoundaryParametrizations hε hθ hθ',
    zero_not_mem_closure_roundedSector hε hθ,
    mem_roundedSector_iff_exists hε hθ hθ',
    removed_sector_frontier_subset_shortRays hε hθ,
    added_sector_frontier_subset_roundingArc hε hθ hθ',
    hausdorffMeasure_removed_sector_frontier_le hε hθ,
    hausdorffMeasure_added_sector_frontier_le hε hθ hθ'⟩

/-- The regular zero-level charts are proved without assuming a defining
function certificate or any boundary side for the rounded domain. -/
theorem model_normal_charts :
    Specs.D12Complex.Ch14.CircularCornerRounding.model_normal_charts_type := by
  intro ε θ hε hθ hθ' a
  exact ⟨exists_normal_coordinates hε hθ a, exists_model_zero_chart hε hθ hθ' a⟩

end D12Complex.CircularCornerRounding

