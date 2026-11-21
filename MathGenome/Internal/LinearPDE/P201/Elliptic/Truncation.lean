import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Truncation
import MathGenome.Internal.LinearPDE.P201.Common.ExactTrace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FourierSobolev.P102.U4.ChainProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P201.Truncation

abbrev positivePart : P201Specs.Truncation.PositivePartType :=
  @P201Specs.Truncation.positivePart
abbrev testToH : P201Specs.Truncation.TestToHType := @P201Specs.Truncation.testToH

theorem underlying_toW {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    P102.U4.sobolevUnderlying (hToW ℝ Ω 1 u) = hUnderlying Ω 1 u := rfl

/-- The zeroth coordinate is exactly max(u,0), with no change of measure. -/
theorem positivePart_underlying {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    (hUnderlying Ω 1 (positivePart Ω u) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => max (hUnderlying Ω 1 u x) 0 := by
  have h := (P102.U4.lower_truncation_rule Ω 2 (hToW ℝ Ω 1 u) 0
    (Or.inl le_rfl)).choose_spec.1
  change (P102.U4.sobolevUnderlying ((hToW ℝ Ω 1)
    ((hToW ℝ Ω 1).symm _)) : Space n → ℝ) =ᵐ[domainMeasure Ω] _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simpa only [underlying_toW, max_comm] using h

/-- Each first-derivative coordinate retains the strict-cutoff formula. -/
theorem positivePart_derivative {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) (j : Fin n) :
    (hFirstDerivative (positivePart Ω u) j : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => if 0 < hUnderlying Ω 1 u x then hFirstDerivative u j x else 0 := by
  have h := (P102.U4.lower_truncation_rule Ω 2 (hToW ℝ Ω 1 u) 0
    (Or.inl le_rfl)).choose_spec.2 j
  simpa only [positivePart, P201Specs.Truncation.positivePart,
    P201.hFirstDerivative, P201Specs.hFirstDerivative,
    ContinuousLinearEquiv.apply_symm_apply, P102.U4.Truncations.sobolevFirstDerivative,
    P102.U4.Truncations.firstSobolevIndex, mem_Ioi, underlying_toW] using h

/-- Equality of gradient classes with their bundled coordinate representatives. -/
theorem gradient_ae {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    (hGradient u : Space n → Space n) =ᵐ[domainMeasure Ω]
      fun x => WithLp.toLp 2 (fun j => hFirstDerivative u j x) :=
  (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (hFirstDerivative u j))).coeFn_toLp

theorem positivePart_formula : P201Specs.Truncation.PositivePartStatement := by
  intro n Ω u
  refine ⟨positivePart_underlying Ω u, ?_⟩
  have hcoord : ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin n,
      hFirstDerivative (positivePart Ω u) j x =
        if 0 < hUnderlying Ω 1 u x then hFirstDerivative u j x else 0 :=
    ae_all_iff.mpr (positivePart_derivative Ω u)
  filter_upwards [gradient_ae Ω (positivePart Ω u), gradient_ae Ω u, hcoord]
    with x hx hu hc
  rw [hx, hu]
  split_ifs with h
  · exact congrArg (WithLp.toLp 2) (funext fun j => by simpa only [ite_eq_left h] using hc j)
  · apply PiLp.ext
    intro j
    change hFirstDerivative (positivePart Ω u) j x = 0
    simpa only [ite_eq_right h] using hc j

theorem zero_level : P201Specs.Truncation.ZeroLevelStatement := by
  intro n Ω u
  have hcoord : ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin n,
      hUnderlying Ω 1 u x = 0 → hFirstDerivative u j x = 0 :=
    ae_all_iff.mpr (fun j => P102.U4.truncation_level_set Ω 2 (hToW ℝ Ω 1 u) 0 j)
  filter_upwards [gradient_ae Ω u, hcoord] with x hx hc hu
  rw [hx]
  apply PiLp.ext
  intro j
  exact hc j hu

/-- The test inclusion represents the original smooth function. -/
theorem testToH_underlying {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) :
    (hUnderlying Ω 1 (testToH Ω φ) : Space n → ℝ) =ᵐ[domainMeasure Ω] φ := by
  have h := (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose_spec
  change (P102.U4.sobolevUnderlying
    ((hToW ℝ Ω 1) ((hToW ℝ Ω 1).symm _)) : Space n → ℝ) =ᵐ[_] _
  rw [ContinuousLinearEquiv.apply_symm_apply, h]
  exact (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).coeFn_toLp

end P201.Truncation

namespace P201.Truncation
section Cutoff
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Strict-positive cutoff of a second L² class by a first L² class. -/
def cutoffLp (f g : MeasureTheory.Lp ℝ 2 μ) : MeasureTheory.Lp ℝ 2 μ :=
  ((Lp.memLp g).indicator (measurableSet_lt (f := fun _ : X => (0 : ℝ)) measurable_const
    (Lp.stronglyMeasurable f).measurable).nullMeasurableSet).toLp _

theorem cutoffLp_ae (f g : MeasureTheory.Lp ℝ 2 μ) :
    (cutoffLp f g : X → ℝ) =ᵐ[μ] fun x => if 0 < f x then g x else 0 := by
  exact ((Lp.memLp g).indicator (measurableSet_lt (f := fun _ : X => (0 : ℝ)) measurable_const
    (Lp.stronglyMeasurable f).measurable).nullMeasurableSet).coeFn_toLp

/-- At fixed cutoff, changing the field is an L² contraction. -/
theorem cutoffLp_sub_bound (f g h : MeasureTheory.Lp ℝ 2 μ) :
    ‖cutoffLp f g - cutoffLp f h‖ ≤ ‖g - h‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutoffLp_ae f g, cutoffLp_ae f h,
    Lp.coeFn_sub (cutoffLp f g) (cutoffLp f h), Lp.coeFn_sub g h]
    with x hg hh hs hgh
  simp only [hs, hgh, Pi.sub_apply, hg, hh]
  split_ifs <;> simp

/-- A moving cutoff converges on a fixed field that vanishes at the cutoff
level. This is the dominated-convergence step behind H¹ continuity. -/
theorem cutoffLp_tendsto_fixed (f : ℕ → MeasureTheory.Lp ℝ 2 μ)
    (a g : MeasureTheory.Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (a x)))
    (hz : ∀ᵐ x ∂μ, a x = 0 → g x = 0) :
    Tendsto (fun k => cutoffLp (f k) g) atTop (𝓝 (cutoffLp a g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  let r : ℕ → X → ℝ := fun k x =>
    (if 0 < f k x then g x else 0) - (if 0 < a x then g x else 0)
  have hr (k) : AEStronglyMeasurable (r k) μ := by
    exact ((Lp.aestronglyMeasurable g).indicator
      (measurableSet_lt (f := fun _ : X => (0 : ℝ)) measurable_const (Lp.stronglyMeasurable (f k)).measurable)).sub
      ((Lp.aestronglyMeasurable g).indicator
        (measurableSet_lt (f := fun _ : X => (0 : ℝ)) measurable_const (Lp.stronglyMeasurable a).measurable))
  have hb (k) : ∀ᵐ x ∂μ, ‖r k x‖ ≤ ‖g x‖ := by
    filter_upwards [] with x
    dsimp [r]
    split_ifs <;> simp
  have hl : ∀ᵐ x ∂μ, Tendsto (fun k => r k x) atTop (𝓝 0) := by
    filter_upwards [hf, hz] with x hx hz
    rcases lt_trichotomy (a x) 0 with ha | ha | ha
    · apply tendsto_const_nhds.congr'
      filter_upwards [hx.eventually (gt_mem_nhds ha)] with k hk
      simp [r, not_lt_of_gt ha, not_lt_of_gt hk]
    · have hg := hz ha
      simp only [r, hg, ite_self, sub_self]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [hx.eventually (lt_mem_nhds ha)] with k hk
      simp [r, ha, hk]
  have ht := P102.U4.eLpNorm_tendsto_zero_of_dominated
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hr (Lp.memLp g) hb hl
  apply ht.congr
  intro k
  apply eLpNorm_congr_ae
  filter_upwards [cutoffLp_ae (f k) g, cutoffLp_ae a g] with x hk ha
  simp only [Pi.sub_apply, hk, ha, r]

/-- Strong L² convergence of the selector and field gives strong convergence
of their cutoff, provided the limiting field vanishes on the selector's zero set. -/
theorem cutoffLp_tendsto (f g : ℕ → MeasureTheory.Lp ℝ 2 μ)
    (a b : MeasureTheory.Lp ℝ 2 μ) (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b))
    (hz : ∀ᵐ x ∂μ, a x = 0 → b x = 0) :
    Tendsto (fun k => cutoffLp (f k) (g k)) atTop (𝓝 (cutoffLp a b)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hf.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hfix := cutoffLp_tendsto_fixed (fun k => f (ns (ms k))) a b hae hz
  have hsmall : Tendsto
      (fun k => cutoffLp (f (ns (ms k))) (g (ns (ms k))) -
        cutoffLp (f (ns (ms k))) b) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun k => cutoffLp_sub_bound _ _ _)
    simpa only [sub_self, norm_zero, Function.comp_def] using
      ((hg.comp (hns.comp hms.tendsto_atTop)).sub (tendsto_const_nhds (x := b))).norm
  convert hsmall.add hfix using 1 <;> simp
end Cutoff
end P201.Truncation

namespace P201.Truncation

/-- Positive part on L², with the same representative convention as Sobolev
positive part. This operator is a contraction. -/
def positiveLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : MeasureTheory.Lp ℝ 2 μ) : MeasureTheory.Lp ℝ 2 μ :=
  (LipschitzWith.id.max_const (0 : ℝ)).compLp (by simp) u

theorem positiveLp_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : MeasureTheory.Lp ℝ 2 μ) :
    (positiveLp u : X → ℝ) =ᵐ[μ] fun x => max (u x) 0 :=
  (LipschitzWith.id.max_const (0 : ℝ)).coeFn_compLp (by simp) u

theorem underlying_positiveLp {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    hUnderlying Ω 1 (positivePart Ω u) = positiveLp (hUnderlying Ω 1 u) := by
  apply Lp.ext
  exact (positivePart_underlying Ω u).trans (positiveLp_ae _).symm

theorem derivative_cutoffLp {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) (j : Fin n) :
    hFirstDerivative (positivePart Ω u) j =
      cutoffLp (hUnderlying Ω 1 u) (hFirstDerivative u j) := by
  apply Lp.ext
  exact (positivePart_derivative Ω u j).trans (cutoffLp_ae _ _).symm

/-- All weak derivative coordinates vary continuously in the full H¹ norm. -/
theorem tendsto_derivative {n : ℕ} (Ω : Domain n) {u : ℕ → H ℝ Ω 1}
    {v : H ℝ Ω 1} (hu : Tendsto u atTop (𝓝 v)) (α : P102.U4.SobolevIndex n 1) :
    Tendsto (fun k => P102.U4.sobolevDerivative (hToW ℝ Ω 1 (u k)) α)
      atTop (𝓝 (P102.U4.sobolevDerivative (hToW ℝ Ω 1 v) α)) :=
  (((PiLp.proj 2 (fun _ : P102.U4.SobolevIndex n 1 => Lp ℝ Ω 2) α).comp
    (P201Specs.hilbertSubmodule ℝ Ω 1).subtypeL).continuous.tendsto v).comp hu

theorem positivePart_continuous : P201Specs.Truncation.ContinuityStatement := by
  intro n Ω
  apply continuous_iff_seqContinuous.mpr
  intro u v hu
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  apply (PiLp.homeomorph 2 (fun _ : P102.U4.SobolevIndex n 1 => Lp ℝ Ω 2)).isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro α
  change Tendsto (fun k => P102.U4.sobolevDerivative (hToW ℝ Ω 1 (positivePart Ω (u k))) α)
    atTop (𝓝 (P102.U4.sobolevDerivative (hToW ℝ Ω 1 (positivePart Ω v)) α))
  have hu0 : Tendsto (fun k => hUnderlying Ω 1 (u k)) atTop (𝓝 (hUnderlying Ω 1 v)) :=
    ((hUnderlying Ω 1).continuous.tendsto v).comp hu
  by_cases hz : α.val = 0
  · have ha : α = P102.U4.zeroSobolevIndex n 1 := Subtype.ext hz
    subst α
    change Tendsto (fun k => hUnderlying Ω 1 (positivePart Ω (u k)))
      atTop (𝓝 (hUnderlying Ω 1 (positivePart Ω v)))
    simp only [underlying_positiveLp]
    exact ((LipschitzWith.id.max_const (0 : ℝ)).continuous_compLp (by simp)).tendsto _ |>.comp hu0
  · have hc : α.val.card = 1 := by
      have := α.property
      have hn := Multiset.card_eq_zero.not.mpr hz
      omega
    obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hc
    have ha : α = ⟨{j}, by simp⟩ := Subtype.ext hj
    subst α
    change Tendsto (fun k => hFirstDerivative (positivePart Ω (u k)) j)
      atTop (𝓝 (hFirstDerivative (positivePart Ω v) j))
    simp only [derivative_cutoffLp]
    apply cutoffLp_tendsto _ _ _ _ hu0 (tendsto_derivative Ω hu ⟨{j}, by simp⟩)
    exact P102.U4.truncation_level_set Ω 2 (hToW ℝ Ω 1 v) 0 j

end P201.Truncation

namespace P201.Truncation
open scoped ContDiff

/-- A flat, nonnegative smooth replacement of the positive-part function. -/
def smoothRamp (t : ℝ) : ℝ := t * Real.smoothTransition t

theorem smoothRamp_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothRamp :=
  contDiff_id.mul Real.smoothTransition.contDiff

theorem smoothRamp_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothRamp t = 0 := by
  simp [smoothRamp, Real.smoothTransition.zero_of_nonpos ht]

theorem smoothRamp_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothRamp t = t := by
  simp [smoothRamp, Real.smoothTransition.one_of_one_le ht]

theorem smoothRamp_deriv_zero : deriv smoothRamp 0 = 0 := by
  change deriv (fun t : ℝ => t * Real.smoothTransition t) 0 = 0
  have h := (hasDerivAt_id (0 : ℝ)).mul
    ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num) 0).hasDerivAt
  simpa only [id_eq, Pi.mul_def, smoothRamp, Real.smoothTransition.zero, mul_zero, zero_mul, add_zero] using h.deriv

theorem smoothRamp_deriv_neg {t : ℝ} (ht : t < 0) : deriv smoothRamp t = 0 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds ht] with s hs
  exact smoothRamp_of_nonpos hs.le

theorem smoothRamp_deriv_pos {t : ℝ} (ht : 1 < t) : deriv smoothRamp t = 1 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  exact smoothRamp_of_one_le hs.le

/-- The derivative bound is uniform after dilation, since the transition
occurs on a fixed compact scalar interval. -/
theorem smoothRamp_deriv_bounded : ∃ C : ℝ≥0, ∀ t, ‖deriv smoothRamp t‖ ≤ C := by
  have hc := smoothRamp_contDiff.continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image hc.norm.continuousOn
  refine ⟨⟨max B 1, le_trans zero_le_one (le_max_right _ _)⟩, fun t => ?_⟩
  change ‖deriv smoothRamp t‖ ≤ max B 1
  by_cases ht : t < 0
  · rw [smoothRamp_deriv_neg ht, norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  by_cases ht' : 1 < t
  · rw [smoothRamp_deriv_pos ht', norm_one]
    exact le_max_right _ _
  exact (hB ⟨t, ⟨le_of_not_gt ht, le_of_not_gt ht'⟩, rfl⟩).trans (le_max_left _ _)

def rampBound : ℝ≥0 := smoothRamp_deriv_bounded.choose

theorem rampBound_spec (t : ℝ) : ‖deriv smoothRamp t‖ ≤ rampBound :=
  smoothRamp_deriv_bounded.choose_spec t

/-- Smooth positive parts that fix zero and preserve supports. -/
def scalarPositive (k : ℕ) (t : ℝ) : ℝ :=
  smoothRamp ((k + 1 : ℝ) * t) / (k + 1 : ℝ)

def scalarSlope (k : ℕ) (t : ℝ) : ℝ := deriv smoothRamp ((k + 1 : ℝ) * t)

theorem scalarPositive_contDiff (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (scalarPositive k) :=
  (smoothRamp_contDiff.comp (contDiff_const.mul contDiff_id)).div_const _

theorem scalarPositive_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (scalarPositive k) (scalarSlope k t) t := by
  have hn : (k + 1 : ℝ) ≠ 0 := by positivity
  have h := (((smoothRamp_contDiff.differentiable (by norm_num))
    ((k + 1 : ℝ) * t)).hasDerivAt.comp t
      ((hasDerivAt_id t).const_mul (k + 1 : ℝ))).div_const (k + 1 : ℝ)
  change HasDerivAt (fun x => smoothRamp ((k + 1 : ℝ) * x) / (k + 1 : ℝ)) _ t
  simpa only [scalarSlope, Function.comp_def, mul_one, mul_div_cancel_right₀ _ hn] using h

@[simp] theorem scalarPositive_zero (k : ℕ) : scalarPositive k 0 = 0 := by
  simp [scalarPositive, smoothRamp]

theorem scalarPositive_nonneg (k : ℕ) (t : ℝ) : 0 ≤ scalarPositive k t := by
  by_cases ht : t ≤ 0
  · have hnon : (k + 1 : ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
    simp only [scalarPositive, smoothRamp_of_nonpos hnon, zero_div, le_refl]
  · exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_of_not_ge ht))
      (Real.smoothTransition.nonneg _)) (by positivity)

theorem scalarPositive_lipschitz (k : ℕ) : LipschitzWith rampBound (scalarPositive k) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((scalarPositive_contDiff k).differentiable (by norm_num))
  intro t
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (scalarPositive k) t‖ ≤ (rampBound : ℝ)
  rw [← norm_deriv_eq_norm_fderiv, (scalarPositive_hasDerivAt k t).deriv]
  exact rampBound_spec _

theorem scalarPositive_eventually (t : ℝ) :
    ∀ᶠ k : ℕ in atTop, scalarPositive k t = max t 0 := by
  by_cases ht : t ≤ 0
  · filter_upwards [] with k
    have hnon : (k + 1 : ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
    simp [scalarPositive, smoothRamp_of_nonpos hnon, max_eq_right ht]
  · have ht' : 0 < t := lt_of_not_ge ht
    have hlim : Tendsto (fun k : ℕ => (k + 1 : ℝ) * t) atTop atTop :=
      by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)).atTop_mul_const ht'
    filter_upwards [hlim.eventually (eventually_gt_atTop (1 : ℝ))] with k hk
    have hn : (k + 1 : ℝ) ≠ 0 := by positivity
    simp [scalarPositive, smoothRamp_of_one_le hk.le, max_eq_left ht'.le, mul_div_cancel_left₀ _ hn]

theorem scalarSlope_eventually (t : ℝ) :
    ∀ᶠ k : ℕ in atTop, scalarSlope k t = if 0 < t then 1 else 0 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · filter_upwards [] with k
    have hneg : (k + 1 : ℝ) * t < 0 := mul_neg_of_pos_of_neg (by positivity) ht
    simp [scalarSlope, smoothRamp_deriv_neg hneg, ht.not_gt]
  · simp [scalarSlope, smoothRamp_deriv_zero]
  · have hlim : Tendsto (fun k : ℕ => (k + 1 : ℝ) * t) atTop atTop :=
      by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)).atTop_mul_const ht
    filter_upwards [hlim.eventually (eventually_gt_atTop (1 : ℝ))] with k hk
    simp [scalarSlope, smoothRamp_deriv_pos hk, ht]

/-- Apply the proved scalar weak chain rule in the actual derivative graph. -/
theorem smoothPositive_exists {n : ℕ} (Ω : Domain n) (k : ℕ) (u : H ℝ Ω 1) :
    ∃ w : H ℝ Ω 1,
      (hUnderlying Ω 1 w : Space n → ℝ) =ᵐ[domainMeasure Ω]
        (fun x => scalarPositive k (hUnderlying Ω 1 u x)) ∧
      ∀ j : Fin n, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure Ω]
        (fun x => scalarSlope k (hUnderlying Ω 1 u x) * hFirstDerivative u j x) := by
  have hbound : ∃ C : ℝ≥0, ∀ t, ‖fderiv ℝ (scalarPositive k) t‖ ≤ C := by
    refine ⟨rampBound, fun t => ?_⟩
    rw [← norm_deriv_eq_norm_fderiv, (scalarPositive_hasDerivAt k t).deriv]
    exact rampBound_spec _
  obtain ⟨w, hw, hwd⟩ := P102.U4.chain_rule ℝ Ω 2 (hToW ℝ Ω 1 u) (scalarPositive k)
    ((scalarPositive_contDiff k).of_le (by norm_num)) hbound (Or.inl (scalarPositive_zero k))
  refine ⟨(hToW ℝ Ω 1).symm w, ?_, ?_⟩
  · change (P102.U4.sobolevUnderlying ((hToW ℝ Ω 1) ((hToW ℝ Ω 1).symm w)) : _ → ℝ) =ᵐ[_] _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [underlying_toW] using hw
  · intro j
    simpa only [P201.hFirstDerivative, P201Specs.hFirstDerivative,
      ContinuousLinearEquiv.apply_symm_apply, P102.U4.firstWeakDerivative,
      P102.U4.firstSobolevIndex, underlying_toW, fderiv_eq_deriv_mul,
      (scalarPositive_hasDerivAt k _).deriv] using hwd j

def smoothPositive {n : ℕ} (Ω : Domain n) (k : ℕ) (u : H ℝ Ω 1) : H ℝ Ω 1 :=
  (smoothPositive_exists Ω k u).choose

theorem smoothPositive_underlying {n : ℕ} (Ω : Domain n) (k : ℕ) (u : H ℝ Ω 1) :
    (hUnderlying Ω 1 (smoothPositive Ω k u) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => scalarPositive k (hUnderlying Ω 1 u x)) :=
  (smoothPositive_exists Ω k u).choose_spec.1

theorem smoothPositive_derivative {n : ℕ} (Ω : Domain n) (k : ℕ) (u : H ℝ Ω 1) (j : Fin n) :
    (hFirstDerivative (smoothPositive Ω k u) j : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => scalarSlope k (hUnderlying Ω 1 u x) * hFirstDerivative u j x) :=
  (smoothPositive_exists Ω k u).choose_spec.2 j

end P201.Truncation

namespace P201.Truncation

/-- Dominated convergence stated directly for the actual L² classes. -/
theorem lp_tendsto_of_dominated {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (v : ℕ → MeasureTheory.Lp ℝ 2 μ) (w g : MeasureTheory.Lp ℝ 2 μ) (C : ℝ≥0)
    (hb : ∀ k, ∀ᵐ x ∂μ, ‖v k x - w x‖ ≤ C * ‖g x‖)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun k => v k x) atTop (𝓝 (w x))) :
    Tendsto v atTop (𝓝 w) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply P102.U4.eLpNorm_tendsto_zero_of_dominated
    (by norm_num) (by norm_num)
    (fun k => (Lp.aestronglyMeasurable (v k)).sub (Lp.aestronglyMeasurable w))
    ((Lp.memLp g).const_mul (C : ℝ))
  · intro k
    simpa only [norm_mul, Real.norm_of_nonneg C.coe_nonneg, Pi.sub_apply] using hb k
  · filter_upwards [hl] with x hx
    simpa only [sub_self, Pi.sub_apply] using hx.sub_const (w x)

/-- The flat scalar approximations converge in full H¹, including at the
zero level of the input. The cutoff slope is zero at that level. -/
theorem smoothPositive_tendsto {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    Tendsto (fun k => smoothPositive Ω k u) atTop (𝓝 (positivePart Ω u)) := by
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  apply (PiLp.homeomorph 2 (fun _ : P102.U4.SobolevIndex n 1 => Lp ℝ Ω 2)).isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro α
  by_cases hz : α.val = 0
  · have ha : α = P102.U4.zeroSobolevIndex n 1 := Subtype.ext hz
    subst α
    change Tendsto (fun k => hUnderlying Ω 1 (smoothPositive Ω k u))
      atTop (𝓝 (hUnderlying Ω 1 (positivePart Ω u)))
    have he : ∀ᵐ x ∂domainMeasure Ω, ∀ k,
        hUnderlying Ω 1 (smoothPositive Ω k u) x = scalarPositive k (hUnderlying Ω 1 u x) :=
      ae_all_iff.mpr (fun k => smoothPositive_underlying Ω k u)
    apply lp_tendsto_of_dominated _ _ (hUnderlying Ω 1 u) (rampBound + 1)
    · intro k
      filter_upwards [he, positivePart_underlying Ω u] with x hx hp
      rw [hx k, hp]
      have h1 := (scalarPositive_lipschitz k).norm_le_mul (scalarPositive_zero k) (hUnderlying Ω 1 u x)
      have h2 : ‖max (hUnderlying Ω 1 u x) 0‖ ≤ ‖hUnderlying Ω 1 u x‖ := by
        by_cases ht : 0 ≤ hUnderlying Ω 1 u x
        · simp [max_eq_left ht]
        · simp [max_eq_right (le_of_not_ge ht)]
      exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by push_cast; ring))
    · filter_upwards [he, positivePart_underlying Ω u] with x hx hp
      apply tendsto_const_nhds.congr'
      filter_upwards [scalarPositive_eventually (hUnderlying Ω 1 u x)] with k hk
      exact ((hx k).trans (hk.trans hp.symm)).symm
  · have hc : α.val.card = 1 := by
      have := α.property
      have hn := Multiset.card_eq_zero.not.mpr hz
      omega
    obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hc
    have ha : α = ⟨{j}, by simp⟩ := Subtype.ext hj
    subst α
    change Tendsto (fun k => hFirstDerivative (smoothPositive Ω k u) j)
      atTop (𝓝 (hFirstDerivative (positivePart Ω u) j))
    have he : ∀ᵐ x ∂domainMeasure Ω, ∀ k,
        hFirstDerivative (smoothPositive Ω k u) j x =
          scalarSlope k (hUnderlying Ω 1 u x) * hFirstDerivative u j x :=
      ae_all_iff.mpr (fun k => smoothPositive_derivative Ω k u j)
    apply lp_tendsto_of_dominated _ _ (hFirstDerivative u j) (rampBound + 1)
    · intro k
      filter_upwards [he, positivePart_derivative Ω u j] with x hx hp
      rw [hx k, hp]
      have h1 : ‖scalarSlope k (hUnderlying Ω 1 u x) * hFirstDerivative u j x‖ ≤
          rampBound * ‖hFirstDerivative u j x‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (rampBound_spec _) (norm_nonneg _)
      have h2 : ‖if 0 < hUnderlying Ω 1 u x then hFirstDerivative u j x else 0‖ ≤
          ‖hFirstDerivative u j x‖ := by split_ifs <;> simp
      exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by push_cast; ring))
    · filter_upwards [he, positivePart_derivative Ω u j] with x hx hp
      apply tendsto_const_nhds.congr'
      filter_upwards [scalarSlope_eventually (hUnderlying Ω 1 u x)] with k hk
      rw [hx k, hk, hp]
      split_ifs <;> simp

end P201.Truncation

namespace P201.Truncation
open scoped ContDiff

/-- Scalar smoothing of a test remains a test, is nonnegative everywhere,
and has support within the original compact support. -/
def nonnegativeTest {n : ℕ} (Ω : Domain n) (k : ℕ) (φ : Test ℝ Ω) : Test ℝ Ω :=
  ⟨scalarPositive k ∘ φ, (scalarPositive_contDiff k).comp φ.contDiff,
    φ.hasCompactSupport.comp_left (scalarPositive_zero k),
    (tsupport_comp_subset (scalarPositive_zero k) φ).trans φ.tsupport_subset⟩

theorem nonnegativeTest_nonneg {n : ℕ} (Ω : Domain n) (k : ℕ) (φ : Test ℝ Ω) (x : Space n) :
    0 ≤ nonnegativeTest Ω k φ x := scalarPositive_nonneg k (φ x)

theorem smoothPositive_test {n : ℕ} (Ω : Domain n) (k : ℕ) (φ : Test ℝ Ω) :
    smoothPositive Ω k (testToH Ω φ) = testToH Ω (nonnegativeTest Ω k φ) := by
  apply P201.hilbertUnderlyingInjective Ω 1
  apply Lp.ext
  filter_upwards [smoothPositive_underlying Ω k (testToH Ω φ), testToH_underlying Ω φ,
    testToH_underlying Ω (nonnegativeTest Ω k φ)] with x hx hφ ht
  rw [hx, hφ, ht]
  rfl

/-- The closure used to define H¹₀ is exactly the range closure of the
canonical compact test inclusion, with the full Hilbert norm. -/
theorem hZero_eq_closure_test {n : ℕ} (Ω : Domain n) :
    (P201Specs.hZeroSubmodule ℝ Ω : Set (H ℝ Ω 1)) =
      closure (Set.range (testToH Ω)) := by
  change closure _ = closure _
  congr 1
  ext u
  change (∃ φ : Test ℝ Ω, P102.U4.testToDomainLp Ω 2 φ =
      P102.U4.sobolevUnderlying (hToW ℝ Ω 1 u)) ↔ ∃ φ, testToH Ω φ = u
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, P201.hilbertUnderlyingInjective Ω 1 ?_⟩
    apply Lp.ext
    filter_upwards [testToH_underlying Ω φ,
      (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).coeFn_toLp] with x ht hφ'
    exact ht.trans (hφ'.symm.trans (congrArg (fun f : Lp ℝ Ω 2 => f x) hφ))
  · rintro ⟨φ, rfl⟩
    refine ⟨φ, ?_⟩
    change P102.U4.testToDomainLp Ω 2 φ =
      P102.U4.sobolevUnderlying ((hToW ℝ Ω 1) ((hToW ℝ Ω 1).symm _))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose_spec.symm

/-- Nonnegative H¹₀ classes have genuinely nonnegative compact smooth
approximants, without a Lipschitz or boundedness assumption on Ω. -/
theorem nonnegative_density : P201Specs.Truncation.NonnegativeDensityStatement := by
  intro n Ω u hu
  let A : Set (H ℝ Ω 1) := {v | ∃ φ : Test ℝ Ω, (∀ x, 0 ≤ φ x) ∧ testToH Ω φ = v}
  have hp (φ : Test ℝ Ω) : positivePart Ω (testToH Ω φ) ∈ closure A := by
    apply mem_closure_of_tendsto (smoothPositive_tendsto Ω (testToH Ω φ))
    filter_upwards [] with k
    exact ⟨nonnegativeTest Ω k φ, nonnegativeTest_nonneg Ω k φ,
      (smoothPositive_test Ω k φ).symm⟩
  have hucl : u.val ∈ closure (range (testToH Ω)) := by
    rw [← hZero_eq_closure_test]
    exact u.property
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hucl
  have hposlim := (positivePart_continuous Ω).continuousAt.tendsto.comp hlim
  have huplus : positivePart Ω u.val = u.val := by
    apply P201.hilbertUnderlyingInjective Ω 1
    apply Lp.ext
    filter_upwards [positivePart_underlying Ω u.val, hu] with x hx hn
    exact hx.trans (max_eq_left hn)
  change Tendsto (fun k => positivePart Ω (v k)) atTop (𝓝 (positivePart Ω u.val)) at hposlim
  rw [huplus] at hposlim
  have hAcl : u.val ∈ closure A := isClosed_closure.mem_of_tendsto hposlim
    (Eventually.of_forall fun k => by obtain ⟨φ, hφ⟩ := hv k; rw [← hφ]; exact hp φ)
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp hAcl
  choose φ hφ hφw using hw
  refine ⟨φ, hφ, ?_⟩
  simpa only [hφw] using hwlim

end P201.Truncation

namespace P201.Truncation
section Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (θ : ℝ → ℝ) (hθ : Continuous θ) (C : ℝ≥0) (hb : ∀ t, ‖θ t‖ ≤ C)

/-- A bounded continuous scalar multiplier applied to L² data. -/
def multiplierLp (f g : MeasureTheory.Lp ℝ 2 μ) : MeasureTheory.Lp ℝ 2 μ :=
  ((Lp.memLp g).of_le_mul
    ((hθ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul
      (Lp.aestronglyMeasurable g))
    (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))).toLp _

theorem multiplierLp_ae (f g : MeasureTheory.Lp ℝ 2 μ) :
    (multiplierLp θ hθ C hb f g : X → ℝ) =ᵐ[μ] fun x => θ (f x) * g x := by
  exact MemLp.coeFn_toLp _

theorem multiplierLp_sub_bound (f g h : MeasureTheory.Lp ℝ 2 μ) :
    ‖multiplierLp θ hθ C hb f g - multiplierLp θ hθ C hb f h‖ ≤ C * ‖g - h‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplierLp_ae θ hθ C hb f g, multiplierLp_ae θ hθ C hb f h,
    Lp.coeFn_sub (multiplierLp θ hθ C hb f g) (multiplierLp θ hθ C hb f h),
    Lp.coeFn_sub g h] with x hg hh hs hgh
  simp only [hs, hgh, Pi.sub_apply, hg, hh, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

theorem multiplierLp_tendsto_fixed (f : ℕ → MeasureTheory.Lp ℝ 2 μ)
    (a g : MeasureTheory.Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (a x))) :
    Tendsto (fun k => multiplierLp θ hθ C hb (f k) g) atTop
      (𝓝 (multiplierLp θ hθ C hb a g)) := by
  have he : ∀ᵐ x ∂μ, ∀ k, multiplierLp θ hθ C hb (f k) g x = θ (f k x) * g x :=
    ae_all_iff.mpr (fun k => multiplierLp_ae θ hθ C hb (f k) g)
  apply lp_tendsto_of_dominated _ _ g (C + C)
  · intro k
    filter_upwards [he, multiplierLp_ae θ hθ C hb a g] with x hk ha
    rw [hk k, ha, ← sub_mul, norm_mul]
    have hh := (norm_sub_le (θ (f k x)) (θ (a x))).trans (add_le_add (hb _) (hb _))
    simpa only [NNReal.coe_add] using mul_le_mul_of_nonneg_right hh (norm_nonneg (g x))
  · filter_upwards [he, multiplierLp_ae θ hθ C hb a g, hf] with x hk ha hx
    simpa only [hk, ha, Function.comp_def] using ((hθ.tendsto _).comp hx).mul_const (g x)

theorem multiplierLp_tendsto (f g : ℕ → MeasureTheory.Lp ℝ 2 μ)
    (a b : MeasureTheory.Lp ℝ 2 μ) (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b)) :
    Tendsto (fun k => multiplierLp θ hθ C hb (f k) (g k)) atTop
      (𝓝 (multiplierLp θ hθ C hb a b)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hf.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hfix := multiplierLp_tendsto_fixed θ hθ C hb (fun k => f (ns (ms k))) a b hae
  have hsmall : Tendsto
      (fun k => multiplierLp θ hθ C hb (f (ns (ms k))) (g (ns (ms k))) -
        multiplierLp θ hθ C hb (f (ns (ms k))) b) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun k => multiplierLp_sub_bound θ hθ C hb _ _ _)
    simpa only [sub_self, norm_zero, Function.comp_def, mul_zero] using
      (((hg.comp (hns.comp hms.tendsto_atTop)).sub
        (tendsto_const_nhds (x := b))).norm.const_mul (C : ℝ))
  convert hsmall.add hfix using 1 <;> simp
end Multiplier

/-- The smooth scalar approximations themselves act continuously on H¹. -/
theorem smoothPositive_continuous {n : ℕ} (Ω : Domain n) (k : ℕ) :
    Continuous (smoothPositive Ω k) := by
  have hslope : Continuous (scalarSlope k) :=
    (smoothRamp_contDiff.continuous_deriv (by norm_num)).comp
      (continuous_const.mul continuous_id)
  have hbound (t) : ‖scalarSlope k t‖ ≤ rampBound := rampBound_spec _
  apply continuous_iff_seqContinuous.mpr
  intro u v hu
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  apply (PiLp.homeomorph 2 (fun _ : P102.U4.SobolevIndex n 1 => Lp ℝ Ω 2)).isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro α
  have hu0 : Tendsto (fun i => hUnderlying Ω 1 (u i)) atTop (𝓝 (hUnderlying Ω 1 v)) :=
    ((hUnderlying Ω 1).continuous.tendsto v).comp hu
  by_cases hz : α.val = 0
  · have ha : α = P102.U4.zeroSobolevIndex n 1 := Subtype.ext hz
    subst α
    change Tendsto (fun i => hUnderlying Ω 1 (smoothPositive Ω k (u i)))
      atTop (𝓝 (hUnderlying Ω 1 (smoothPositive Ω k v)))
    have he (w : H ℝ Ω 1) : hUnderlying Ω 1 (smoothPositive Ω k w) =
        (scalarPositive_lipschitz k).compLp (scalarPositive_zero k) (hUnderlying Ω 1 w) := by
      apply Lp.ext
      exact (smoothPositive_underlying Ω k w).trans
        ((scalarPositive_lipschitz k).coeFn_compLp (scalarPositive_zero k) _).symm
    simp only [he]
    exact ((scalarPositive_lipschitz k).continuous_compLp
      (scalarPositive_zero k)).tendsto _ |>.comp hu0
  · have hc : α.val.card = 1 := by
      have := α.property
      have hn := Multiset.card_eq_zero.not.mpr hz
      omega
    obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hc
    have ha : α = ⟨{j}, by simp⟩ := Subtype.ext hj
    subst α
    change Tendsto (fun i => hFirstDerivative (smoothPositive Ω k (u i)) j)
      atTop (𝓝 (hFirstDerivative (smoothPositive Ω k v) j))
    have he (w : H ℝ Ω 1) : hFirstDerivative (smoothPositive Ω k w) j =
        multiplierLp (scalarSlope k) hslope rampBound hbound
          (hUnderlying Ω 1 w) (hFirstDerivative w j) := by
      apply Lp.ext
      exact (smoothPositive_derivative Ω k w j).trans
        (multiplierLp_ae (scalarSlope k) hslope rampBound hbound _ _).symm
    simp only [he]
    exact multiplierLp_tendsto (scalarSlope k) hslope rampBound hbound _ _ _ _
      hu0 (tendsto_derivative Ω hu ⟨{j}, by simp⟩)

end P201.Truncation

namespace P201.Truncation

/-- The same smooth scalar approximations converge on any L² measure space. -/
theorem scalarPositive_Lp_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : MeasureTheory.Lp ℝ 2 μ) :
    Tendsto (fun k => (scalarPositive_lipschitz k).compLp (scalarPositive_zero k) g)
      atTop (𝓝 (positiveLp g)) := by
  have he : ∀ᵐ x ∂μ, ∀ k,
      (scalarPositive_lipschitz k).compLp (scalarPositive_zero k) g x = scalarPositive k (g x) :=
    ae_all_iff.mpr (fun k => (scalarPositive_lipschitz k).coeFn_compLp (scalarPositive_zero k) g)
  apply lp_tendsto_of_dominated _ _ g (rampBound + 1)
  · intro k
    filter_upwards [he, positiveLp_ae g] with x hx hp
    rw [hx k, hp]
    have h1 := (scalarPositive_lipschitz k).norm_le_mul (scalarPositive_zero k) (g x)
    have h2 : ‖max (g x) 0‖ ≤ ‖g x‖ := by
      by_cases ht : 0 ≤ g x
      · simp [max_eq_left ht]
      · simp [max_eq_right (le_of_not_ge ht)]
    exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by push_cast; ring))
  · filter_upwards [he, positiveLp_ae g] with x hx hp
    apply tendsto_const_nhds.congr'
    filter_upwards [scalarPositive_eventually (g x)] with k hk
    exact ((hx k).trans (hk.trans hp.symm)).symm

/-- Trace compatibility for the smooth scalar approximations follows from
global smooth density and continuity of both composition operators. -/
theorem smoothPositive_trace {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (k : ℕ)
    (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) (hT : P201Specs.Trace.AgreesWithSmooth T)
    (u : H ℝ Ω 1) :
    P201Specs.Trace.inclusion Ω hΩ (T (smoothPositive Ω k u)) =
      (scalarPositive_lipschitz k).compLp (scalarPositive_zero k)
        (P201Specs.Trace.inclusion Ω hΩ (T u)) := by
  obtain ⟨φ, v, hv, hlim⟩ := P102.Sobolev.Extension.lipschitz_ambient_density
    m (graphFrame m) Ω hΩ ℝ 2 (by norm_num) (hToW ℝ Ω 1 u)
  let w : ℕ → H ℝ Ω 1 := fun i => (hToW ℝ Ω 1).symm (v i)
  have hwlim : Tendsto w atTop (𝓝 u) := by
    simpa only [w, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      ((hToW ℝ Ω 1).symm.continuous.tendsto _).comp hlim
  have hw (i) : (hUnderlying Ω 1 (w i) : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] φ i := by
    have h := hv i (P102.U4.zeroSobolevIndex (m + 1) 1)
    change (P102.U4.sobolevUnderlying
      ((hToW ℝ Ω 1) ((hToW ℝ Ω 1).symm (v i))) : _ → ℝ) =ᵐ[_] _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [P102.U4.sobolevUnderlying, P102.U4.sobolevDerivative,
      P102.U4.zeroSobolevIndex, P102.U4.multiPartial, Multiset.sort_zero,
      P102.U4.partialWord] using h
  let S := (P201Specs.Trace.inclusion Ω hΩ).comp T
  change S (smoothPositive Ω k u) =
    (scalarPositive_lipschitz k).compLp (scalarPositive_zero k) (S u)
  have he (i) : S (smoothPositive Ω k (w i)) =
      (scalarPositive_lipschitz k).compLp (scalarPositive_zero k) (S (w i)) := by
    have hwi := hT (w i) (φ i) (φ i).contDiff (hw i)
    have hcomp : (hUnderlying Ω 1 (smoothPositive Ω k (w i)) : _ → ℝ) =ᵐ[domainMeasure Ω]
        scalarPositive k ∘ φ i := by
      filter_upwards [smoothPositive_underlying Ω k (w i), hw i] with x hx hf
      rw [hx, hf]
      rfl
    have hsi := hT (smoothPositive Ω k (w i)) (scalarPositive k ∘ φ i)
      ((scalarPositive_contDiff k).comp (φ i).contDiff) hcomp
    apply Lp.ext
    filter_upwards [hsi, hwi,
      (scalarPositive_lipschitz k).coeFn_compLp (scalarPositive_zero k) (S (w i))]
      with x hs hw hc
    change S (smoothPositive Ω k (w i)) x = scalarPositive k (φ i x) at hs
    change S (w i) x = φ i x at hw
    rw [hs, hc]
    change scalarPositive k (φ i x) = scalarPositive k (S (w i) x)
    rw [hw]
  have hleft : Tendsto (fun i => S (smoothPositive Ω k (w i))) atTop
      (𝓝 (S (smoothPositive Ω k u))) :=
    (S.continuous.comp (smoothPositive_continuous Ω k)).tendsto u |>.comp hwlim
  have hright : Tendsto (fun i => (scalarPositive_lipschitz k).compLp
      (scalarPositive_zero k) (S (w i))) atTop
      (𝓝 ((scalarPositive_lipschitz k).compLp (scalarPositive_zero k) (S u))) :=
    (((scalarPositive_lipschitz k).continuous_compLp (scalarPositive_zero k)).comp
      S.continuous).tendsto u |>.comp hwlim
  exact tendsto_nhds_unique hleft (by simpa only [he] using hright)

/-- Compatibility with the actual physical C02 trace in every n ≥ 1. -/
theorem trace_positivePart : P201Specs.Truncation.TraceStatement := by
  intro m Ω hΩ T hT u
  let S := (P201Specs.Trace.inclusion Ω hΩ).comp T
  have hleft : Tendsto (fun k => S (smoothPositive Ω k u)) atTop
      (𝓝 (S (positivePart Ω u))) :=
    (S.continuous.tendsto _).comp (smoothPositive_tendsto Ω u)
  have he (k) : S (smoothPositive Ω k u) =
      (scalarPositive_lipschitz k).compLp (scalarPositive_zero k) (S u) :=
    smoothPositive_trace Ω hΩ k T hT u
  have hright : Tendsto (fun k => S (smoothPositive Ω k u)) atTop
      (𝓝 (positiveLp (S u))) := by
    simpa only [he] using scalarPositive_Lp_tendsto (S u)
  have hsame : S (positivePart Ω u) = positiveLp (S u) :=
    tendsto_nhds_unique hleft hright
  change (S (positivePart Ω u) : Space (m + 1) → ℝ) =ᵐ[_] _
  rw [hsame]
  exact positiveLp_ae (S u)

/-- Smooth agreement determines the exact kernel for every physical trace;
the kernel is obtained from the proved C02 ordinary trace theorem. -/
theorem trace_ker {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) (hT : P201Specs.Trace.AgreesWithSmooth T) :
    T.ker = P201Specs.hZeroSubmodule ℝ Ω := by
  let E := hToW ℝ Ω 1
  let S := ((P201Specs.Trace.inclusion Ω hΩ).comp T).comp E.symm.toContinuousLinearMap
  have hS : P102.Trace.Ordinary.IsTrace S := by
    intro w f hf hw
    exact hT (E.symm w) f hf hw
  have hker := P102.Trace.Ordinary.ordinary_trace.2.1 m (graphFrame m) Ω hΩ ℝ 2
    (by norm_num) S hS
  rw [P201.hZeroClosureBridge ℝ Ω, ← hker]
  ext u
  change T u = 0 ↔ S (E u) = 0
  change T u = 0 ↔ P201Specs.Trace.inclusion Ω hΩ (T (E.symm (E u))) = 0
  rw [E.symm_apply_apply]
  exact ⟨fun h => by rw [h, map_zero], fun h =>
    P201.Trace.inclusion_injective Ω hΩ (by rw [h, map_zero])⟩

/-- The exact kernel identifies the ordered-trace test with H¹₀. -/
theorem ordered_trace : P201Specs.Truncation.OrderedTraceStatement := by
  intro m Ω hΩ T hT u v huv
  rw [← trace_ker Ω hΩ T hT]
  change T (positivePart Ω (u - v)) = 0
  apply P201.Trace.inclusion_injective Ω hΩ
  rw [map_zero]
  apply Lp.ext
  have ht := trace_positivePart Ω hΩ T hT (u - v)
  have hsub : P201Specs.Trace.inclusion Ω hΩ (T (u - v)) =
      P201Specs.Trace.inclusion Ω hΩ (T u) - P201Specs.Trace.inclusion Ω hΩ (T v) := by
    simp only [map_sub]
  rw [hsub] at ht
  filter_upwards [ht, huv,
    Lp.coeFn_sub (P201Specs.Trace.inclusion Ω hΩ (T u)) (P201Specs.Trace.inclusion Ω hΩ (T v)),
    Lp.coeFn_zero ℝ 2 (boundaryMeasure Ω)] with x hx huv hs hz
  rw [hx, hs]
  simpa only [Pi.sub_apply, Pi.zero_apply, max_eq_right (sub_nonpos.mpr huv)] using hz.symm

/-- All E04 truncation and nonnegative-test conclusions with the original
objects, arbitrary-open-set bulk scope, and exact physical boundary trace. -/
theorem full_truncation : P201Specs.Truncation.FullStatement :=
  ⟨positivePart_formula, zero_level, positivePart_continuous, trace_positivePart,
    ordered_trace, nonnegative_density⟩

end P201.Truncation
