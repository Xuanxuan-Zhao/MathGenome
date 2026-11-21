import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.LogVolterra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeakVolterraResolvent

/-! Logarithmic Volterra operators from `fa2:p5:weak-volterra`.
The common kernel is defined by the actual logarithmic iterates.
The exact first term is removed before applying the power majorant. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.LogVolterra
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraBounds.Spec
open ExpandedFA.PartV

/-- The value at zero is zero by the ordinary real-log convention. -/
lemma continuousOn_logWeight {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun r : ℝ => Real.log r * r^ε) (Ici 0) := by
  intro r hr
  by_cases h : r = 0
  · subst r
    rw [← continuousWithinAt_Ioi_iff_Ici]
    simpa [ContinuousWithinAt] using tendsto_log_mul_rpow_nhdsGT_zero hε
  · exact ((Real.continuousAt_log h).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl h))).continuousWithinAt

/-- Absorb a small positive power into the amplitude, with zero diagonal. -/
def logAmplitude {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (ε : ℝ) (hε : 0 < ε)
    (k : C(triangle T, 𝕜)) : C(triangle T, 𝕜) :=
  ⟨fun z => (Real.log (z.val.1-z.val.2) * (z.val.1-z.val.2)^ε) • k z,
    ((continuousOn_logWeight hε).comp_continuous
      ((continuous_fst.comp continuous_subtype_val).sub
        (continuous_snd.comp continuous_subtype_val))
      (fun z => sub_nonneg.mpr z.property.2.1)).smul k.continuous⟩

lemma logKernel_eq_power {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    {ε : ℝ} (hε : 0 < ε) (k : C(triangle T, 𝕜)) (t s : ℝ) :
    Spec.logKernel k t s = (t-s)^((1-ε)-1) •
      amplitudeValue (logAmplitude ε hε k) t s := by
  classical
  by_cases hz : (t,s) ∈ triangle T
  · simp only [Spec.logKernel, amplitudeValue, dite_eq_left hz, logAmplitude,
      ContinuousMap.coe_mk, smul_smul]
    by_cases hr : t-s = 0
    · simp [hr]
    · have hp : 0 < t-s := lt_of_le_of_ne (sub_nonneg.mpr hz.2.1) (Ne.symm hr)
      congr 1
      calc
        Real.log (t-s) = Real.log (t-s) * (t-s)^(((1-ε)-1)+ε) := by simp
        _ = _ := by rw [Real.rpow_add hp]; ring
  · simp [Spec.logKernel, amplitudeValue, hz]

lemma logIntegrand_eq_power {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    {ε : ℝ} (hε : 0 < ε) (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜) (t s : ℝ) :
    Spec.logIntegrand k f t s = weakIntegrand (1-ε) (logAmplitude ε hε k) f t s := by
  rw [Spec.logIntegrand, logKernel_eq_power hε]
  simp only [weakIntegrand, smul_mul_assoc]

lemma logValue_eq_power {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    {ε : ℝ} (hε : 0 < ε) (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜) (t : ℝ) :
    Spec.logValue k f t = weakValue (1-ε) (logAmplitude ε hε k) f t := by
  simp only [Spec.logValue, weakValue, logIntegrand_eq_power hε]

lemma logIterate_eq_power {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    {ε : ℝ} (hε : 0 < ε) (k : C(triangle T, 𝕜)) (n : ℕ) (t s : ℝ) :
    Spec.logIterate k n t s =
      WeakVolterraResolvent.Spec.iteratedKernel (1-ε) (logAmplitude ε hε k) n t s := by
  induction n generalizing t s with
  | zero => exact logKernel_eq_power hε k t s
  | succ n ih =>
    simp only [Spec.logIterate, WeakVolterraResolvent.Spec.iteratedKernel,
      logKernel_eq_power hε, ih, smul_mul_assoc]

lemma resolvent_eq_power {𝕜 : Type} [RCLike 𝕜] {T ε : ℝ}
    (hε : 0 < ε) (k : C(triangle T, 𝕜)) (ζ : 𝕜)
    {q : C(triangle T, 𝕜)}
    (hq : WeakVolterraResolvent.Spec.KernelSeries (1-ε) (logAmplitude ε hε k) ζ q)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    Spec.resolventKernel k ζ t s =
      (t-s)^((1-ε)-1) • amplitudeValue q t s := by
  have hh := hq.2.2.2 t s hs hst ht
  simpa only [Spec.resolventKernel, logIterate_eq_power hε,
    amplitudeValue, dite_eq_left (show (t,s) ∈ triangle T from ⟨hs,hst.le,ht⟩)] using hh.tsum_eq

lemma resolvent_integrand_eq_ae {𝕜 : Type} [RCLike 𝕜] {T ε : ℝ}
    (hε : 0 < ε) (k : C(triangle T, 𝕜)) (ζ : 𝕜)
    {q : C(triangle T, 𝕜)}
    (hq : WeakVolterraResolvent.Spec.KernelSeries (1-ε) (logAmplitude ε hε k) ζ q)
    (f : ℝ → 𝕜) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fun s => Spec.resolventKernel k ζ t s * f s) =ᵐ[volume.restrict (Ioc 0 t)]
      weakIntegrand (1-ε) q f t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne t)] with s hs hst
  rw [resolvent_eq_power hε k ζ hq hs.1.le (lt_of_le_of_ne hs.2 hst) ht.2]
  simp only [weakIntegrand, smul_mul_assoc]

theorem zero_time : Spec.ZeroTime := by
  intro 𝕜 _ T k f
  simp [Spec.logValue]

/-- All continuous data, including the singleton interval. Boundedness of the
original amplitude follows from compactness of the actual closed triangle. -/
theorem continuous_theorem : Spec.ContinuousTheorem := by
  intro 𝕜 _ T hT k
  let ε : ℝ := 1/2
  have hε : 0 < ε := by norm_num [ε]
  have hα : 0 < 1-ε := by norm_num [ε]
  let a := logAmplitude ε hε k
  obtain ⟨V, hV, hc, hb, hr⟩ := WeakVolterraBounds.continuous_theorem
    (1-ε) T hα hT a ‖a‖ (norm_nonneg _) (fun z => a.norm_coe_le_norm z)
  refine ⟨V, ?_, hc, hr, ?_⟩
  · intro f t
    constructor
    · convert (hV f t).1 using 1
      exact funext (fun s => logIntegrand_eq_power hε k _ t s)
    · simpa only [logValue_eq_power hε] using (hV f t).2
  · intro ζ
    obtain ⟨q, hq, hC, _⟩ := WeakVolterraResolvent.resolvent_representation
      (1-ε) T hα hT a ‖a‖ (norm_nonneg _) (fun z => a.norm_coe_le_norm z) ζ
    obtain ⟨R, hR₁, hR₂, hR⟩ := hC V (fun f t => (hV f t).2)
    refine ⟨R, hR₁, hR₂, ?_⟩
    intro f t
    have he := resolvent_integrand_eq_ae hε k ζ hq (continuousExtension hT f) t.property
    refine ⟨((hR f t).1).congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    exact (hR f t).2

/-- The same integral construction on every a.e. quotient, including both
endpoints. No representative or exceptional set is fixed in advance. -/
theorem lp_theorem : Spec.LpTheorem := by
  intro 𝕜 _ T hT k p _
  let ε : ℝ := 1/2
  have hε : 0 < ε := by norm_num [ε]
  have hα : 0 < 1-ε := by norm_num [ε]
  let a := logAmplitude ε hε k
  obtain ⟨V, hV, hc, hb, hr⟩ := WeakVolterraBounds.lp_theorem
    (1-ε) T hα hT a ‖a‖ (norm_nonneg _) (fun z => a.norm_coe_le_norm z) p
  refine ⟨V, ?_, hc, hr, ?_⟩
  · intro f hf
    constructor
    · filter_upwards [(hV f hf).1] with t ht
      convert ht using 1
      exact funext (fun s => logIntegrand_eq_power hε k f t s)
    · filter_upwards [(hV f hf).2] with t ht
      simpa only [logValue_eq_power hε] using ht
  · intro ζ
    obtain ⟨q, hq, _, hL⟩ := WeakVolterraResolvent.resolvent_representation
      (1-ε) T hα hT a ‖a‖ (norm_nonneg _) (fun z => a.norm_coe_le_norm z) ζ
    obtain ⟨R, hR₁, hR₂, hR⟩ := hL p V (fun f hf => (hV f hf).2)
    refine ⟨R, hR₁, hR₂, ?_⟩
    intro f hf
    obtain ⟨hI, hrep⟩ := hR f hf
    constructor
    · filter_upwards [hI, ae_restrict_mem measurableSet_Ioc] with t hIt ht
      have he := resolvent_integrand_eq_ae hε k ζ hq f ⟨ht.1.le, ht.2⟩
      exact hIt.congr he.symm
    · filter_upwards [hrep, ae_restrict_mem measurableSet_Ioc] with t hrt ht
      have he := resolvent_integrand_eq_ae hε k ζ hq f ⟨ht.1.le, ht.2⟩
      rw [integral_congr_ae he]
      exact hrt

lemma kernel_summable {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (k : C(triangle T, 𝕜)) (ζ : 𝕜)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    Summable (fun n : ℕ => ζ^(n+1) * Spec.logIterate k n t s) := by
  have hε : (0 : ℝ) < 1/2 := by norm_num
  let a := logAmplitude (1/2) hε k
  obtain ⟨q, hq⟩ := WeakVolterraResolvent.kernel_series
    (show (0 : ℝ) < 1-1/2 by norm_num) hT (norm_nonneg a) a
    (fun z => a.norm_coe_le_norm z) ζ
  simpa only [logIterate_eq_power hε] using (hq.2.2.2 t s hs hst ht).summable

/-- After dropping the first iterate, every remaining exponent is at least
2α-1. The majorant is summable independently of the lag for 0 < lag ≤ 1. -/
lemma kernel_tail_bound {𝕜 : Type} [RCLike 𝕜] {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hε₁ : ε < 1)
    (k : C(triangle T, 𝕜)) (ζ : 𝕜) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t s : ℝ), 0 ≤ s → s < t → t ≤ T → t-s ≤ 1 →
      ‖Spec.resolventKernel k ζ t s - ζ * Spec.logKernel k t s‖ ≤
        C * (t-s)^(2*(1-ε)-1) := by
  let α := 1-ε
  have hα : 0 < α := sub_pos.mpr hε₁
  let a := logAmplitude ε hε k
  let M := ‖a‖
  let B (n : ℕ) : ℝ := ‖ζ‖^(n+1) *
    WeakVolterraResolvent.Spec.amplitudeBound α 1 M n
  have hsB : Summable B := WeakVolterraResolvent.summable_amplitude_majorant
    hα (by norm_num) (norm_nonneg a) ‖ζ‖ (norm_nonneg _)
  have hsB' : Summable (fun n => B (n+1)) :=
    (summable_nat_add_iff 1).mpr hsB
  have hB (n : ℕ) : 0 ≤ B n := by
    dsimp [B, WeakVolterraResolvent.Spec.amplitudeBound, M]
    positivity [Real.Gamma_pos_of_pos (show 0 < ((n+1 : ℕ) : ℝ)*α by positivity)]
  refine ⟨∑' n, B (n+1), tsum_nonneg (fun n => hB _), ?_⟩
  intro t s hs hst ht hr₁
  have hr : 0 < t-s := sub_pos.mpr hst
  let F (n : ℕ) : 𝕜 := ζ^(n+1) * Spec.logIterate k n t s
  have hF : Summable F := kernel_summable hT k ζ hs hst ht
  have hbound (n : ℕ) : ‖F (n+1)‖ ≤ (t-s)^(2*α-1) * B (n+1) := by
    change ‖ζ^(n+1+1) * Spec.logIterate k (n+1) t s‖ ≤ _
    rw [norm_mul, norm_pow, logIterate_eq_power hε]
    have hb := WeakVolterraResolvent.iteratedKernel_bound hα hT (norm_nonneg a) a
      (fun z => a.norm_coe_le_norm z) (n+1) t s hs hst ht
    have hp : (t-s)^(((n+1+1 : ℕ) : ℝ)*α-1) ≤ (t-s)^(2*α-1) := by
      apply Real.rpow_le_rpow_of_exponent_ge hr hr₁
      push_cast
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    calc
      _ ≤ ‖ζ‖^(n+1+1) * WeakVolterraResolvent.Spec.kernelBound α M (n+1) (t-s) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (t-s)^(2*α-1) * B (n+1) := by
        dsimp [WeakVolterraResolvent.Spec.kernelBound, B,
          WeakVolterraResolvent.Spec.amplitudeBound]
        simp only [Real.one_rpow]
        have hg : 0 < Real.Gamma (((n+1+1 : ℕ) : ℝ)*α) :=
          Real.Gamma_pos_of_pos (by positivity)
        calc
          _ = (‖ζ‖^(n+1+1) * (M^(n+1+1) * Real.Gamma α^(n+1+1)) /
              Real.Gamma (((n+1+1 : ℕ) : ℝ)*α)) *
                (t-s)^(((n+1+1 : ℕ) : ℝ)*α-1) := by ring
          _ ≤ (‖ζ‖^(n+1+1) * (M^(n+1+1) * Real.Gamma α^(n+1+1)) /
              Real.Gamma (((n+1+1 : ℕ) : ℝ)*α)) * (t-s)^(2*α-1) :=
            mul_le_mul_of_nonneg_left hp (by positivity [Real.Gamma_pos_of_pos hα])
          _ = _ := by ring
  have hnorm : Summable (fun n => ‖F (n+1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound
      (hsB'.mul_left ((t-s)^(2*α-1)))
  have he : Spec.resolventKernel k ζ t s - ζ * Spec.logKernel k t s =
      ∑' n, F (n+1) := by
    have hh := hF.sum_add_tsum_nat_add 1
    simpa only [Finset.sum_range_one, F, Spec.resolventKernel,
      Spec.logIterate, zero_add, pow_one] using (sub_eq_iff_eq_add.mpr (hh.symm.trans (add_comm _ _)))
  rw [he]
  calc
    _ ≤ ∑' n, ‖F (n+1)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, (t-s)^(2*α-1) * B (n+1) :=
      hnorm.tsum_le_tsum hbound (hsB'.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

theorem leading_term : Spec.LeadingTerm := by
  intro 𝕜 _ T hT k ζ
  refine ⟨fun t s hs hst ht => kernel_summable hT k ζ hs hst ht, ?_⟩
  intro ε hε hε₁
  obtain ⟨C, hC, hb⟩ := kernel_tail_bound hT hε (by linarith) k ζ
  refine ⟨C, hC, ?_⟩
  simpa only [show 2*(1-ε)-1 = 1-2*ε by ring] using hb

end ExpandedFA.PartV.LogVolterra
