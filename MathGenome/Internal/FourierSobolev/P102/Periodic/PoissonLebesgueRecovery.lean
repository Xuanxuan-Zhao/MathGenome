import MathGenome.Internal.FourierSobolev.P102.Periodic.PoissonNormRecovery
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.PoissonLebesgueRecovery
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology Interval

namespace P102.Periodic

/-- A nonnegative decreasing weight preserves a bound on all initial integrals.
The second mean value theorem applies to the signed function `h - c`. -/
lemma integral_weight_le_of_primitive_le {b c : ℝ} {h w : ℝ → ℝ}
    (hb : 0 ≤ b) (hh : IntervalIntegrable h volume 0 b)
    (hw : AntitoneOn w (Icc 0 b)) (hw0 : 0 ≤ w b)
    (hprim : ∀ s ∈ Icc 0 b, (∫ t in 0..s, h t) ≤ c * s) :
    (∫ t in 0..b, w t * h t) ≤ c * ∫ t in 0..b, w t := by
  have hwi : IntervalIntegrable w volume 0 b := (by simpa [uIcc_of_le hb] using hw : AntitoneOn w [[0, b]]).intervalIntegrable
  obtain ⟨s, hs, heq⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn hb hw0 hw
      (hh.sub intervalIntegrable_const : IntervalIntegrable (fun t => h t - c) volume 0 b)
  have hs0 : (∫ t in 0..s, h t - c) ≤ 0 := by
    rw [intervalIntegral.integral_sub (hh.mono_set (by
      rw [uIcc_of_le hb, uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2))
      intervalIntegrable_const, intervalIntegral.integral_const]
    simpa only [sub_zero, smul_eq_mul, mul_comm] using sub_nonpos.mpr (hprim s hs)
  have h0 : 0 ≤ w 0 := hw0.trans (hw ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb)
  have hprod : IntervalIntegrable (fun t => w t * h t) volume 0 b := by
    rw [intervalIntegrable_iff]
    exact hh.def'.smul_of_top_right <| (hw.memLp_isCompact isCompact_Icc).mono_measure <|
      Measure.restrict_mono_set volume (by rw [uIoc_of_le hb]; exact Ioc_subset_Icc_self)
  have heq' : (∫ t in 0..b, w t * h t) - c * ∫ t in 0..b, w t =
      w 0 * ∫ t in 0..s, h t - c := by
    rw [← heq, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hprod) (hwi.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  linarith [mul_nonpos_of_nonneg_of_nonpos h0 hs0]

end P102.Periodic

namespace P102.Periodic

variable (T : ℝ) [Fact (0 < T)]

/-- Angular parametrization, including its normalization on a full period. -/
lemma angular_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Circle T → E) :
    (∫ y, f y ∂haar T) = (2 * Real.pi)⁻¹ •
      ∫ v in -Real.pi..Real.pi, f ((T * v / (2 * Real.pi) : ℝ) : Circle T) := by
  rw [← (rescale_measure (2 * Real.pi) T).integral_comp
    (AddCircle.homeomorphAddCircle (2 * Real.pi) T
      (by positivity) (Fact.out : 0 < T).ne').isClosedEmbedding.measurableEmbedding f,
    AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi)]
  simp only [show -Real.pi + 2 * Real.pi = Real.pi by ring, rescale_formula]

lemma angular_interval_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Circle T → E} (hf : Integrable f (haar T)) :
    IntervalIntegrable
      (fun v => f ((T * v / (2 * Real.pi) : ℝ) : Circle T)) volume
      (-Real.pi) Real.pi := by
  have hi := ((rescale_measure (2 * Real.pi) T).comp
    (interval_measure (2 * Real.pi) (-Real.pi))).integrable_comp_of_integrable hf
  rw [integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top] at hi
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
  simpa only [IntegrableOn, Function.comp_def, rescale_formula,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] using hi

lemma angular_ae_eq {f g : Circle T → ℂ} (hfg : f =ᵐ[haar T] g) :
    (fun v => f ((T * v / (2 * Real.pi) : ℝ) : Circle T)) =ᵐ[
      volume.restrict (Ioc (-Real.pi) Real.pi)]
    (fun v => g ((T * v / (2 * Real.pi) : ℝ) : Circle T)) := by
  have h := (interval_measure (2 * Real.pi) (-Real.pi)).quasiMeasurePreserving.ae
    ((rescale_measure (2 * Real.pi) T).quasiMeasurePreserving.ae hfg)
  rw [Measure.ae_ennreal_smul_measure_eq (by positivity)] at h
  simpa only [Filter.EventuallyEq, rescale_formula, show -Real.pi + 2 * Real.pi = Real.pi by ring] using h

/-- A representative change preserves every specified angular Lebesgue value. -/
theorem abel_representative_invariance :
    Expected.PoissonLebesgueRecovery.representativeInvariance := by
  intro T hT f g hfg
  constructor
  · intro r x
    change abelMean T r f x = abelMean T r g x
    unfold abelMean
    simp_rw [coefficient_congr T f g hfg]
  · intro x L
    have he := angular_ae_eq T (f := fun y => f (x - y)) (g := fun y => g (x - y))
      ((measurePreserving_sub_left (haar T) x).quasiMeasurePreserving.ae
        (p := fun y => f y = g y) hfg)
    have heq : ∀ᶠ s : ℝ in 𝓝[>] 0,
        (2 * s)⁻¹ * (∫ v in -s..s,
          ‖f (x - ((T * v / (2 * Real.pi) : ℝ) : Circle T)) - L‖) =
        (2 * s)⁻¹ * (∫ v in -s..s,
          ‖g (x - ((T * v / (2 * Real.pi) : ℝ) : Circle T)) - L‖) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (gt_mem_nhds Real.pi_pos)] with s hs hsπ
      change 0 < s at hs
      congr 1
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by linarith : -s ≤ s)]
      have he' := ae_restrict_of_ae_restrict_of_subset
        (show Ioc (-s) s ⊆ Ioc (-Real.pi) Real.pi from
          Ioc_subset_Ioc (by linarith) hsπ.le) he
      exact he'.mono fun v hv => congrArg (fun z : ℂ => ‖z - L‖) hv
    exact Filter.tendsto_congr' heq

end P102.Periodic

namespace P102.Periodic

/-- Monotone probability kernels recover a function whose initial integrals
are little-o of the radius. This is the near-point/tail argument. -/
lemma weighted_integral_tendsto_zero {l : Filter ℝ} {b M : ℝ}
    {h : ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hb : 0 < b) (hM : 0 ≤ M)
    (hh : IntervalIntegrable h volume 0 b)
    (hn : ∀ s ∈ Icc 0 b, 0 ≤ h s)
    (hw : ∀ᶠ r in l, AntitoneOn (w r) (Icc 0 b) ∧
      (∀ s ∈ Icc 0 b, 0 ≤ w r s) ∧ (∫ s in 0..b, w r s) ≤ M)
    (hd : ∀ δ ∈ Ioc 0 b, Tendsto (fun r => w r δ) l (𝓝 0))
    (hs : ∀ c : ℝ, 0 < c → ∃ δ ∈ Ioc 0 b,
      ∀ s ∈ Icc 0 δ, (∫ t in 0..s, h t) ≤ c * s) :
    Tendsto (fun r => ∫ s in 0..b, w r s * h s) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hw] with r hr
    exact ha.trans_le <| intervalIntegral.integral_nonneg hb.le
      (fun s hs => mul_nonneg (hr.2.1 s hs) (hn s hs))
  · intro ε hε
    let c := ε / (2 * (M + 1))
    have hc : 0 < c := by dsimp [c]; positivity
    obtain ⟨δ, hδ, hprim⟩ := hs c hc
    have hiδ : IntervalIntegrable h volume 0 δ := hh.mono_set <| by
      rw [uIcc_of_le hb.le, uIcc_of_le hδ.1.le]
      exact Icc_subset_Icc le_rfl hδ.2
    have hitail : IntervalIntegrable h volume δ b := hiδ.symm.trans hh
    have ht0 : Tendsto (fun r => w r δ * ∫ s in δ..b, h s) l (𝓝 0) := by
      simpa only [zero_mul] using (hd δ hδ).mul_const (∫ s in δ..b, h s)
    have ht := ht0.eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    filter_upwards [hw, ht] with r hr htail
    have hwi : IntervalIntegrable (w r) volume 0 b := by
      exact (show AntitoneOn (w r) (uIcc 0 b) by
        simpa only [uIcc_of_le hb.le] using hr.1).intervalIntegrable
    have hprod' : IntervalIntegrable (fun s => w r s * h s) volume 0 b := by
      rw [intervalIntegrable_iff]
      exact hh.def'.smul_of_top_right <| (hr.1.memLp_isCompact isCompact_Icc).mono_measure <|
        Measure.restrict_mono_set volume (by rw [uIoc_of_le hb.le]; exact Ioc_subset_Icc_self)
    have hpδ := hprod'.mono_set (show uIcc 0 δ ⊆ uIcc 0 b by
      rw [uIcc_of_le hb.le, uIcc_of_le hδ.1.le]
      exact Icc_subset_Icc le_rfl hδ.2)
    have hptail := hpδ.symm.trans hprod'
    have hnear := integral_weight_le_of_primitive_le hδ.1.le hiδ
      (hr.1.mono (Icc_subset_Icc le_rfl hδ.2))
      (hr.2.1 δ ⟨hδ.1.le, hδ.2⟩) hprim
    have hwδ := hwi.mono_set (show uIcc 0 δ ⊆ uIcc 0 b by
      rw [uIcc_of_le hb.le, uIcc_of_le hδ.1.le]
      exact Icc_subset_Icc le_rfl hδ.2)
    have hmass : (∫ s in 0..δ, w r s) ≤ M := by
      have heq := intervalIntegral.integral_add_adjacent_intervals hwδ (hwδ.symm.trans hwi)
      have hpos := intervalIntegral.integral_nonneg (μ := volume) hδ.2
        (fun s hs => hr.2.1 s ⟨hδ.1.le.trans hs.1, hs.2⟩)
      linarith [hr.2.2]
    have htaille : (∫ s in δ..b, w r s * h s) ≤
        w r δ * ∫ s in δ..b, h s := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hδ.2 hptail (hitail.const_mul _)
      intro s hs
      exact mul_le_mul_of_nonneg_right
        (hr.1 ⟨hδ.1.le, hδ.2⟩ ⟨hδ.1.le.trans hs.1, hs.2⟩ hs.1)
        (hn s ⟨hδ.1.le.trans hs.1, hs.2⟩)
    rw [← intervalIntegral.integral_add_adjacent_intervals hpδ hptail]
    have hcm : c * M < ε / 2 := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (M + 1))).2
      nlinarith
    linarith [hnear, mul_le_mul_of_nonneg_left hmass hc.le]

end P102.Periodic

namespace P102.Periodic

lemma integral_symmetrize {h : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hh : IntervalIntegrable h volume (-s) s) :
    (∫ v in 0..s, h v + h (-v)) = ∫ v in -s..s, h v := by
  have hp : IntervalIntegrable h volume 0 s := hh.mono_set <| by
    rw [uIcc_of_le (by linarith : -s ≤ s), uIcc_of_le hs]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hm : IntervalIntegrable h volume (-s) 0 := hh.mono_set <| by
    rw [uIcc_of_le (by linarith : -s ≤ s), uIcc_of_le (by linarith : -s ≤ 0)]
    exact Icc_subset_Icc le_rfl hs
  have hn : IntervalIntegrable (fun v => h (-v)) volume 0 s := by
    simpa only [neg_neg, neg_zero] using ((IntervalIntegrable.iff_comp_neg).mp hm).symm
  rw [intervalIntegral.integral_add hp hn, intervalIntegral.integral_comp_neg, neg_zero,
    add_comm, intervalIntegral.integral_add_adjacent_intervals hm hp]

variable (T : ℝ) [Fact (0 < T)]

lemma poisson_angular_mass_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ v in 0..Real.pi,
      poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T)) ≤ 2 * Real.pi := by
  let w := fun v : ℝ => poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T)
  have hi := angular_interval_integrable T (poisson_kernel_mass T r hr hr1).1
  have hp : IntervalIntegrable w volume 0 Real.pi := hi.mono_set <| by
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hm : IntervalIntegrable w volume (-Real.pi) 0 := hi.trans hp.symm
  have he := angular_integral_eq T (poissonKernel T r)
  have hmass : (∫ y, poissonKernel T r y ∂haar T) = 1 :=
    (poisson_kernel_mass T r hr hr1).2
  rw [hmass, smul_eq_mul] at he
  have hfull : (∫ v in -Real.pi..Real.pi, w v) = 2 * Real.pi := by
    dsimp [w]
    have hπ : 2 * Real.pi ≠ 0 := by positivity
    field_simp at he
    nlinarith
  have hnonneg : 0 ≤ ∫ v in -Real.pi..0, w v :=
    intervalIntegral.integral_nonneg_of_forall (by linarith [Real.pi_pos])
      (fun v => poisson_nonneg T hr hr1 _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hm hp
  change (∫ v in 0..Real.pi, w v) ≤ 2 * Real.pi
  linarith

lemma poisson_angular_tendsto_zero {δ : ℝ} (hδ : δ ∈ Ioc 0 Real.pi) :
    Tendsto (fun r => poissonKernel T r ((T * δ / (2 * Real.pi) : ℝ) : Circle T))
      (𝓝[<] 1) (𝓝 0) := by
  simp_rw [poisson_angular]
  have hc : Real.cos δ < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 from le_rfl)
      hδ.2 hδ.1
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_id.pow 2)).div
    ((tendsto_const_nhds.sub
      ((tendsto_const_nhds.mul tendsto_id).mul_const (Real.cos δ))).add (tendsto_id.pow 2))
    (show (1 : ℝ) - 2 * 1 * Real.cos δ + 1 ^ 2 ≠ 0 by nlinarith)
  have ht' : Tendsto (fun r : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos δ + r ^ 2))
      (𝓝 1) (𝓝 0) := by
    change Tendsto (fun r : ℝ => (1 - r ^ 2) /
      (1 - 2 * r * Real.cos δ + r ^ 2)) (𝓝 1)
      (𝓝 ((1 - (1 : ℝ) ^ 2) / (1 - 2 * 1 * Real.cos δ + 1 ^ 2))) at ht
    simpa only [one_pow, sub_self, zero_div] using ht
  exact ht'.mono_left nhdsWithin_le_nhds

end P102.Periodic

namespace P102.Periodic

variable (T : ℝ) [Fact (0 < T)]

lemma poisson_error_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {f : Circle T → ℂ} (hf : Integrable f (haar T)) (x : Circle T) (L : ℂ) :
    ‖abelMean T r f x - L‖ ≤ (2 * Real.pi)⁻¹ *
      ∫ v in 0..Real.pi,
        poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T) *
          (‖f (x - ((T * v / (2 * Real.pi) : ℝ) : Circle T)) - L‖ +
            ‖f (x - ((T * (-v) / (2 * Real.pi) : ℝ) : Circle T)) - L‖) := by
  let K : C(Circle T, ℝ) := ⟨poissonKernel T r, poisson_continuous T hr hr1⟩
  have hiF : Integrable (fun y => poissonKernel T r y • f (x - y)) (haar T) :=
    integrable_continuous_smul T (hf.comp_sub_left x) K
  have hc : Integrable (fun y => poissonKernel T r y • L) (haar T) :=
    integrable_continuous_smul T (integrable_const L) K
  have hconv : abelMean T r f x =
      ∫ y, poissonKernel T r y • f (x - y) ∂haar T := by
    have he : abelMean T r f x =
        convolution T f (fun y => (poissonKernel T r y : ℂ)) x :=
      (abel_convolution T r hr hr1 f hf x).2
    rw [he]
    unfold convolution
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      simp only [Complex.real_smul, mul_comm]
  have herr : abelMean T r f x - L =
      ∫ y, poissonKernel T r y • (f (x - y) - L) ∂haar T := by
    simp_rw [smul_sub]
    rw [integral_sub hiF hc,
      integral_smul_const, show (∫ y, poissonKernel T r y ∂haar T) = 1 from
        (poisson_kernel_mass T r hr hr1).2, one_smul, hconv]
  have hnorm : ‖abelMean T r f x - L‖ ≤
      ∫ y, poissonKernel T r y * ‖f (x - y) - L‖ ∂haar T := by
    rw [herr]
    convert norm_integral_le_integral_norm (fun y => poissonKernel T r y • (f (x - y) - L)) using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (poisson_nonneg T hr hr1 y)]
  rw [angular_integral_eq T (fun y => poissonKernel T r y * ‖f (x - y) - L‖),
    smul_eq_mul] at hnorm
  have hgi : Integrable (fun y => poissonKernel T r y * ‖f (x - y) - L‖) (haar T) := by
    simpa only [K, ContinuousMap.coe_mk, Pi.sub_apply, smul_eq_mul] using
      integrable_continuous_smul T (((hf.comp_sub_left x).sub (integrable_const L)).norm) K
  have hs := integral_symmetrize Real.pi_pos.le (angular_interval_integrable T hgi)
  have heven (v : ℝ) :
      poissonKernel T r ((T * (-v) / (2 * Real.pi) : ℝ) : Circle T) =
      poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T) := by
    rw [show T * (-v) / (2 * Real.pi) = -(T * v / (2 * Real.pi)) by ring,
      AddCircle.coe_neg, poisson_even]
  rw [← hs] at hnorm
  convert hnorm using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  rw [heven]
  ring

end P102.Periodic

namespace P102.Periodic

/-- Abel means recover each specified Lebesgue value of an integrable
representative. No almost-everywhere differentiation theorem is assumed. -/
theorem abel_lebesgue_recovery : Expected.PoissonLebesgueRecovery.lebesgueRecovery := by
  intro T hT f hf x L hLeb
  let g := fun v : ℝ => ‖f (x - ((T * v / (2 * Real.pi) : ℝ) : Circle T)) - L‖
  let h := fun v : ℝ => g v + g (-v)
  let w := fun r v : ℝ => poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T)
  have hg : IntervalIntegrable g volume (-Real.pi) Real.pi :=
    angular_interval_integrable T (((hf.comp_sub_left x).sub (integrable_const L)).norm)
  have hgp : IntervalIntegrable g volume 0 Real.pi := hg.mono_set <| by
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hgm : IntervalIntegrable g volume (-Real.pi) 0 := hg.trans hgp.symm
  have hgn : IntervalIntegrable (fun v => g (-v)) volume 0 Real.pi := by
    simpa only [neg_neg, neg_zero] using ((IntervalIntegrable.iff_comp_neg).mp hgm).symm
  have hh : IntervalIntegrable h volume 0 Real.pi := hgp.add hgn
  have hsmall : ∀ c : ℝ, 0 < c → ∃ δ ∈ Ioc 0 Real.pi,
      ∀ s ∈ Icc 0 δ, (∫ t in 0..s, h t) ≤ c * s := by
    intro c hc
    have hlim : Tendsto (fun s : ℝ => (2 * s)⁻¹ * ∫ v in -s..s, g v)
        (𝓝[>] 0) (𝓝 0) := hLeb
    obtain ⟨u, hu, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
      (hlim.eventually_lt_const (show (0 : ℝ) < c / 2 by positivity))
    let δ := min u Real.pi
    have hδ : 0 < δ := lt_min (by exact hu) Real.pi_pos
    refine ⟨δ, ⟨hδ, min_le_right _ _⟩, ?_⟩
    intro s hs
    rcases hs.1.eq_or_lt with hs0 | hs0
    · subst s
      simp
    have hgs : IntervalIntegrable g volume (-s) s := hg.mono_set <| by
      rw [uIcc_of_le (by linarith : -s ≤ s),
        uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      exact Icc_subset_Icc (by linarith [hs.2.trans (min_le_right u Real.pi)])
        (hs.2.trans (min_le_right u Real.pi))
    change (∫ t in 0..s, g t + g (-t)) ≤ c * s
    rw [integral_symmetrize hs.1 hgs]
    have he := hbound (show s ∈ Ioc 0 u from
      ⟨hs0, hs.2.trans (min_le_left u Real.pi)⟩)
    have hi := (inv_mul_lt_iff₀ (show 0 < 2 * s by positivity)).mp he
    nlinarith
  have hparam : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with r hr hr0
    exact ⟨le_of_lt hr0, hr⟩
  have hweight : ∀ᶠ r : ℝ in 𝓝[<] 1,
      AntitoneOn (w r) (Icc 0 Real.pi) ∧
      (∀ s ∈ Icc 0 Real.pi, 0 ≤ w r s) ∧ (∫ s in 0..Real.pi, w r s) ≤ 2 * Real.pi := by
    filter_upwards [hparam] with r hr
    exact ⟨poisson_kernel_monotone T r hr.1 hr.2,
      fun s _ => poisson_nonneg T hr.1 hr.2 _, poisson_angular_mass_bound T hr.1 hr.2⟩
  have ht := weighted_integral_tendsto_zero Real.pi_pos (by positivity : 0 ≤ 2 * Real.pi)
    hh (fun s _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hweight
    (fun δ hδ => poisson_angular_tendsto_zero T hδ) hsmall
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun r => norm_nonneg _))
    (g := fun r => (2 * Real.pi)⁻¹ * ∫ v in 0..Real.pi, w r v * h v)
  · filter_upwards [hparam] with r hr
    exact poisson_error_bound T hr.1 hr.2 hf x L
  · simpa only [mul_zero] using ht.const_mul (2 * Real.pi)⁻¹

/-- The real-valued specialization uses precisely the real absolute
mean-oscillation condition and the canonical scalar embedding. -/
theorem abel_real_lebesgue_recovery :
    Expected.PoissonLebesgueRecovery.realLebesgueRecovery := by
  intro T hT f hf x L hL
  apply abel_lebesgue_recovery T (fun y => (f y : ℂ)) hf.ofReal x (L : ℂ)
  simpa only [Expected.PoissonLebesgueRecovery.HasAngularLebesgueValue,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hL

/-- The full Poisson recovery theorem, with the earlier norm and series
results and the Lebesgue-point and representative conclusions. -/
theorem poisson_complete_recovery : Expected.PoissonLebesgueRecovery.completeRecovery := by
  exact ⟨poisson_kernel_basic, poisson_kernel_series, poisson_kernel_mass,
    poisson_kernel_monotone, poisson_kernel_decay, abel_series, abel_convolution,
    abel_uniform_recovery, abel_real_uniform_recovery, abel_lp_recovery,
    abel_real_lp_recovery, poisson_formula, abel_lebesgue_recovery,
    abel_real_lebesgue_recovery, abel_representative_invariance⟩

end P102.Periodic
