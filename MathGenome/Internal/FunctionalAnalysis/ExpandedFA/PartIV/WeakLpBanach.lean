import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WeakLpBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.DistributionFunctions
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV

noncomputable def weakLpQuasiNorm : WeakLpBanachSpec.QuasiNormType := @weakLpQ
noncomputable def weakLpNorm : WeakLpBanachSpec.QuasiNormType := @weakLpN

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

@[simp] theorem weakLpN_zero (μ : Measure Ω) (p : ℝ) :
    weakLpN μ p (0 : Ω → E) = 0 := by
  simp [weakLpN]

@[simp] theorem weakLpN_zero_measure (p : ℝ) (f : Ω → E) : weakLpN 0 p f = 0 := by
  simp [weakLpN]

@[simp] theorem weakLpQ_zero_measure (p : ℝ) (hp : 0 < p) (f : Ω → E) :
    weakLpQ 0 p f = 0 := by
  simp [weakLpQ, DistributionFunctionsSpec.DistributionValue,
    hp]

/-- The norm depends only on the a.e. equivalence class. -/
theorem weakLpN_congr_ae (μ : Measure Ω) (p : ℝ) {f g : Ω → E} (h : f =ᵐ[μ] g) :
    weakLpN μ p f = weakLpN μ p g := by
  unfold weakLpN
  congr 1
  funext A
  congr 1
  funext hA
  congr 1
  funext hpos
  congr 1
  exact lintegral_congr_ae (ae_restrict_of_ae (h.fun_comp enorm))

/-- Testing a fixed positive-measure measurable set. -/
theorem weakLpN_test (μ : Measure Ω) (p : ℝ) (f : Ω → E)
    {A : Set Ω} (hA : MeasurableSet A) (hpos : 0 < μ A) :
    (μ A) ^ (1 / p - 1) * (∫⁻ x in A, ‖f x‖ₑ ∂μ) ≤ weakLpN μ p f :=
  le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le hpos le_rfl))

theorem weakLpN_add_le (μ : Measure Ω) (p : ℝ) (f g : Ω → E)
    (hf : AEStronglyMeasurable f μ) :
    weakLpN μ p (f + g) ≤ weakLpN μ p f + weakLpN μ p g := by
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hpos => ?_
  calc
    _ ≤ (μ A) ^ (1 / p - 1) *
        ((∫⁻ x in A, ‖f x‖ₑ ∂μ) + ∫⁻ x in A, ‖g x‖ₑ ∂μ) := by
      gcongr
      exact (lintegral_mono fun x => enorm_add_le (f x) (g x)).trans
        (le_of_eq (lintegral_add_left' (hf.enorm.restrict) _))
    _ = _ + _ := mul_add _ _ _
    _ ≤ _ := add_le_add (weakLpN_test μ p f hA hpos) (weakLpN_test μ p g hA hpos)

@[simp] theorem weakLpN_neg (μ : Measure Ω) (p : ℝ) (f : Ω → E) :
    weakLpN μ p (-f) = weakLpN μ p f := by
  simp [weakLpN]

/-- A fixed-set integral is controlled by N, with zero sets handled separately. -/
theorem setLIntegral_enorm_le_weakLpN (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (f : Ω → E) {A : Set Ω} (hA : MeasurableSet A) :
    (∫⁻ x in A, ‖f x‖ₑ ∂μ) ≤ (μ A) ^ (1 - 1 / p) * weakLpN μ p f := by
  by_cases hzero : μ A = 0
  · simp [Measure.restrict_eq_zero.mpr hzero]
  have hm := weakLpN_test μ p f hA (pos_iff_ne_zero.mpr hzero)
  have hcancel : (μ A) ^ (1 - 1 / p) * (μ A) ^ (1 / p - 1) = 1 := by
    rw [← ENNReal.rpow_add _ _ hzero (measure_ne_top μ A)]
    ring_nf
    exact ENNReal.rpow_zero
  calc
    _ = (μ A) ^ (1 - 1 / p) * ((μ A) ^ (1 / p - 1) *
        (∫⁻ x in A, ‖f x‖ₑ ∂μ)) := by rw [← mul_assoc, hcancel, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hm

/-- In particular the embedding into L1 used in completeness is quantitative. -/
theorem lintegral_enorm_le_weakLpN (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (f : Ω → E) :
    (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ (μ univ) ^ (1 - 1 / p) * weakLpN μ p f := by
  simpa using setLIntegral_enorm_le_weakLpN μ p f MeasurableSet.univ

/-- The quasi-norm also descends to a.e. classes. -/
theorem weakLpQ_congr_ae (μ : Measure Ω) (p : ℝ) {f g : Ω → E} (h : f =ᵐ[μ] g) :
    weakLpQ μ p f = weakLpQ μ p g := by
  have hd : DistributionFunctionsSpec.DistributionValue μ f =
      DistributionFunctionsSpec.DistributionValue μ g := by
    funext t
    apply measure_congr
    filter_upwards [h] with x hx using by simp [hx]
  simp only [weakLpQ, hd]

/-- The lower comparison first for a measurable modulus. -/
theorem weakLpQ_le_weakLpN_of_measurable (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 0 < p) (f : Ω → E) (hf : Measurable (fun x => ‖f x‖)) :
    weakLpQ μ p f ≤ weakLpN μ p f := by
  refine iSup_le fun t => iSup_le fun ht => ?_
  let A : Set Ω := {x | t < ‖f x‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  change ENNReal.ofReal t * (μ A) ^ (1 / p) ≤ _
  by_cases hz : μ A = 0
  · simp [hz, hp]
  have hi : ENNReal.ofReal t * μ A ≤ ∫⁻ x in A, ‖f x‖ₑ ∂μ := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono' hA
    intro x hx
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx.le
  calc
    _ = (μ A) ^ (1 / p - 1) * (ENNReal.ofReal t * μ A) := by
      have he : (μ A) ^ (1 / p - 1) * μ A = (μ A) ^ (1 / p) := by
        nth_rw 2 [← ENNReal.rpow_one (x := μ A)]
        rw [← ENNReal.rpow_add _ _ hz (measure_ne_top μ A)]
        congr 1
        ring
      calc
        _ = ENNReal.ofReal t * ((μ A) ^ (1 / p - 1) * μ A) := by rw [he]
        _ = _ := by ac_rfl
    _ ≤ (μ A) ^ (1 / p - 1) * (∫⁻ x in A, ‖f x‖ₑ ∂μ) := mul_le_mul' le_rfl hi
    _ ≤ _ := weakLpN_test μ p f hA (pos_iff_ne_zero.mpr hz)

theorem weakLpQ_le_weakLpN (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 0 < p) (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    weakLpQ μ p f ≤ weakLpN μ p f := by
  rw [weakLpQ_congr_ae μ p hf.ae_eq_mk, weakLpN_congr_ae μ p hf.ae_eq_mk]
  exact weakLpQ_le_weakLpN_of_measurable μ p hp _ hf.stronglyMeasurable_mk.norm.measurable

/-- Definiteness is tested on the whole space, and works for zero total measure. -/
theorem weakLpN_eq_zero_iff (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    weakLpN μ p f = 0 ↔ f =ᵐ[μ] 0 := by
  constructor
  · intro hn
    have hi : (∫⁻ x, ‖f x‖ₑ ∂μ) = 0 := by
      apply le_antisymm _ bot_le
      simpa [hn] using lintegral_enorm_le_weakLpN μ p f
    have hz := (lintegral_eq_zero_iff' hf.enorm).mp hi
    filter_upwards [hz] with x hx
    exact enorm_eq_zero.mp hx
  · intro hf0
    rw [weakLpN_congr_ae μ p hf0, weakLpN_zero]

/-- Fatou for the actual N functional, before passing to the a.e. quotient. -/
theorem weakLpN_fatou (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ) (fs : ℕ → Ω → E) (f : Ω → E)
    (hfs : ∀ n, AEStronglyMeasurable (fs n) μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    weakLpN μ p f ≤ liminf (fun n => weakLpN μ p (fs n)) atTop := by
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hpos => ?_
  let c : ℝ≥0∞ := (μ A) ^ (1 / p - 1)
  have hc : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg' hpos (measure_ne_top μ A)
  calc
    _ = ∫⁻ x in A, c * ‖f x‖ₑ ∂μ := (lintegral_const_mul' c _ hc).symm
    _ = ∫⁻ x in A, liminf (fun n => c * ‖fs n x‖ₑ) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hconv] with x hx
      exact (Tendsto.liminf_eq ((ENNReal.continuous_const_mul hc).tendsto _ |>.comp
        ((continuous_enorm.tendsto _).comp hx))).symm
    _ ≤ liminf (fun n => ∫⁻ x in A, c * ‖fs n x‖ₑ ∂μ) atTop :=
      lintegral_liminf_le' (fun n => aemeasurable_const.mul (hfs n).enorm.restrict)
    _ ≤ _ := by
      refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
      show (∫⁻ x in A, c * ‖fs n x‖ₑ ∂μ) ≤ weakLpN μ p (fs n)
      rw [lintegral_const_mul' c _ hc]
      exact weakLpN_test μ p (fs n) hA hpos

/-- A weak quasi-norm bound controls every positive distribution level. -/
theorem distribution_le_of_weakLpQ_le (μ : Measure Ω) (p : ℝ) (hp : 0 < p)
    (f : Ω → E) (C : ℝ) (hC : 0 ≤ C) (hbound : weakLpQ μ p f ≤ ENNReal.ofReal C)
    (t : ℝ) (ht : 0 < t) :
    distribution μ f t ≤ ENNReal.ofReal (C ^ p) * ENNReal.ofReal (t ^ (-p)) := by
  have hb : ENNReal.ofReal t * distribution μ f t ^ (1 / p) ≤ ENNReal.ofReal C :=
    (show ENNReal.ofReal t * DistributionFunctionsSpec.DistributionValue μ f t ^ (1 / p) ≤
      weakLpQ μ p f from le_iSup_of_le t (le_iSup_of_le ht le_rfl)).trans hbound
  have hb' := ENNReal.rpow_le_rpow hb hp.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC hp.le] at hb'
  have ht0 : (ENNReal.ofReal t) ^ p ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ht) ENNReal.ofReal_ne_top).ne'
  have htfin : (ENNReal.ofReal t) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have he : (ENNReal.ofReal t ^ p)⁻¹ = ENNReal.ofReal (t ^ (-p)) := by
    rw [← ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos ht]
  calc
    _ = (ENNReal.ofReal t ^ p)⁻¹ * (ENNReal.ofReal t ^ p * distribution μ f t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 htfin, one_mul]
    _ ≤ (ENNReal.ofReal t ^ p)⁻¹ * ENNReal.ofReal (C ^ p) := mul_le_mul' le_rfl hb'
    _ = _ := by rw [he, mul_comm]

/-- The scalar tail integral used in the sharp comparison. -/
theorem lintegral_Ioi_rpow_neg (p a : ℝ) (hp : 1 < p) (ha : 0 < a) :
    (∫⁻ t : ℝ in Ioi a, ENNReal.ofReal (t ^ (-p))) =
      ENNReal.ofReal (a ^ (1 - p) / (p - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) ha)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
      Real.rpow_nonneg ((ha.trans ht).le) _)),
    integral_Ioi_rpow_of_lt (by linarith : -p < -1) ha]
  congr 1
  rw [show -p + 1 = 1 - p by ring]
  simp only [show 1 - p = -(p - 1) by ring, div_neg, neg_div, neg_neg]

/-- Elementary optimization of the two pieces of the distribution integral. -/
lemma weakLp_balance (p m C : ℝ) (hp : 1 < p) (hm : 0 < m) (hC : 0 < C) :
    let a := C * m ^ (-1 / p)
    m * a + C ^ p * a ^ (1 - p) / (p - 1) =
      (p / (p - 1)) * C * m ^ (1 - 1 / p) := by
  dsimp only
  have he : (-1 / p) * (1 - p) = 1 - 1 / p := by
    field_simp
    ring
  have hfirst : m * (C * m ^ (-1 / p)) = C * m ^ (1 - 1 / p) := by
    calc
      _ = C * (m ^ (1 : ℝ) * m ^ (-1 / p)) := by rw [Real.rpow_one]; ring
      _ = C * m ^ (1 - 1 / p) := by
        rw [← Real.rpow_add hm]
        congr 2
        ring
  have hsecond : C ^ p * (C * m ^ (-1 / p)) ^ (1 - p) =
      C * m ^ (1 - 1 / p) := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hm.le _),
      ← Real.rpow_mul hm.le, he]
    calc
      _ = (C ^ p * C ^ (1 - p)) * m ^ (1 - 1 / p) := by ring
      _ = _ := by rw [← Real.rpow_add hC, add_sub_cancel, Real.rpow_one]
  rw [hfirst, hsecond]
  have hne : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- A positive upper bound for Q gives the sharp bound on each set integral. -/
theorem setLIntegral_enorm_le_of_weakLpQ_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (f : Ω → E) (hf : Measurable (fun x => ‖f x‖))
    (C : ℝ) (hC : 0 < C) (hbound : weakLpQ μ p f ≤ ENNReal.ofReal C)
    {A : Set Ω} (_hA : MeasurableSet A) (hpos : 0 < μ A) :
    (∫⁻ x in A, ‖f x‖ₑ ∂μ) ≤
      ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal C * (μ A) ^ (1 - 1 / p) := by
  let m : ℝ := (μ A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  have hmE : ENNReal.ofReal m = μ A := ENNReal.ofReal_toReal (measure_ne_top μ A)
  let a : ℝ := C * m ^ (-1 / p)
  have ha : 0 < a := mul_pos hC (Real.rpow_pos_of_pos hm _)
  have hpp : 0 ≤ p / (p - 1) := by positivity
  have hunion : Ioc 0 a ∪ Ioi a = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact ha.trans ht
    · intro ht
      exact (le_or_gt t a).elim (fun h => Or.inl ⟨ht, h⟩) Or.inr
  have hdist (t : ℝ) : distribution (μ.restrict A) f t ≤ μ A := by
    unfold distribution
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hf)]
    exact measure_mono inter_subset_right
  have hdist' (t : ℝ) (ht : a < t) : distribution (μ.restrict A) f t ≤
      ENNReal.ofReal (C ^ p) * ENNReal.ofReal (t ^ (-p)) := by
    apply le_trans _ (distribution_le_of_weakLpQ_le μ p (by linarith) f C hC.le hbound t
      (ha.trans ht))
    unfold distribution
    exact Measure.restrict_apply_le _ _
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), distribution (μ.restrict A) f t := by
      simpa only [ofReal_norm, distribution] using
        (lintegral_eq_lintegral_meas_lt (μ.restrict A)
          (ae_of_all _ (fun x => norm_nonneg (f x))) hf.aemeasurable)
    _ = (∫⁻ t in Ioc 0 a, distribution (μ.restrict A) f t) +
        ∫⁻ t in Ioi a, distribution (μ.restrict A) f t := by
      rw [← hunion, lintegral_union measurableSet_Ioi (by
        apply disjoint_left.2
        intro t ht hs
        exact (not_lt_of_ge ht.2) hs)]
    _ ≤ (ENNReal.ofReal m * ENNReal.ofReal a) +
        ENNReal.ofReal (C ^ p) * ENNReal.ofReal (a ^ (1 - p) / (p - 1)) := by
      apply add_le_add
      · calc
          _ ≤ ∫⁻ _t : ℝ in Ioc 0 a, μ A := lintegral_mono (fun t => hdist t)
          _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero, hmE]
      · calc
          _ ≤ ∫⁻ t : ℝ in Ioi a, ENNReal.ofReal (C ^ p) * ENNReal.ofReal (t ^ (-p)) :=
            setLIntegral_mono' measurableSet_Ioi hdist'
          _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioi_rpow_neg p a hp ha]
    _ = ENNReal.ofReal (m * a + C ^ p * a ^ (1 - p) / (p - 1)) := by
      rw [ENNReal.ofReal_add (mul_nonneg hm.le ha.le)
        (by positivity : 0 ≤ C ^ p * a ^ (1 - p) / (p - 1)),
        ENNReal.ofReal_mul hm.le]
      congr 1
      rw [show C ^ p * a ^ (1 - p) / (p - 1) = C ^ p * (a ^ (1 - p) / (p - 1)) by ring,
        ENNReal.ofReal_mul (Real.rpow_nonneg hC.le _)]
    _ = _ := by
      rw [weakLp_balance p m C hp hm hC,
        ENNReal.ofReal_mul (mul_nonneg hpp hC.le), ENNReal.ofReal_mul hpp,
        ← ENNReal.ofReal_rpow_of_pos hm, hmE]

/-- The upper comparison with any strictly positive upper bound for Q. -/
theorem weakLpN_le_of_weakLpQ_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (f : Ω → E) (hf : Measurable (fun x => ‖f x‖))
    (C : ℝ) (hC : 0 < C) (hbound : weakLpQ μ p f ≤ ENNReal.ofReal C) :
    weakLpN μ p f ≤ ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal C := by
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hpos => ?_
  calc
    _ ≤ (μ A) ^ (1 / p - 1) * (ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal C *
        (μ A) ^ (1 - 1 / p)) :=
      mul_le_mul' le_rfl (setLIntegral_enorm_le_of_weakLpQ_le μ p hp f hf C hC hbound hA hpos)
    _ = _ := by
      have he : (μ A) ^ (1 / p - 1) * (μ A) ^ (1 - 1 / p) = 1 := by
        rw [← ENNReal.rpow_add _ _ hpos.ne' (measure_ne_top μ A)]
        rw [show 1 / p - 1 + (1 - 1 / p) = (0 : ℝ) by ring, ENNReal.rpow_zero]
      calc
        _ = (ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal C) *
            ((μ A) ^ (1 / p - 1) * (μ A) ^ (1 - 1 / p)) := by ac_rfl
        _ = _ := by rw [he, mul_one]

theorem weakLpN_le_conj_mul_weakLpQ_of_measurable (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (f : Ω → E) (hf : Measurable (fun x => ‖f x‖)) :
    weakLpN μ p f ≤ ENNReal.ofReal (p / (p - 1)) * weakLpQ μ p f := by
  have hpp : 0 < p / (p - 1) := by positivity
  by_cases htop : weakLpQ μ p f = ∞
  · simp [htop, ENNReal.mul_top, hpp]
  let b : ℝ := (weakLpQ μ p f).toReal
  have hb : ENNReal.ofReal b = weakLpQ μ p f := ENNReal.ofReal_toReal htop
  have hcont : Continuous (fun ε : ℝ =>
      ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (b + ε)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id))
  have hlim : Tendsto (fun ε : ℝ =>
      ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (b + ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (p / (p - 1)) * weakLpQ μ p f)) := by
    simpa only [add_zero, hb] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply weakLpN_le_of_weakLpQ_le μ p hp f hf (b + ε)
    (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)
  rw [← hb]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hε.le)

theorem weakLpN_le_conj_mul_weakLpQ (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    weakLpN μ p f ≤ ENNReal.ofReal (p / (p - 1)) * weakLpQ μ p f := by
  rw [weakLpN_congr_ae μ p hf.ae_eq_mk, weakLpQ_congr_ae μ p hf.ae_eq_mk]
  exact weakLpN_le_conj_mul_weakLpQ_of_measurable μ p hp _ hf.stronglyMeasurable_mk.norm.measurable

theorem weakLp_comparison : WeakLpBanachSpec.ComparisonStatement := by
  intro Ω E _ _ μ _ p hp f hf
  exact ⟨weakLpQ_le_weakLpN μ p (by linarith) f hf, weakLpN_le_conj_mul_weakLpQ μ p hp f hf⟩

/-- Finite N gives an actual L1 function, not just local integrability. -/
theorem integrable_of_weakLpN_lt_top (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (f : Ω → E) (hf : AEStronglyMeasurable f μ)
    (hfin : weakLpN μ p f < ∞) : Integrable f μ := by
  have hpow : 0 ≤ 1 - 1 / p := by
    have : 1 / p < 1 := (div_lt_one (by linarith : 0 < p)).mpr hp
    linarith
  refine ⟨hf, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact (lintegral_enorm_le_weakLpN μ p f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hpow (measure_ne_top μ univ)) hfin)

section Scalar
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp] theorem weakLpN_smul (μ : Measure Ω) (p : ℝ) (c : 𝕜) (f : Ω → 𝕜) :
    weakLpN μ p (c • f) = ‖c‖ₑ * weakLpN μ p f := by
  simp only [weakLpN, Pi.smul_apply, enorm_smul,
    lintegral_const_mul' _ _ (enorm_ne_top (x := c)), ENNReal.mul_iSup]
  congr 1
  funext A
  congr 1
  funext hA
  congr 1
  funext hpos
  ac_rfl

/-- The finite-N a.e. classes form the required scalar vector space. -/
noncomputable def weakLpSubmodule (μ : Measure Ω) (p : ℝ) :
    Submodule 𝕜 (Ω →ₘ[μ] 𝕜) where
  carrier := {f | weakLpN μ p f < ∞}
  zero_mem' := by
    change weakLpN μ p ((0 : Ω →ₘ[μ] 𝕜) : Ω → 𝕜) < ∞
    rw [weakLpN_congr_ae μ p AEEqFun.coeFn_zero, weakLpN_zero]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro f g hf hg
    change weakLpN μ p ((f + g : Ω →ₘ[μ] 𝕜) : Ω → 𝕜) < ∞
    rw [weakLpN_congr_ae μ p (AEEqFun.coeFn_add f g)]
    exact (weakLpN_add_le μ p f g f.aestronglyMeasurable).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)
  smul_mem' := by
    intro c f hf
    change weakLpN μ p ((c • f : Ω →ₘ[μ] 𝕜) : Ω → 𝕜) < ∞
    rw [weakLpN_congr_ae μ p (AEEqFun.coeFn_smul c f), weakLpN_smul]
    exact ENNReal.mul_lt_top (enorm_lt_top) hf

/-- Membership is exactly finite N, without replacing the space by its completion. -/
@[simp] theorem mem_weakLpSubmodule (μ : Measure Ω) (p : ℝ) (f : Ω →ₘ[μ] 𝕜) :
    f ∈ weakLpSubmodule μ p ↔ weakLpN μ p f < ∞ := Iff.rfl

/-- The norm on the finite-N submodule is N itself. -/
noncomputable instance weakLpSubmoduleNorm (μ : Measure Ω) (p : ℝ) :
    Norm (weakLpSubmodule (𝕜 := 𝕜) μ p) :=
  ⟨fun f => (weakLpN μ p (f : Ω →ₘ[μ] 𝕜)).toReal⟩

theorem weakLpNormCore (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ) :
    NormedSpace.Core 𝕜 (weakLpSubmodule (𝕜 := 𝕜) μ p) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c f := by
    change (weakLpN μ p (⇑(c • f.val : Ω →ₘ[μ] 𝕜))).toReal = _
    rw [weakLpN_congr_ae μ p (AEEqFun.coeFn_smul c f.val), weakLpN_smul,
      ENNReal.toReal_mul, toReal_enorm]
    rfl
  norm_triangle f g := by
    change (weakLpN μ p (⇑(f.val + g.val : Ω →ₘ[μ] 𝕜))).toReal ≤ _
    rw [weakLpN_congr_ae μ p (AEEqFun.coeFn_add f.val g.val)]
    calc
      _ ≤ (weakLpN μ p (f : Ω →ₘ[μ] 𝕜) + weakLpN μ p (g : Ω →ₘ[μ] 𝕜)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨f.property.ne, g.property.ne⟩)
          (weakLpN_add_le μ p f.val g.val f.val.aestronglyMeasurable)
      _ = _ := ENNReal.toReal_add f.property.ne g.property.ne
  norm_eq_zero_iff f := by
    change (weakLpN μ p (f : Ω →ₘ[μ] 𝕜)).toReal = 0 ↔ f = 0
    rw [ENNReal.toReal_eq_zero_iff, or_iff_left f.property.ne,
      weakLpN_eq_zero_iff μ p _ f.val.aestronglyMeasurable]
    constructor
    · intro h
      apply Subtype.ext
      exact AEEqFun.ext (h.trans AEEqFun.coeFn_zero.symm)
    · intro h
      subst f
      change ((0 : Ω →ₘ[μ] 𝕜) : Ω → 𝕜) =ᵐ[μ] 0
      exact AEEqFun.coeFn_zero

noncomputable instance weakLpNormedAddCommGroup (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ) :
    NormedAddCommGroup (weakLpSubmodule (𝕜 := 𝕜) μ p) :=
  .ofCore (weakLpNormCore μ p)

noncomputable instance weakLpNormedSpace (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ) :
    NormedSpace 𝕜 (weakLpSubmodule (𝕜 := 𝕜) μ p) := .ofCore (weakLpNormCore μ p)

/-- Cauchy sequences for N converge through an actual L1 limit and a.e. subsequence. -/
theorem weakLp_l1_limit : WeakLpBanachSpec.L1LimitStatement := by
  intro Ω 𝕜 _ _ μ _ p hp fs hfs hfin hC
  have hpow : 0 ≤ 1 - 1 / p := by
    have : 1 / p < 1 := (div_lt_one (by linarith : 0 < p)).mpr hp
    linarith
  let c : ℝ≥0∞ := (μ univ) ^ (1 - 1 / p)
  have hc : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hpow (measure_ne_top μ univ)
  have hmem (n : ℕ) : MemLp (fs n) 1 μ :=
    (memLp_one_iff_integrable).mpr (integrable_of_weakLpN_lt_top μ p hp _ (hfs n) (hfin n))
  let F : ℕ → Lp 𝕜 1 μ := fun n => (hmem n).toLp (fs n)
  have hL1C : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fs nm.1 - fs nm.2) 1 μ)
      atTop (𝓝 0) := by
    have hbound := (ENNReal.continuous_const_mul hc).tendsto 0 |>.comp hC
    simp only [mul_zero] at hbound
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun _ => bot_le) ?_
    apply Eventually.of_forall
    intro nm
    rw [eLpNorm_one_eq_lintegral_enorm ((hfs nm.1).sub (hfs nm.2))]
    exact lintegral_enorm_le_weakLpN μ p _
  have hFC : CauchySeq F := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    refine hL1C.congr' (Eventually.of_forall fun nm => ?_)
    exact eLpNorm_congr_ae ((hmem nm.1).coeFn_toLp.sub (hmem nm.2).coeFn_toLp).symm
  obtain ⟨g, hFg⟩ := cauchySeq_tendsto_of_complete hFC
  have hL1 : Tendsto (fun n => eLpNorm (fs n - (g : Ω → 𝕜)) 1 μ) atTop (𝓝 0) := by
    have hh := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F g).mp hFg
    refine hh.congr' (Eventually.of_forall fun n => ?_)
    exact eLpNorm_congr_ae ((hmem n).coeFn_toLp.sub EventuallyEq.rfl)
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hL1).exists_seq_tendsto_ae
  have hN : Tendsto (fun n => weakLpN μ p (fs n - (g : Ω → 𝕜))) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨⟨n₀, m₀⟩, hb⟩ := (ENNReal.tendsto_atTop_zero.mp hC) ε hε
    refine ⟨max n₀ m₀, fun n hn => ?_⟩
    calc
      _ ≤ liminf (fun j => weakLpN μ p (fs n - fs (σ j))) atTop := by
        apply weakLpN_fatou μ p _ _ (fun j => (hfs n).sub (hfs (σ j)))
        filter_upwards [hae] with x hx
        exact tendsto_const_nhds.sub hx
      _ ≤ ε := by
        apply liminf_le_of_frequently_le'
        apply Eventually.frequently
        filter_upwards [hσ.tendsto_atTop.eventually (eventually_ge_atTop m₀)] with j hj
        exact hb (n, σ j) ⟨(le_max_left _ _).trans hn, hj⟩
  obtain ⟨N, hNbound⟩ := (ENNReal.tendsto_atTop_zero.mp hN) 1 zero_lt_one
  have hgfin : weakLpN μ p (g : Ω → 𝕜) < ∞ := by
    have he : (g : Ω → 𝕜) = -(fs N - (g : Ω → 𝕜)) + fs N := by ext x; simp
    rw [he]
    exact (weakLpN_add_le μ p _ _ ((hfs N).sub (Lp.aestronglyMeasurable g)).neg).trans_lt
      (ENNReal.add_lt_top.mpr ⟨by
        rw [weakLpN_neg]
        exact (hNbound N le_rfl).trans_lt ENNReal.one_lt_top,
        hfin N⟩)
  exact ⟨g, memLp_one_iff_integrable.mp (Lp.memLp g), hgfin, hL1, hN⟩

theorem weakLpSubmodule_N_sub (μ : Measure Ω) (p : ℝ)
    (f g : weakLpSubmodule (𝕜 := 𝕜) μ p) :
    weakLpN μ p (⇑((f - g).val)) = weakLpN μ p (⇑f.val - ⇑g.val) := by
  change weakLpN μ p (⇑(f.val - g.val)) = _
  exact weakLpN_congr_ae μ p (AEEqFun.coeFn_sub _ _)

@[simp] theorem weakLpSubmodule_norm_sub (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ)
    (f g : weakLpSubmodule (𝕜 := 𝕜) μ p) :
    ‖f - g‖ = (weakLpN μ p (⇑f.val - ⇑g.val)).toReal :=
  congrArg ENNReal.toReal (weakLpSubmodule_N_sub μ p f g)

/-- Completeness for the normed a.e. quotient, using `weakLp_l1_limit`. -/
theorem weakLp_completeSpace (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ) (hp : 1 < p) :
    CompleteSpace (weakLpSubmodule (𝕜 := 𝕜) μ p) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hR := cauchySeq_iff_tendsto_dist_atTop_0.mp hu
  simp only [dist_eq_norm, weakLpSubmodule_norm_sub] at hR
  have hC : Tendsto (fun nm : ℕ × ℕ => weakLpN μ p (⇑(u nm.1).val - ⇑(u nm.2).val))
      atTop (𝓝 0) := by
    apply (ENNReal.tendsto_toReal_iff (fun nm => ?_) ENNReal.zero_ne_top).mp
    · exact hR
    · rw [← weakLpSubmodule_N_sub]
      exact (u nm.1 - u nm.2).property.ne
  obtain ⟨f, hf, hfin, _, hN⟩ := weakLp_l1_limit μ p hp
    (fun n => (u n).val) (fun n => (u n).val.aestronglyMeasurable)
    (fun n => (u n).property) hC
  let a : Ω →ₘ[μ] 𝕜 := AEEqFun.mk f hf.aestronglyMeasurable
  have ha : a ∈ weakLpSubmodule (𝕜 := 𝕜) μ p := by
    change weakLpN μ p (⇑a) < ∞
    rwa [weakLpN_congr_ae μ p (AEEqFun.coeFn_mk f hf.aestronglyMeasurable)]
  let w : weakLpSubmodule (𝕜 := 𝕜) μ p := ⟨a, ha⟩
  refine ⟨w, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hNR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hN
  simp only [ENNReal.toReal_zero] at hNR
  refine hNR.congr' (Eventually.of_forall fun n => ?_)
  change (weakLpN μ p (⇑(u n).val - f)).toReal = dist (u n) w
  rw [dist_eq_norm, weakLpSubmodule_norm_sub]
  apply congrArg ENNReal.toReal
  exact weakLpN_congr_ae μ p (EventuallyEq.rfl.sub (AEEqFun.coeFn_mk f hf.aestronglyMeasurable)).symm

theorem weakLp_banach : WeakLpBanachSpec.BanachStatement := by
  intro Ω 𝕜 _ _ μ _ p hp
  refine ⟨weakLpSubmodule μ p, (fun _ => Iff.rfl), weakLpNormedAddCommGroup μ p, ?_⟩
  exact ⟨rfl, ⟨weakLpNormedSpace μ p, trivial⟩, (fun _ => rfl), weakLp_completeSpace μ p hp⟩

theorem weakLp_zero_measure : WeakLpBanachSpec.ZeroMeasureStatement := by
  intro Ω 𝕜 _ _
  constructor
  · exact ⟨fun f g => AEEqFun.ext (by simp [Filter.EventuallyEq])⟩
  · intro p hp f
    exact ⟨weakLpN_zero_measure p f, weakLpQ_zero_measure p (by linarith) f⟩

end Scalar

end ExpandedFA.PartIV
