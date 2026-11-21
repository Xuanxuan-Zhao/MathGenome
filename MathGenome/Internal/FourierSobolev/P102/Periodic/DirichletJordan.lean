import MathGenome.Internal.FourierSobolev.P102.Periodic.Dini
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.DirichletJordan
import Mathlib.Topology.Piecewise
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.BoundedVariation

/-! The independent bounded-variation alternative and the complete Theorem 1.6.
The oscillatory estimates below use the second mean value theorem, not Dini
integrability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace P102.Periodic

/-- The removable value at zero is convenient for interval integrals. -/
def sineKernel (w v : ℝ) : ℝ := w * Real.sinc (w * v)

lemma continuous_sineKernel (w : ℝ) : Continuous (sineKernel w) :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

lemma sineKernel_eq (w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0) :
    sineKernel w v = Real.sin (w * v) / v := by
  rw [sineKernel, Real.sinc_of_ne_zero (mul_ne_zero hw hv)]
  field_simp

lemma norm_sineKernel_le (w v : ℝ) : ‖sineKernel w v‖ ≤ |w| := by
  simp only [sineKernel, norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg w)).trans_eq
    (mul_one _)

lemma norm_integral_sin_mul_le (w a b : ℝ) (hw : 0 < w) :
    ‖∫ v in a..b, Real.sin (w * v)‖ ≤ 2 / w := by
  rw [intervalIntegral.integral_comp_mul_left Real.sin hw.ne', integral_sin,
    smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hw, Real.norm_eq_abs]
  have hc : |Real.cos (w * a) - Real.cos (w * b)| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one (w * a), Real.abs_cos_le_one (w * b)])
  calc
    w⁻¹ * |Real.cos (w * a) - Real.cos (w * b)| ≤ w⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hw.le)
    _ = 2 / w := by ring

/-- Cancellation away from zero, with a bound independent of the upper endpoint. -/
lemma norm_integral_sineKernel_tail_le (w a b : ℝ) (hw : 0 < w)
    (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ v in a..b, sineKernel w v‖ ≤ 2 / (a * w) := by
  obtain ⟨c, hc, he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (f := fun v : ℝ => v⁻¹) (g := fun v => Real.sin (w * v)) hab (inv_nonneg.mpr (ha.le.trans hab))
    (fun u hu v hv huv => inv_anti₀ (ha.trans_le hu.1) huv)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable a b)
  have heq : (∫ v in a..b, sineKernel w v) =
      ∫ v in a..b, v⁻¹ * Real.sin (w * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    rw [sineKernel_eq w v hw.ne' (ha.trans_le hv.1).ne']
    ring
  rw [heq, he, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  calc
    a⁻¹ * ‖∫ v in a..c, Real.sin (w * v)‖ ≤ a⁻¹ * (2 / w) :=
      mul_le_mul_of_nonneg_left (norm_integral_sin_mul_le w a c hw) (inv_nonneg.mpr ha.le)
    _ = 2 / (a * w) := by ring

/-- A uniform bound for every positive-frequency sine-integral increment.
The constant is immaterial for convergence; the bound holds also at a = 0. -/
theorem norm_integral_sineKernel_le (w a b : ℝ) (hw : 0 < w)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖∫ v in a..b, sineKernel w v‖ ≤ 3 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (sineKernel w) volume a b :=
    (continuous_sineKernel w).intervalIntegrable
  have hsmall (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ w⁻¹) :
      ‖∫ v in c..d, sineKernel w v‖ ≤ 1 := by
    calc
      _ ≤ |w| * |d - c| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun v _ => norm_sineKernel_le w v)
      _ = w * (d - c) := by rw [abs_of_pos hw, abs_of_nonneg (sub_nonneg.mpr hcd)]
      _ ≤ w * w⁻¹ := mul_le_mul_of_nonneg_left (by linarith) hw.le
      _ = 1 := mul_inv_cancel₀ hw.ne'
  have hlarge (c d : ℝ) (hc : w⁻¹ ≤ c) (hcd : c ≤ d) :
      ‖∫ v in c..d, sineKernel w v‖ ≤ 2 := by
    have hc0 : 0 < c := (inv_pos.mpr hw).trans_le hc
    have hcw : 1 ≤ c * w := by
      calc
        1 = w⁻¹ * w := (inv_mul_cancel₀ hw.ne').symm
        _ ≤ c * w := mul_le_mul_of_nonneg_right hc hw.le
    exact (norm_integral_sineKernel_tail_le w c d hw hc0 hcd).trans
      ((div_le_iff₀ (mul_pos hc0 hw)).mpr (by linarith))
  by_cases hb : b ≤ w⁻¹
  · exact (hsmall a b ha hab hb).trans (by norm_num)
  by_cases ha' : w⁻¹ ≤ a
  · exact (hlarge a b ha' hab).trans (by norm_num)
  have hac : a ≤ w⁻¹ := (lt_of_not_ge ha').le
  have hcb : w⁻¹ ≤ b := (lt_of_not_ge hb).le
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a w⁻¹) (hi w⁻¹ b)]
  exact (norm_add_le _ _).trans (by linarith [hsmall a w⁻¹ ha hac le_rfl, hlarge w⁻¹ b le_rfl hcb])

/-- Monotone weights are controlled by their endpoint and a uniform
sine-integral bound. This is the quantitative core of the Jordan argument. -/
theorem norm_integral_monotone_sineKernel_le
    (p : ℝ → ℝ) (w b : ℝ) (hw : 0 < w) (hb : 0 ≤ b)
    (hp : MonotoneOn p (Icc 0 b)) (hp0 : 0 ≤ p 0) :
    ‖∫ v in 0..b, p v * sineKernel w v‖ ≤ 3 * p b := by
  obtain ⟨c, hc, he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
    (f := p) (g := sineKernel w) hb hp0 hp
    ((continuous_sineKernel w).intervalIntegrable 0 b)
  rw [he, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp0.trans (hp ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb))]
  exact (mul_le_mul_of_nonneg_left (norm_integral_sineKernel_le w c b hw hc.1 hc.2)
    (hp0.trans (hp ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb))).trans_eq (mul_comm _ _)

/-- For a real BV function the small-neighborhood bound depends only on
its variation from the endpoint. In particular it vanishes as the neighborhood
shrinks whenever the function is right-continuous at the endpoint. -/
theorem norm_integral_bv_sineKernel_le (h : ℝ → ℝ) (w b : ℝ)
    (hw : 0 < w) (hb : 0 ≤ b) (hh : BoundedVariationOn h (Icc 0 b)) :
    ‖∫ v in 0..b, (h v - h 0) * sineKernel w v‖ ≤
      3 * variationOnFromTo h (Icc 0 b) 0 b := by
  let V := variationOnFromTo h (Icc 0 b) 0
  let p := fun v => (V v + (h v - h 0)) / 2
  let q := fun v => (V v - (h v - h 0)) / 2
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hp : MonotoneOn p (Icc 0 b) := by
    intro x hx y hy hxy
    have H := variationOnFromTo.add_self_monotoneOn hh.locallyBoundedVariationOn h0 hx hy hxy
    dsimp [p, V]
    simp only [Pi.add_apply] at H
    linarith
  have hq : MonotoneOn q (Icc 0 b) := by
    intro x hx y hy hxy
    have H := variationOnFromTo.sub_self_monotoneOn hh.locallyBoundedVariationOn h0 hx hy hxy
    dsimp [q, V]
    simp only [Pi.sub_apply] at H
    linarith
  have hp0 : p 0 = 0 := by simp [p, V, variationOnFromTo.self]
  have hq0 : q 0 = 0 := by simp [q, V, variationOnFromTo.self]
  have hip : IntervalIntegrable (fun v => p v * sineKernel w v) volume 0 b :=
    ((show MonotoneOn p (uIcc 0 b) by simpa [uIcc_of_le hb] using hp).intervalIntegrable).mul_continuousOn (continuous_sineKernel w).continuousOn
  have hiq : IntervalIntegrable (fun v => q v * sineKernel w v) volume 0 b :=
    ((show MonotoneOn q (uIcc 0 b) by simpa [uIcc_of_le hb] using hq).intervalIntegrable).mul_continuousOn (continuous_sineKernel w).continuousOn
  have heq : (fun v => (h v - h 0) * sineKernel w v) =
      (fun v => p v * sineKernel w v - q v * sineKernel w v) := by
    funext v
    dsimp [p, q]
    ring
  rw [heq, intervalIntegral.integral_sub hip hiq]
  calc
    _ ≤ ‖∫ v in 0..b, p v * sineKernel w v‖ + ‖∫ v in 0..b, q v * sineKernel w v‖ := norm_sub_le _ _
    _ ≤ 3 * p b + 3 * q b := add_le_add
      (norm_integral_monotone_sineKernel_le p w b hw hb hp (by rw [hp0]))
      (norm_integral_monotone_sineKernel_le q w b hw hb hq (by rw [hq0]))
    _ = 3 * variationOnFromTo h (Icc 0 b) 0 b := by dsimp [p, q, V]; ring

/-- Adjoining the prescribed limit at zero preserves BV on every smaller
closed interval. The original representative is untouched at positive points. -/
theorem boundedVariationOn_update_zero {E : Type*} [NormedAddCommGroup E]
    (g : ℝ → E) (a : E) (δ b : ℝ) (_hb : 0 < b) (hbδ : b < δ)
    (hg : BoundedVariationOn g (Ioo 0 δ))
    (ha : Tendsto g (𝓝[>] 0) (𝓝 a)) :
    BoundedVariationOn (Function.update g 0 a) (Icc 0 b) ∧
    ContinuousWithinAt (Function.update g 0 a) (Ici 0) 0 := by
  have hc : ContinuousWithinAt (Function.update g 0 a) (Ici 0) 0 := by
    rw [continuousWithinAt_update_same]
    convert ha using 1
    congr 1
    ext v
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  refine ⟨?_, hc⟩
  have hi : BoundedVariationOn (Function.update g 0 a) (Ioc 0 b) := by
    have heq : EqOn (Function.update g 0 a) g (Ioc 0 b) :=
      fun v hv => Function.update_of_ne hv.1.ne' _ _
    unfold BoundedVariationOn
    rw [eVariationOn.congr heq]
    exact hg.mono (fun v hv => ⟨hv.1, hv.2.trans_lt hbδ⟩)
  unfold BoundedVariationOn at hi ⊢
  rwa [← eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt hc]

/-- Addition preserves bounded variation for normed-group-valued functions. -/
theorem boundedVariationOn_add {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    (hg : BoundedVariationOn g s) : BoundedVariationOn (fun x => f x + g x) s := by
  have hle : eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
    apply iSup_le
    rintro ⟨n, u, hu, hs⟩
    calc
      _ ≤ (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
      _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu hs) (eVariationOn.sum_le hu hs)
  exact ne_top_of_le_ne_top (by finiteness) hle

/-- The removable correction between the trigonometric and singular kernels
is uniformly bounded on the positive half-period. -/
lemma sine_correction_bound (v : ℝ) (hv : 0 < v) (hvπ : v ≤ Real.pi) :
    |(Real.sin (v / 2))⁻¹ - 2 / v| ≤ Real.pi ^ 2 := by
  let s := Real.sin (v / 2)
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])
  have hslow : v ≤ Real.pi * s := by
    have H := Real.mul_le_sin (x := v / 2) (by linarith) (by linarith)
    have : v / Real.pi ≤ s := by convert H using 1; ring
    simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).mp this
  have hdiff : 0 ≤ v - 2 * s := by
    have H := Real.sin_le (show 0 ≤ v / 2 by linarith)
    dsimp [s]
    linarith
  have hbound : v - 2 * s ≤ v ^ 3 := by
    have H := Real.abs_sub_sin_le (v / 2)
    rw [abs_of_pos (by linarith : 0 < v / 2)] at H
    have H' := (le_abs_self (v / 2 - s)).trans H
    nlinarith [pow_pos hv 3]
  have heq : (Real.sin (v / 2))⁻¹ - 2 / v = (v - 2 * s) / (v * s) := by
    change s⁻¹ - 2 / v = _
    field_simp [hs.ne', hv.ne']
  rw [heq, abs_of_nonneg (div_nonneg hdiff (mul_pos hv hs).le)]
  apply (div_le_iff₀ (mul_pos hv hs)).mpr
  have H : v ^ 3 ≤ Real.pi * v * (v * s) := by
    nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hslow)]
  calc
    v - 2 * s ≤ v ^ 3 := hbound
    _ ≤ Real.pi * v * (v * s) := H
    _ ≤ Real.pi ^ 2 * (v * s) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hvπ) (mul_nonneg Real.pi_pos.le (mul_pos hv hs).le)]

/-- Riemann--Lebesgue for real amplitudes and real sine frequencies. -/
lemma integral_sin_mul_tendsto_zero (h : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hh : IntegrableOn h (Icc a b)) :
    Tendsto (fun w : ℝ => ∫ v in a..b, h v * Real.sin (w * v)) atTop (𝓝 0) := by
  have ht := (setIntegral_exp_mul_tendsto_cocompact (Icc a b) measurableSet_Icc
    (fun v => (h v : ℂ))).mono_left atTop_le_cocompact
  have H := Complex.continuous_im.continuousAt.tendsto.comp ht
  simp only [Complex.zero_im] at H
  convert H using 1
  ext w
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hi : IntegrableOn (fun v => (h v : ℂ) * Complex.exp (Complex.I * w * v))
      (Icc a b) := by
    have hreal : IntegrableOn (fun v => (h v : ℂ)) (Icc a b) :=
      Complex.ofRealCLM.integrable_comp hh
    exact hreal.mul_continuousOn (by fun_prop) isCompact_Icc
  change _ = Complex.im (∫ v in Icc a b, (h v : ℂ) * Complex.exp (Complex.I * w * v))
  have he := integral_im hi
  change (∫ v in Icc a b, Complex.im ((h v : ℂ) * Complex.exp (Complex.I * w * v))) =
    Complex.im (∫ v in Icc a b, (h v : ℂ) * Complex.exp (Complex.I * w * v)) at he
  rw [← he]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  simp [Complex.mul_im, Complex.exp_im]

/-- Riemann--Lebesgue in the sine form for complex amplitudes. -/
lemma integral_complex_sin_mul_tendsto_zero (h : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hh : IntegrableOn h (Icc a b)) :
    Tendsto (fun w : ℝ => ∫ v in a..b, h v * (Real.sin (w * v) : ℂ)) atTop (𝓝 0) := by
  have hr := integral_sin_mul_tendsto_zero (fun v => (h v).re) a b hab
    (Complex.reCLM.integrable_comp hh)
  have him := integral_sin_mul_tendsto_zero (fun v => (h v).im) a b hab
    (Complex.imCLM.integrable_comp hh)
  have H := ((Complex.continuous_ofReal.tendsto 0).comp hr).add
    (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
  simp only [Complex.ofReal_zero, zero_mul, zero_add] at H
  apply H.congr'
  apply Eventually.of_forall
  intro w
  have hi : IntervalIntegrable (fun v => h v * (Real.sin (w * v) : ℂ)) volume a b :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hh).mul_continuousOn
      (by fun_prop)
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  have him := Complex.imCLM.intervalIntegral_comp_comm hi
  change (∫ v in a..b, (h v * (Real.sin (w * v) : ℂ)).re) = _ at hre
  change (∫ v in a..b, (h v * (Real.sin (w * v) : ℂ)).im) = _ at him
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hre him
  change (↑(∫ v in a..b, (h v).re * Real.sin (w * v)) : ℂ) +
    ↑(∫ v in a..b, (h v).im * Real.sin (w * v)) * Complex.I = _
  rw [hre, him]
  exact Complex.re_add_im _

/-- The variation at a right-continuous endpoint controls the singular
oscillatory integral, independently of Dini integrability. -/
theorem integral_bv_sineKernel_tendsto_zero (h : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hh : BoundedVariationOn h (Icc 0 b))
    (hc : ContinuousWithinAt h (Ici 0) 0) :
    Tendsto (fun w : ℝ => ∫ v in 0..b, (h v - h 0) * sineKernel w v)
      atTop (𝓝 0) := by
  let V := variationOnFromTo h (Icc 0 b) 0
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv := hh.continuousWithinAt_variationOnFromTo_inter_Ici h0 h0
    (hc.mono inter_subset_right)
  have hv' : Tendsto V (𝓝[>] 0) (𝓝 0) := by
    have he : Icc (0 : ℝ) b ∩ Ici 0 = Icc 0 b := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      tauto
    rw [he, ContinuousWithinAt, variationOnFromTo.self,
      nhdsWithin_Icc_eq_nhdsGE hb] at hv
    exact hv.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), V η < ε / 6 :=
    hv'.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨η, hη, hvη⟩ := (hev.and (Ioo_mem_nhdsGT hb)).exists
  have hη0 : 0 < η := hvη.1
  have hηb : η < b := hvη.2
  have hVeq : variationOnFromTo h (Icc 0 η) 0 η = V η := by
    simp only [V, variationOnFromTo.eq_of_le h _ hη0.le]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨⟨hx0, hxη⟩, _⟩
      exact ⟨⟨hx0, hxη.trans hηb.le⟩, hx0, hxη⟩
    · rintro ⟨_, hx0, hxη⟩
      exact ⟨⟨hx0, hxη⟩, hx0, hxη⟩
  have hi : IntervalIntegrable h volume 0 b := hh.intervalIntegrable (by
    rw [uIcc_of_le hb.le])
  have hitail : IntegrableOn (fun v => (h v - h 0) / v) (Icc η b) := by
    have hh' : IntegrableOn h (Icc η b) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mp hi).mono_set
        (Icc_subset_Icc hη0.le le_rfl)
    have hr : IntegrableOn (fun v => h v - h 0) (Icc η b) :=
      hh'.sub (integrableOn_const (by exact measure_Icc_lt_top.ne))
    simpa only [div_eq_mul_inv, Pi.inv_apply, id_eq] using hr.mul_continuousOn
      (continuous_id.continuousOn.inv₀ (fun v hv => (hη0.trans_le hv.1).ne')) isCompact_Icc
  have ht := integral_sin_mul_tendsto_zero (fun v => (h v - h 0) / v)
    η b hηb.le hitail
  have ht' : Tendsto (fun w : ℝ => ∫ v in η..b, (h v - h 0) * sineKernel w v)
      atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hηb.le] at hv
    dsimp only
    rw [sineKernel_eq w v hw.ne' (hη0.trans_le hv.1).ne']
    ring
  have he := (Metric.tendsto_nhds.mp ht') (ε / 2) (by linarith)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with w hw hw0
  rw [dist_zero_right] at hw ⊢
  have hsmall := norm_integral_bv_sineKernel_le h w η hw0 hη0.le
    (hh.mono (Icc_subset_Icc le_rfl hηb.le))
  rw [hVeq] at hsmall
  have hik : IntervalIntegrable (fun v => (h v - h 0) * sineKernel w v) volume 0 b :=
    (hi.sub intervalIntegrable_const).mul_continuousOn (continuous_sineKernel w).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hik.mono_set (by rw [uIcc_of_le hη0.le, uIcc_of_le hb.le]; exact Icc_subset_Icc le_rfl hηb.le))
    (hik.mono_set (by rw [uIcc_of_le hηb.le, uIcc_of_le hb.le]; exact Icc_subset_Icc hη0.le le_rfl))]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Complex BV amplitudes are handled through their two real components. -/
theorem integral_complex_bv_sineKernel_tendsto_zero (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b)
    (hh : BoundedVariationOn h (Icc 0 b))
    (hc : ContinuousWithinAt h (Ici 0) 0) :
    Tendsto (fun w : ℝ => ∫ v in 0..b, (h v - h 0) * (sineKernel w v : ℂ))
      atTop (𝓝 0) := by
  have hr := integral_bv_sineKernel_tendsto_zero (fun v => (h v).re) b hb
    (Complex.reCLM.lipschitzWith.comp_boundedVariationOn hh)
    (Complex.continuous_re.continuousAt.comp_continuousWithinAt hc)
  have him := integral_bv_sineKernel_tendsto_zero (fun v => (h v).im) b hb
    (Complex.imCLM.lipschitzWith.comp_boundedVariationOn hh)
    (Complex.continuous_im.continuousAt.comp_continuousWithinAt hc)
  have H := ((Complex.continuous_ofReal.tendsto 0).comp hr).add
    (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
  simp only [Complex.ofReal_zero, zero_mul, zero_add] at H
  apply H.congr'
  apply Eventually.of_forall
  intro w
  have hi : IntervalIntegrable (fun v => (h v - h 0) * (sineKernel w v : ℂ)) volume 0 b :=
    ((hh.intervalIntegrable (by rw [uIcc_of_le hb.le])).sub intervalIntegrable_const).mul_continuousOn
      (Complex.continuous_ofReal.comp (continuous_sineKernel w)).continuousOn
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  have him := Complex.imCLM.intervalIntegral_comp_comm hi
  change (∫ v in 0..b, ((h v - h 0) * (sineKernel w v : ℂ)).re) = _ at hre
  change (∫ v in 0..b, ((h v - h 0) * (sineKernel w v : ℂ)).im) = _ at him
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add] at hre him
  change (↑(∫ v in 0..b, ((h v).re - (h 0).re) * sineKernel w v) : ℂ) +
    ↑(∫ v in 0..b, ((h v).im - (h 0).im) * sineKernel w v) * Complex.I = _
  rw [hre, him]
  exact Complex.re_add_im _

/-- The bounded correction is integrable against every L¹ amplitude. -/
lemma integrable_sine_correction (h : ℝ → ℂ) (b : ℝ) (_hb : 0 < b) (hbπ : b ≤ Real.pi)
    (hh : IntegrableOn h (Icc 0 b)) :
    IntegrableOn (fun v => h v * (((Real.sin (v / 2))⁻¹ - 2 / v : ℝ) : ℂ)) (Icc 0 b) := by
  apply (integrableOn_Icc_iff_integrableOn_Ioo (by finiteness) (by finiteness)).mpr
  have hi : IntegrableOn h (Ioo 0 b) := hh.mono_set Ioo_subset_Icc_self
  apply hi.mul_bdd
  · exact (Complex.continuous_ofReal.measurable.comp
      (((Real.measurable_sin.comp (measurable_id.div_const 2)).inv).sub
        (measurable_const.div measurable_id))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      sine_correction_bound v hv.1 (hv.2.le.trans hbπ)

/-- Reduction on a small half-interval from the Dirichlet kernel to sin(wv)/v.
All amplitudes are only assumed integrable; no Dini test is introduced. -/
lemma integral_local_dirichlet_tendsto_zero (h : ℝ → ℂ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ Real.pi) (hh : IntegrableOn h (Icc 0 b))
    (hz : Tendsto (fun w : ℝ => ∫ v in 0..b, h v * (sineKernel w v : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ v in 0..b,
      h v * dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))) atTop (𝓝 0) := by
  let c := fun v : ℝ => ((Real.sin (v / 2))⁻¹ - 2 / v : ℝ)
  have hcorr := integrable_sine_correction h b hb hbπ hh
  have Hc := integral_complex_sin_mul_tendsto_zero (fun v => h v * (c v : ℂ)) 0 b hb.le hcorr
  have hfreq : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have H := ((hz.const_mul 2).add Hc).comp hfreq
  simp only [mul_zero, zero_add] at H
  apply H.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_def]
  have hik : IntervalIntegrable (fun v => h v * (sineKernel ((N : ℝ) + 1 / 2) v : ℂ)) volume 0 b :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mpr hh).mul_continuousOn
      (Complex.continuous_ofReal.comp (continuous_sineKernel _)).continuousOn
  have hic : IntervalIntegrable (fun v => h v * (c v : ℂ) *
      (Real.sin (((N : ℝ) + 1 / 2) * v) : ℂ)) volume 0 b :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mpr hcorr).mul_continuousOn (by fun_prop)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hik.const_mul 2) hic]
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all
  intro v hv
  rw [uIoc_of_le hb.le] at hv
  have hvπ : v ≤ Real.pi := hv.2.trans hbπ
  rw [dirichletKernel_sine_quotient N v (by linarith [Real.pi_pos, hv.1]) hvπ hv.1.ne',
    sineKernel_eq _ v (by positivity) hv.1.ne']
  dsimp only [c]
  push_cast
  ring

/-- The contribution on the rest of the half-period vanishes by
Riemann--Lebesgue, and may be added to the local Jordan limit. -/
lemma integral_half_dirichlet_tendsto_zero (h : ℝ → ℂ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ Real.pi) (hh : IntegrableOn h (Icc 0 Real.pi))
    (hz : Tendsto (fun w : ℝ => ∫ v in 0..b, h v * (sineKernel w v : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ v in 0..Real.pi,
      h v * dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))) atTop (𝓝 0) := by
  have hlocal := integral_local_dirichlet_tendsto_zero h b hb hbπ
    (hh.mono_set (Icc_subset_Icc le_rfl hbπ)) hz
  have ht : IntegrableOn (fun v => h v * ((Real.sin (v / 2))⁻¹ : ℂ)) (Icc b Real.pi) := by
    apply (hh.mono_set (Icc_subset_Icc hb.le le_rfl)).mul_continuousOn _ isCompact_Icc
    apply ((Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_id.div_const 2))).continuousOn).inv₀
    intro v hv
    change (Real.sin (v / 2) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr ((Real.sin_pos_of_pos_of_lt_pi (by linarith [hv.1])
      (by linarith [hv.2, Real.pi_pos])).ne')
  have hfreq : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have htail := (integral_complex_sin_mul_tendsto_zero
    (fun v => h v * ((Real.sin (v / 2))⁻¹ : ℂ)) b Real.pi hbπ ht).comp hfreq
  have htail' : Tendsto (fun N : ℕ => ∫ v in b..Real.pi,
      h v * dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))) atTop (𝓝 0) := by
    apply htail.congr'
    apply Eventually.of_forall
    intro N
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hbπ] at hv
    dsimp only
    rw [dirichletKernel_sine_quotient N v (by linarith [hv.1]) hv.2
      (hb.trans_le hv.1).ne']
    push_cast
    ring
  have H := hlocal.add htail'
  simp only [zero_add] at H
  apply H.congr'
  apply Eventually.of_forall
  intro N
  have hi : IntervalIntegrable (fun v => h v *
      dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))) volume 0 Real.pi :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hh).mul_continuousOn
      ((continuous_dirichletKernel _ N).comp continuous_quotient_mk').continuousOn
  exact intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set (by rw [uIcc_of_le hb.le, uIcc_of_le Real.pi_pos.le]; exact Icc_subset_Icc le_rfl hbπ))
    (hi.mono_set (by rw [uIcc_of_le hbπ, uIcc_of_le Real.pi_pos.le]; exact Icc_subset_Icc hb.le le_rfl))

/-- Probability Haar normalization for an even integrable function. -/
lemma integral_even_circle (h : Circle (2 * Real.pi) → ℂ)
    (hh : Integrable h (haar (2 * Real.pi))) (he : ∀ y, h (-y) = h y) :
    (∫ y, h y ∂haar (2 * Real.pi)) =
      (Real.pi⁻¹ : ℝ) • ∫ v in 0..Real.pi, h (v : Circle (2 * Real.pi)) := by
  have hf : IntervalIntegrable (fun v : ℝ => h (v : Circle (2 * Real.pi)))
      volume (-Real.pi) Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr
    convert integrableOn_circle_interval (2 * Real.pi) h hh (-Real.pi) using 1
    congr 1
    ring
  have hm : (∫ v in -Real.pi..0, h (v : Circle (2 * Real.pi))) =
      ∫ v in 0..Real.pi, h (v : Circle (2 * Real.pi)) := by
    have H := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi)
      (fun v : ℝ => h (v : Circle (2 * Real.pi)))
    simpa only [AddCircle.coe_neg, he, neg_zero] using H.symm
  rw [haar_integral_interval]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hf.mono_set (by rw [uIcc_of_le (by linarith [Real.pi_pos]),
      uIcc_of_le (by linarith [Real.pi_pos])]; exact Icc_subset_Icc le_rfl Real.pi_pos.le))
    (hf.mono_set (by rw [uIcc_of_le Real.pi_pos.le,
      uIcc_of_le (by linarith [Real.pi_pos])]; exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)), hm]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp
  ring

open Expected.Dini (offset residual)

/-- A local oscillatory limit for the symmetric residual suffices for ordinary
Fourier convergence. The coefficient normalization is probability Haar. -/
theorem partialSum_tendsto_of_local_sineKernel
    (f : Circle (2 * Real.pi) → ℂ) (hf : Integrable f (haar (2 * Real.pi)))
    (x : Circle (2 * Real.pi)) (L : ℂ) (b : ℝ) (hb : 0 < b) (hbπ : b ≤ Real.pi)
    (hz : Tendsto (fun w : ℝ => ∫ v in 0..b,
      residual (2 * Real.pi) f x L v * (sineKernel w v : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => partialSum (2 * Real.pi) N f x) atTop (𝓝 L) := by
  let P := 2 * Real.pi
  let R : Circle P → ℂ := fun y => f (x + y) + f (x - y) - 2 * L
  have hR : Integrable R (haar P) :=
    ((hf.comp_add_left x).add (hf.comp_sub_left x)).sub (integrable_const _)
  have hReven : ∀ y, R (-y) = R y := by
    intro y
    dsimp [R]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  have hiR : IntegrableOn (fun v : ℝ => R (v : Circle P)) (Icc 0 Real.pi) := by
    have H := integrableOn_circle_interval P R hR 0
    simp only [zero_add] at H
    exact H.mono_set (Icc_subset_Icc le_rfl (by dsimp [P]; linarith [Real.pi_pos]))
  have hzero : Tendsto (fun N : ℕ => ∫ v in 0..Real.pi,
      R (v : Circle P) * dirichletKernel P N (v : Circle P)) atTop (𝓝 0) := by
    apply integral_half_dirichlet_tendsto_zero _ b hb hbπ hiR
    simpa only [Expected.Dini.residual, offset_angular, R, P] using hz
  have hprod (N : ℕ) : Integrable (fun y => R y * dirichletKernel P N y) (haar P) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_dirichletKernel P N).continuousOn
    exact hR.mul_bdd (continuous_dirichletKernel P N).aestronglyMeasurable
      (ae_of_all _ (fun y => hC y (mem_univ _)))
  have hcircle : Tendsto (fun N : ℕ => ∫ y, R y * dirichletKernel P N y ∂haar P)
      atTop (𝓝 0) := by
    have H := hzero.const_smul (Real.pi⁻¹ : ℝ)
    simp only [smul_zero] at H
    apply H.congr'
    exact Eventually.of_forall (fun N => (integral_even_circle _ (hprod N)
      (fun y => by rw [hReven, dirichletKernel_neg])).symm)
  have hidentity (N : ℕ) :
      (∫ y, R y * dirichletKernel P N y ∂haar P) = 2 * (partialSum P N f x - L) := by
    let K := dirichletKernel P N
    have hm : Integrable (fun y => f (x - y) * K y) (haar P) :=
      dirichlet_convolution_exists P f hf N x
    have hp : Integrable (fun y => f (x + y) * K y) (haar P) := by
      simpa only [K, sub_neg_eq_add, dirichletKernel_neg] using hm.comp_neg
    have hk : Integrable K (haar P) :=
      (continuous_dirichletKernel P N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hreflect : (∫ y, f (x + y) * K y ∂haar P) = ∫ y, f (x - y) * K y ∂haar P := by
      simpa only [K, sub_neg_eq_add, dirichletKernel_neg] using
        integral_neg_eq_self (fun y => f (x - y) * K y) (haar P)
    change (∫ y, (f (x + y) + f (x - y) - 2 * L) * K y ∂haar P) = _
    simp_rw [sub_mul, add_mul]
    have hs : Integrable (fun y => f (x + y) * K y + f (x - y) * K y) (haar P) := hp.add hm
    rw [integral_sub hs (hk.const_mul (2 * L)), integral_add hp hm,
      hreflect, integral_const_mul, integral_dirichletKernel, mul_one]
    have hconv := partialSum_eq_convolution P f hf N x
    change partialSum P N f x = (∫ y, f (x - y) * K y ∂haar P) at hconv
    rw [← hconv]
    ring
  have H := hcircle.const_mul (1 / 2 : ℂ)
  simp only [mul_zero] at H
  have Hd : Tendsto (fun N : ℕ => partialSum P N f x - L) atTop (𝓝 0) := by
    apply H.congr'
    exact Eventually.of_forall (fun N => by dsimp only; rw [hidentity]; ring)
  simpa only [sub_add_cancel, zero_add] using Hd.add_const L

open Expected.DirichletJordan (BVSide ComponentBVSide)

/-- A.e. representative freedom is preserved by the local oscillatory limit. -/
theorem bvSide_sineKernel_tendsto_zero (φ : ℝ → ℂ) (a : ℂ) (δ b : ℝ)
    (hb : 0 < b) (hbδ : b < δ) (hφ : BVSide φ a δ) :
    Tendsto (fun w : ℝ => ∫ v in 0..b, (φ v - a) * (sineKernel w v : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨g, hg, hφg, ha⟩ := hφ
  obtain ⟨hg', hc⟩ := boundedVariationOn_update_zero g a δ b hb hbδ hg ha
  have H := integral_complex_bv_sineKernel_tendsto_zero (Function.update g 0 a) b hb hg' hc
  simp only [Function.update_self] at H
  apply H.congr'
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_of_le hb.le]
  apply integral_congr_ae
  have hφg' : φ =ᵐ[volume.restrict (Ioc 0 b)] g :=
    ae_restrict_of_ae_restrict_of_subset
      (show Ioc 0 b ⊆ Ioo 0 δ from fun v hv => ⟨hv.1, hv.2.trans_lt hbδ⟩) hφg
  filter_upwards [hφg', ae_restrict_mem measurableSet_Ioc] with v hv hv'
  simp [hv, Function.update_of_ne hv'.1.ne']

/-- Independently chosen real and imaginary BV representatives combine into
a complex BV representative. No equality at exceptional points is required. -/
theorem bvSide_of_components (φ : ℝ → ℂ) (a : ℂ) (δ : ℝ)
    (h : ComponentBVSide φ a δ) : BVSide φ a δ := by
  obtain ⟨u, v, hu, hv, hreu, himv, hlu, hlv⟩ := h
  let g := fun t => (u t : ℂ) + (v t : ℂ) * Complex.I
  have hu' : BoundedVariationOn (fun t => (u t : ℂ)) (Ioo 0 δ) :=
    Complex.isometry_ofReal.lipschitzWith.comp_boundedVariationOn hu
  have hv' : BoundedVariationOn (fun t => (v t : ℂ) * Complex.I) (Ioo 0 δ) := by
    have hi : LipschitzWith 1 (fun r : ℝ => (r : ℂ) * Complex.I) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub]
    exact hi.comp_boundedVariationOn hv
  refine ⟨g, boundedVariationOn_add hu' hv', ?_, ?_⟩
  · filter_upwards [hreu, himv] with t htu htv
    change φ t = (u t : ℂ) + (v t : ℂ) * Complex.I
    rw [← htu, ← htv]
    exact (Complex.re_add_im (φ t)).symm
  · have H := ((Complex.continuous_ofReal.tendsto a.re).comp hlu).add
      (((Complex.continuous_ofReal.tendsto a.im).comp hlv).mul_const Complex.I)
    simpa only [g, Function.comp_apply, Complex.re_add_im] using H

/-- Addition also respects independent a.e. BV representatives. -/
lemma bvSide_add {φ ψ : ℝ → ℂ} {a b : ℂ} {δ : ℝ}
    (hφ : BVSide φ a δ) (hψ : BVSide ψ b δ) :
    BVSide (fun v => φ v + ψ v) (a + b) δ := by
  obtain ⟨g, hg, hφg, ha⟩ := hφ
  obtain ⟨k, hk, hψk, hb⟩ := hψ
  refine ⟨fun v => g v + k v, boundedVariationOn_add hg hk, ?_, ha.add hb⟩
  exact hφg.add hψk

/-- The independent local BV alternative, in angular coordinates. -/
theorem dirichlet_jordan_angular
    (f : Circle (2 * Real.pi) → ℂ) (hf : Integrable f (haar (2 * Real.pi)))
    (x : Circle (2 * Real.pi)) (aPlus aMinus : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hp : BVSide (fun v => f (x + offset (2 * Real.pi) v)) aPlus δ)
    (hm : BVSide (fun v => f (x - offset (2 * Real.pi) v)) aMinus δ) :
    Tendsto (fun N : ℕ => partialSum (2 * Real.pi) N f x) atTop (𝓝 ((aPlus + aMinus) / 2)) := by
  let b := min δ Real.pi / 2
  have hb : 0 < b := div_pos (lt_min hδ Real.pi_pos) (by norm_num)
  have hbδ : b < δ := by dsimp [b]; linarith [min_le_left δ Real.pi]
  have hbπ : b ≤ Real.pi := by dsimp [b]; linarith [min_le_right δ Real.pi, Real.pi_pos]
  apply partialSum_tendsto_of_local_sineKernel f hf x ((aPlus + aMinus) / 2) b hb hbπ
  have H := bvSide_sineKernel_tendsto_zero _ (aPlus + aMinus) δ b hb hbδ (bvSide_add hp hm)
  convert H using 1
  ext w
  apply intervalIntegral.integral_congr
  intro v hv
  unfold Expected.Dini.residual
  ring

/-- Dirichlet--Jordan for every positive period, retaining local a.e.
representatives and their prescribed one-sided limits. -/
theorem dirichlet_jordan (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ)
    (hf : Integrable f (haar T)) (x : Circle T) (aPlus aMinus : ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hp : BVSide (fun v => f (x + offset T v)) aPlus δ)
    (hm : BVSide (fun v => f (x - offset T v)) aMinus δ) :
    Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 ((aPlus + aMinus) / 2)) := by
  let R := rescale (2 * Real.pi) T
  let F : Circle (2 * Real.pi) → ℂ := fun y => f (R y)
  let X := R.symm x
  have hF : Integrable F (haar (2 * Real.pi)) :=
    (rescale_measure (2 * Real.pi) T).integrable_comp_of_integrable hf
  have hoff (v : ℝ) : R (offset (2 * Real.pi) v) = offset T v := by
    rw [offset_angular]
    exact rescale_formula (2 * Real.pi) T v
  have hpF : BVSide (fun v => F (X + offset (2 * Real.pi) v)) aPlus δ := by
    simpa only [F, map_add, X, AddEquiv.apply_symm_apply, hoff] using hp
  have hmF : BVSide (fun v => F (X - offset (2 * Real.pi) v)) aMinus δ := by
    simpa only [F, map_sub, X, AddEquiv.apply_symm_apply, hoff] using hm
  have H := dirichlet_jordan_angular F hF X aPlus aMinus δ hδ hpF hmF
  simpa only [F, R, rescale_partialSum, X, AddEquiv.apply_symm_apply] using H

/-- The same local theorem for independently chosen BV representatives of
the two real components. -/
theorem dirichlet_jordan_components : Expected.DirichletJordan.componentsStatement := by
  intro T hT f hf x ap am δ hδ hp hm
  exact dirichlet_jordan T f hf x ap am δ hδ
    (bvSide_of_components _ _ _ hp) (bvSide_of_components _ _ _ hm)

/-- Canonical L¹-class version of the local BV theorem. -/
theorem dirichlet_jordanL1 : Expected.DirichletJordan.jordanL1Statement := by
  intro T hT f x ap am δ hδ hp hm
  exact dirichlet_jordan T f (MeasureTheory.L1.integrable_coeFn f) x ap am δ hδ hp hm

/-- The complete source theorem: symmetric Dini and local BV are separate
sufficient alternatives for the same ordinary symmetric partial sums. -/
theorem dirichlet_jordan_alternatives : Expected.DirichletJordan.alternativesStatement := by
  intro T hT f hf x L h
  rcases h with ⟨δ, hδ, hd⟩ | ⟨ap, am, δ, hδ, hp, hm, hL⟩
  · exact dini_symmetric T f hf x L δ hδ hd
  · subst L
    exact dirichlet_jordan T f hf x ap am δ hδ hp hm

/-- The symmetric Dini alternative retains possible cancellation between
the two sides and assumes no one-sided limits. -/
theorem dirichlet_jordan_symmetric_dini : Expected.DirichletJordan.symmetricDiniStatement :=
  dini_symmetric

/-- The source's one-sided Dini corollary, retained in the complete theorem. -/
theorem dirichlet_jordan_separate_dini : Expected.DirichletJordan.separateDiniStatement :=
  dini_separate

/-- Under symmetric Dini integrability, any existing one-sided limits have
the stated midpoint. This assertion does not need the BV alternative. -/
theorem dirichlet_jordan_midpoint : Expected.DirichletJordan.midpointStatement :=
  dini_midpoint

end P102.Periodic
