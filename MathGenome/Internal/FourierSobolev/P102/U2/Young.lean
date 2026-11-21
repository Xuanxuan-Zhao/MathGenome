import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.Young

/-! Young's inequality in Euclidean space and on a circle, including all
infinite endpoints and completed measures. For finite r we apply weighted
three-factor Hölder and Tonelli to the absolute integrand. Zero weights require
no division by function norms. The r=∞ case is ordinary Hölder. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace P102.U2.Young

/-- Three-factor Hölder, with weights allowed to vanish. -/
theorem lintegral_three_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B C : α → ℝ≥0∞} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hC : AEMeasurable C μ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) :
    (∫⁻ x, A x ^ a * B x ^ b * C x ^ c ∂μ) ≤
      (∫⁻ x, A x ∂μ) ^ a * (∫⁻ x, B x ∂μ) ^ b * (∫⁻ x, C x ∂μ) ^ c := by
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
    (f := ![A, B, C]) (p := ![a, b, c])
    (by intro i _; fin_cases i <;> simp [hA, hB, hC])
    (by simpa [Fin.sum_univ_succ, add_assoc] using hs)
    (by intro i _; fin_cases i <;> simp [ha, hb, hc])
  simpa [Fin.prod_univ_succ, mul_assoc] using h

/-- The pointwise Hölder estimate used in the finite-exponent proof of Young. -/
theorem lintegral_mul_le_mixed_powers {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 + 1 / r = 1 / p + 1 / q) :
    (∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ p * g x ^ q ∂μ) ^ (1 / r) *
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p - 1 / r) *
      (∫⁻ x, g x ^ q ∂μ) ^ (1 / q - 1 / r) := by
  have ha : 0 ≤ 1 / r := by positivity
  have hb : 0 ≤ 1 / p - 1 / r := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpr)
  have hc : 0 ≤ 1 / q - 1 / r := sub_nonneg.mpr (one_div_le_one_div_of_le hq hqr)
  have h := lintegral_three_rpow_le ((hf.pow_const p).mul (hg.pow_const q))
    (hf.pow_const p) (hg.pow_const q) ha hb hc (by linarith)
  convert h using 1
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha]
  simp only [← ENNReal.rpow_mul]
  have he1 : p * (1 / r) + p * (1 / p - 1 / r) = 1 := by field_simp; ring
  have he2 : q * (1 / r) + q * (1 / q - 1 / r) = 1 := by field_simp; ring
  calc
    f x * g x = f x ^ (p * (1 / r) + p * (1 / p - 1 / r)) *
        g x ^ (q * (1 / r) + q * (1 / q - 1 / r)) := by rw [he1, he2]; simp
    _ = _ := by
      rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp.le ha) (mul_nonneg hp.le hb),
        ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hq.le ha) (mul_nonneg hq.le hc)]
      ac_rfl

/-- Convolution in the order fixed by the manuscript. -/
def integralConvolution {G 𝕜 : Type*} [Sub G] [MeasurableSpace G] [RCLike 𝕜]
    (μ : Measure G) (f g : G → 𝕜) (x : G) : 𝕜 := ∫ y, f (x - y) * g y ∂μ

lemma integralConvolution_eq_library {G 𝕜 : Type*} [Sub G] [MeasurableSpace G] [RCLike 𝕜]
    (μ : Measure G) (f g : G → 𝕜) :
    integralConvolution μ f g = MeasureTheory.convolution g f (ContinuousLinearMap.mul ℝ 𝕜) μ := by
  funext x
  simp only [integralConvolution, MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply', mul_comm]


lemma exponent_le_output {p q r : ℝ≥0∞} (hq : 1 ≤ q)
    (hs : 1 + r⁻¹ = p⁻¹ + q⁻¹) : p ≤ r := by
  apply ENNReal.inv_le_inv.mp
  apply (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp
  calc
    1 + r⁻¹ = p⁻¹ + q⁻¹ := hs
    _ ≤ p⁻¹ + 1 := add_le_add_right (ENNReal.inv_le_one.mpr hq) _
    _ = 1 + p⁻¹ := add_comm _ _

lemma exponent_relation_real {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : 1 + r⁻¹ = p⁻¹ + q⁻¹) :
    1 + 1 / r.toReal = 1 / p.toReal + 1 / q.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have h := congrArg ENNReal.toReal hs
  simpa only [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.inv_ne_top.mpr hr0),
    ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
    ENNReal.toReal_one, ENNReal.toReal_inv, one_div] using h

section Group
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G]
  (μ : Measure G) [SFinite μ] [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

omit [IsAddLeftInvariant μ] [IsNegInvariant μ] in
/-- Tonelli and translation invariance evaluate the mixed power integral exactly. -/
theorem lintegral_mixed_powers {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (p q : ℝ) :
    (∫⁻ x, ∫⁻ y, f (x - y) ^ p * g y ^ q ∂μ ∂μ) =
      (∫⁻ x, f x ^ p ∂μ) * (∫⁻ y, g y ^ q ∂μ) := by
  have hm : AEMeasurable (fun z : G × G => f (z.1 - z.2) ^ p * g z.2 ^ q) (μ.prod μ) :=
    ((hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant μ μ)).pow_const p).mul
      (hg.comp_snd.pow_const q)
  rw [lintegral_lintegral_swap hm]
  have hi (y : G) : (∫⁻ x, f (x - y) ^ p * g y ^ q ∂μ) =
      (∫⁻ x, f x ^ p ∂μ) * g y ^ q := by
    have hm' : AEMeasurable (fun x => f (x - y) ^ p) μ :=
      (hf.comp_quasiMeasurePreserving (measurePreserving_sub_right μ y).quasiMeasurePreserving).pow_const p
    rw [lintegral_mul_const'' _ hm']
    rw [lintegral_sub_right_eq_self (fun x => f x ^ p) y]
  simp_rw [hi]
  exact lintegral_const_mul'' _ (hg.pow_const q)

/-- Young's inequality for the nonnegative absolute integral, at finite exponents. -/
theorem lintegral_convolution_rpow_le {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 + 1 / r = 1 / p + 1 / q) :
    (∫⁻ x, (∫⁻ y, f (x - y) * g y ∂μ) ^ r ∂μ) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (r / p) * (∫⁻ y, g y ^ q ∂μ) ^ (r / q) := by
  let A := ∫⁻ x, f x ^ p ∂μ
  let B := ∫⁻ y, g y ^ q ∂μ
  let C := fun x => ∫⁻ y, f (x - y) ^ p * g y ^ q ∂μ
  have ha : 0 ≤ 1 / r := by positivity
  have hb : 0 ≤ 1 / p - 1 / r := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpr)
  have hc : 0 ≤ 1 / q - 1 / r := sub_nonneg.mpr (one_div_le_one_div_of_le hq hqr)
  have hb' : 0 ≤ (1 / p - 1 / r) * r := mul_nonneg hb hr.le
  have hc' : 0 ≤ (1 / q - 1 / r) * r := mul_nonneg hc hr.le
  have hC : AEMeasurable C μ := by
    exact (((hf.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ)).pow_const p).mul
      (hg.comp_snd.pow_const q)).lintegral_prod_right'
  calc
    _ ≤ ∫⁻ x, (C x ^ (1 / r) * A ^ (1 / p - 1 / r) * B ^ (1 / q - 1 / r)) ^ r ∂μ := by
      apply lintegral_mono
      intro x
      apply ENNReal.rpow_le_rpow _ hr.le
      have h := lintegral_mul_le_mixed_powers
        (f := fun y => f (x - y)) (hf.comp_quasiMeasurePreserving (μ.measurePreserving_sub_left x).quasiMeasurePreserving) hg hp hq hr hpr hqr hs
      simpa only [lintegral_sub_left_eq_self (fun y => f y ^ p) x] using h
    _ = (∫⁻ x, C x ∂μ) * A ^ ((1 / p - 1 / r) * r) * B ^ ((1 / q - 1 / r) * r) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
        one_div_mul_cancel hr.ne', ENNReal.rpow_one]
      rw [lintegral_mul_const'' _ (hC.mul_const _), lintegral_mul_const'' _ hC]
    _ = (A * B) * A ^ ((1 / p - 1 / r) * r) * B ^ ((1 / q - 1 / r) * r) := by
      rw [lintegral_mixed_powers μ hf hg p q]
    _ = A ^ (r / p) * B ^ (r / q) := by
      have hp' : r / p = 1 + (1 / p - 1 / r) * r := by field_simp; ring
      have hq' : r / q = 1 + (1 / q - 1 / r) * r := by field_simp; ring
      rw [hp', hq', ENNReal.rpow_add_of_nonneg _ _ zero_le_one hb',
        ENNReal.rpow_add_of_nonneg _ _ zero_le_one hc', ENNReal.rpow_one, ENNReal.rpow_one]
      ac_rfl

variable {𝕜 : Type*} [RCLike 𝕜]


omit [IsAddLeftInvariant μ] [IsNegInvariant μ] in
lemma integralConvolution_measurable {f g : G → 𝕜}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (integralConvolution μ f g) μ := by
  rw [integralConvolution_eq_library]
  exact hg.convolution (ContinuousLinearMap.mul ℝ 𝕜) hf

omit [IsAddLeftInvariant μ] [IsNegInvariant μ] in
lemma integralConvolution_congr {f f' g g' : G → 𝕜}
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    integralConvolution μ f g = integralConvolution μ f' g' := by
  rw [integralConvolution_eq_library, integralConvolution_eq_library]
  exact MeasureTheory.convolution_congr (ContinuousLinearMap.mul ℝ 𝕜) hg hf

/-- Finite-exponent Young, including vanishing norms and p=1 or q=1. -/
theorem young_finite {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : 1 + r⁻¹ = p⁻¹ + q⁻¹) (hrtop : r ≠ ∞)
    {f g : G → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    (∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ) ∧
    MemLp (integralConvolution μ f g) r μ ∧
    eLpNorm (integralConvolution μ f g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have hpr : p ≤ r := exponent_le_output hq hs
  have hqr : q ≤ r := exponent_le_output hp (by simpa [add_comm] using hs)
  have hptop : p ≠ ∞ := ne_top_of_le_ne_top hrtop hpr
  have hqtop : q ≠ ∞ := ne_top_of_le_ne_top hrtop hqr
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have hpR := ENNReal.toReal_pos hp0 hptop
  have hqR := ENNReal.toReal_pos hq0 hqtop
  have hrR := ENNReal.toReal_pos hr0 hrtop
  have hsr := exponent_relation_real hp hq hr hs
  have hm := integralConvolution_measurable μ hf.aestronglyMeasurable hg.aestronglyMeasurable
  let H : G → ℝ≥0∞ := fun x => ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ
  have hF := hf.aestronglyMeasurable.enorm
  have hG := hg.aestronglyMeasurable.enorm
  have hH : AEMeasurable H μ := by
    exact ((hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul
      hG.comp_snd).lintegral_prod_right'
  have hbound := lintegral_convolution_rpow_le μ hF hG hpR hqR hrR
    (ENNReal.toReal_mono hrtop hpr) (ENNReal.toReal_mono hrtop hqr) hsr
  have hAf := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hf
  have hBg := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hqtop hg
  have hfinite : (∫⁻ x, H x ^ r.toReal ∂μ) < ∞ := hbound.trans_lt (by
    apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hAf.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hBg.ne)
  have hexists : ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by
    filter_upwards [ae_lt_top' (hH.pow_const r.toReal) hfinite.ne] with x hx
    refine ⟨?_, ?_⟩
    · exact (hf.aestronglyMeasurable.comp_measurePreserving
        (μ.measurePreserving_sub_left x)).mul hg.aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_enorm]
      simpa only [enorm_mul] using (ENNReal.rpow_lt_top_iff_of_pos hrR).mp hx
  have hnorm : eLpNorm (integralConvolution μ f g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop hm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hg.aestronglyMeasurable]
    calc
      _ ≤ (∫⁻ x, H x ^ r.toReal ∂μ) ^ (1 / r.toReal) := by
        apply ENNReal.rpow_le_rpow _ (by positivity)
        apply lintegral_mono
        intro x
        apply ENNReal.rpow_le_rpow _ hrR.le
        simpa only [integralConvolution, enorm_mul] using
          (enorm_integral_le_lintegral_enorm (fun y => f (x - y) * g y) (μ := μ))
      _ ≤ ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (r.toReal / p.toReal) *
          (∫⁻ y, ‖g y‖ₑ ^ q.toReal ∂μ) ^ (r.toReal / q.toReal)) ^ (1 / r.toReal) :=
        ENNReal.rpow_le_rpow hbound (by positivity)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1 <;> congr 1 <;> field_simp
  exact ⟨hexists, hnorm.trans_lt (ENNReal.mul_lt_top hf hg), hnorm⟩

/-- The infinite output exponent, including (1,∞) and (∞,1). -/
theorem young_infty {p q : ℝ≥0∞} (hs : 1 = p⁻¹ + q⁻¹)
    {f g : G → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    (∀ x, Integrable (fun y => f (x - y) * g y) μ) ∧
    MemLp (integralConvolution μ f g) ∞ μ ∧
    eLpNorm (integralConvolution μ f g) ∞ μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have : p.HolderConjugate q := ⟨by simpa using hs.symm⟩
  have hm := integralConvolution_measurable μ hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hexists : ∀ x, Integrable (fun y => f (x - y) * g y) μ := by
    intro x
    exact memLp_one_iff_integrable.mp
      ((hf.comp_measurePreserving (μ.measurePreserving_sub_left x)).mul hg)
  have hnorm : eLpNorm (integralConvolution μ f g) ∞ μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
    rw [eLpNorm_exponent_top hm]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    apply Filter.Eventually.of_forall
    intro x
    rw [integralConvolution_eq_library]
    have h := MeasureTheory.enorm_convolution_le (p := q) (q := p) (ContinuousLinearMap.mul ℝ 𝕜)
      hg.aestronglyMeasurable hf.aestronglyMeasurable x
    simpa only [ContinuousLinearMap.opENorm_mul, one_mul, mul_one, mul_comm] using h
  exact ⟨hexists, hnorm.trans_lt (ENNReal.mul_lt_top hf hg), hnorm⟩

/-- Young on an invariant additive group. All norms and representatives are allowed. -/
theorem young {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : 1 + r⁻¹ = p⁻¹ + q⁻¹) {f g : G → 𝕜}
    (hf : MemLp f p μ) (hg : MemLp g q μ) : YoungExpected.Result μ p q r f g := by
  have hmain : (∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ) ∧
      MemLp (integralConvolution μ f g) r μ ∧
      eLpNorm (integralConvolution μ f g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
    by_cases hrtop : r = ∞
    · subst r
      have h := young_infty μ (by simpa using hs) hf hg
      exact ⟨Filter.Eventually.of_forall h.1, h.2⟩
    · exact young_finite μ hp hq hr hs hrtop hf hg
  refine ⟨hmain.1, hmain.2.1, hmain.2.2, ?_⟩
  intro f' g' hf' hg' x
  exact congrFun (integralConvolution_congr μ hf' hg') x

end Group

section Completion
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {𝕜 : Type*} [RCLike 𝕜]

/-- Completing a measure leaves the totalized Bochner integral unchanged. -/
theorem integral_completion (f : α → 𝕜) :
    (∫ x : NullMeasurableSpace α μ, f x ∂μ.completion) = ∫ x, f x ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have hmp : @MeasurePreserving (NullMeasurableSpace α μ) α _ _ (fun x => x) μ.completion μ := by
      have hm : @Measurable (NullMeasurableSpace α μ) α _ _ (fun x => x) :=
        fun s hs => hs.nullMeasurableSet
      refine ⟨hm, ?_⟩
      apply Measure.ext
      intro s hs
      exact (Measure.map_apply hm hs).trans rfl
    have h := integral_map hmp.measurable.aemeasurable
      (show AEStronglyMeasurable f (Measure.map (fun x : NullMeasurableSpace α μ => (x : α)) μ.completion)
        from hmp.map_eq.symm ▸ hf)
    simpa only [hmp.map_eq, Function.comp_apply] using h.symm
  · have hc : ¬ AEStronglyMeasurable (α := NullMeasurableSpace α μ) f μ.completion :=
      fun hc => hf (Periodic.aeStrong_completion μ f hc)
    exact (integral_non_aestronglyMeasurable hc).trans (integral_non_aestronglyMeasurable hf).symm

/-- A completed-measurable Lp representative has a Borel-measurable replacement,
with the same norm and integrals. -/
theorem completed_borel_representative {p : ℝ≥0∞} {f : α → 𝕜}
    (hf : MemLp (α := NullMeasurableSpace α μ) f p μ.completion) :
    ∃ f₀ : α → 𝕜, Measurable f₀ ∧ f =ᵐ[μ] f₀ ∧ MemLp f₀ p μ ∧
      eLpNorm (α := NullMeasurableSpace α μ) f p μ.completion = eLpNorm f₀ p μ ∧
      (∫ x : NullMeasurableSpace α μ, f x ∂μ.completion) = ∫ x, f₀ x ∂μ := by
  have hf' := (Periodic.mem_completion μ f p).mp hf
  let f₀ := hf'.aestronglyMeasurable.mk f
  have heq : f =ᵐ[μ] f₀ := hf'.aestronglyMeasurable.ae_eq_mk
  refine ⟨f₀, hf'.aestronglyMeasurable.measurable_mk, heq, hf'.ae_eq heq, ?_, ?_⟩
  · rw [Periodic.norm_completion μ f p hf'.aestronglyMeasurable, eLpNorm_congr_ae heq]
  · rw [integral_completion, integral_congr_ae heq]

end Completion

section CompletedGroup
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G]
  (μ : Measure G) [SFinite μ] [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
  {𝕜 : Type*} [RCLike 𝕜]

/-- The full theorem for completed-measurable inputs, with completed integrals. -/
theorem young_completed {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : 1 + r⁻¹ = p⁻¹ + q⁻¹) {f g : G → 𝕜}
    (hf : MemLp (α := NullMeasurableSpace G μ) f p μ.completion)
    (hg : MemLp (α := NullMeasurableSpace G μ) g q μ.completion) :
    YoungExpected.CompletedResult μ p q r f g := by
  have hf' := (Periodic.mem_completion μ f p).mp hf
  have hg' := (Periodic.mem_completion μ g q).mp hg
  have h := young μ hp hq hr hs hf' hg'
  have hconv : (fun x : G => ∫ y : NullMeasurableSpace G μ, f (@Sub.sub G _ x y) * g y ∂μ.completion) =
      integralConvolution μ f g := by
    funext x
    exact integral_completion μ (fun y => f (x - y) * g y)
  unfold YoungExpected.CompletedResult
  dsimp only [NullMeasurableSpace] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [h.1] with x hx
    exact memLp_one_iff_integrable.mp ((Periodic.mem_completion μ (fun y => f (x - y) * g y) 1).mpr
      (memLp_one_iff_integrable.mpr hx))
  · rw [hconv]
    exact (Periodic.mem_completion μ _ r).mpr h.2.1
  · erw [hconv, Periodic.norm_completion μ _ r h.2.1.aestronglyMeasurable,
      Periodic.norm_completion μ f p hf'.aestronglyMeasurable,
      Periodic.norm_completion μ g q hg'.aestronglyMeasurable]
    exact h.2.2.1
  · intro f' g' hf0 hg0 x
    erw [integral_completion μ (fun y => f (x - y) * g y),
      integral_completion μ (fun y => f' (x - y) * g' y)]
    exact h.2.2.2 f' g' hf0 hg0 x

end CompletedGroup

/-- Young on R^d with Lebesgue measure. -/
theorem euclidean_young : YoungExpected.EuclideanYoung := by
  intro d _hd 𝕜 _ p q r hp hq hr hs f g hf hg
  exact young volume hp hq hr hs hf hg

/-- Young on the circle with the canonical probability Haar measure dt/T. -/
theorem circle_young : YoungExpected.CircleYoung := by
  intro T _ 𝕜 _ p q r hp hq hr hs f g hf hg
  exact young (Periodic.haar T) hp hq hr hs hf hg

/-- Euclidean Young for completed-Lebesgue measurable representatives. -/
theorem euclidean_completed_young : YoungExpected.EuclideanCompletedYoung := by
  intro d _hd 𝕜 _ p q r hp hq hr hs f g hf hg
  exact young_completed volume hp hq hr hs hf hg

/-- Periodic Young for completed-Haar measurable representatives. -/
theorem circle_completed_young : YoungExpected.CircleCompletedYoung := by
  intro T _ 𝕜 _ p q r hp hq hr hs f g hf hg
  exact young_completed (Periodic.haar T) hp hq hr hs hf hg

end P102.U2.Young
