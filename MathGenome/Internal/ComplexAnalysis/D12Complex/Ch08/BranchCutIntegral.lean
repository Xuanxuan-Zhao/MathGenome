import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.BranchCutIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Euler's integral, paper.tex:2181–2215. We use the substitution
`t = x / (1 + x)` to the convergent beta integral with parameters `s, 1-s`,
then Euler's reflection formula. The change of variables proves both
integrability and the value. A measure-integral limit theorem supplies
separate ordinary limits at zero and infinity, also for absolute values.
At the endpoints a lower bound by `1/(2x)` proves divergence to infinity.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D12Complex.BranchCutIntegral

private lemma real_beta_kernel (s t x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((x : ℂ) ^ ((s : ℂ) - 1) * (1 - (x : ℂ)) ^ ((t : ℂ) - 1)).re =
      x ^ (s - 1) * (1 - x) ^ (t - 1) := by
  have h : (x : ℂ) ^ ((s : ℂ) - 1) * (1 - (x : ℂ)) ^ ((t : ℂ) - 1) =
      ((x ^ (s - 1) * (1 - x) ^ (t - 1) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

private lemma real_beta_integrable {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => x ^ (s - 1) * (1 - x) ^ (t - 1)) (Ioo 0 1) := by
  have h := (Complex.betaIntegral_convergent (u := (s : ℂ)) (v := (t : ℂ))
    (by simpa) (by simpa)).1.mono_set Ioo_subset_Ioc_self
  exact h.re.congr_fun (fun x hx => real_beta_kernel s t x hx) measurableSet_Ioo

private lemma real_beta_integral {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (∫ x : ℝ in Ioo 0 1, x ^ (s - 1) * (1 - x) ^ (-s)) =
      Real.pi / Real.sin (Real.pi * s) := by
  have hc := Complex.betaIntegral_convergent (u := (s : ℂ)) (v := (1 - s : ℝ))
    (by simpa) (by simp only [Complex.ofReal_re]; linarith)
  have he := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (s : ℂ))
    (t := (1 - s : ℝ)) (by simpa) (by simp only [Complex.ofReal_re]; linarith)
  have hsum : (s : ℂ) + ((1 - s : ℝ) : ℂ) = 1 := by push_cast; ring
  rw [hsum, Complex.Gamma_one, one_mul] at he
  have hval : (Complex.betaIntegral (s : ℂ) (1 - s : ℝ)).re =
      Real.pi / Real.sin (Real.pi * s) := by
    rw [← he, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re, Real.Gamma_mul_Gamma_one_sub]
  rw [← hval, Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re (hc.1.mono_set Ioo_subset_Ioc_self)]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  simpa using (real_beta_kernel s (1 - s) x hx).symm

/-- The increasing substitution from the positive half-line to the unit interval. -/
lemma unit_fraction_image :
    (fun x : ℝ => x / (1 + x)) '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hd : 0 < 1 + x := by linarith only [show 0 < x from hx]
    exact ⟨div_pos hx hd, (div_lt_one hd).mpr (by linarith)⟩
  · intro ht
    refine ⟨t / (1 - t), div_pos ht.1 (sub_pos.mpr ht.2), ?_⟩
    have hd : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
    have h : 1 + t / (1 - t) = 1 / (1 - t) := by field_simp; ring
    dsimp only
    rw [h]
    field_simp

lemma hasDerivAt_unit_fraction (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y / (1 + y)) (1 / (1 + x) ^ 2) x := by
  have h := (hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1)
    (by linarith : 1 + x ≠ 0)
  have h' : HasDerivAt (fun y : ℝ => y / (1 + y))
      ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x := h
  convert h' using 1; ring

lemma unit_fraction_injOn : InjOn (fun x : ℝ => x / (1 + x)) (Ioi 0) := by
  intro x hx y hy h
  have hx' : 1 + x ≠ 0 := by linarith only [show 0 < x from hx]
  have hy' : 1 + y ≠ 0 := by linarith only [show 0 < y from hy]
  have he := (div_eq_div_iff hx' hy').mp h
  nlinarith

lemma beta_substitution_kernel (s x : ℝ) (hx : 0 < x) :
    |1 / (1 + x) ^ 2| •
      ((x / (1 + x)) ^ (s - 1) * (1 - x / (1 + x)) ^ (-s)) =
      x ^ (s - 1) / (1 + x) := by
  have hd : 0 < 1 + x := by linarith
  have he : 1 - x / (1 + x) = (1 + x)⁻¹ := by field_simp; ring
  have hp : (1 + x) ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have hpow : (1 + x) ^ s = (1 + x) ^ (s - 1) * (1 + x) := by
    rw [← Real.rpow_add_one hd.ne']
    congr 1
    ring
  rw [abs_of_pos (by positivity), smul_eq_mul, he,
    Real.div_rpow hx.le hd.le, Real.inv_rpow hd.le, Real.rpow_neg hd.le, inv_inv, hpow]
  field_simp

lemma integral_eq_beta (s : ℝ) :
    (∫ x : ℝ in Ioi 0, x ^ (s - 1) / (1 + x)) =
      ∫ x : ℝ in Ioo 0 1, x ^ (s - 1) * (1 - x) ^ (-s) := by
  rw [← unit_fraction_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x hx => (hasDerivAt_unit_fraction x hx).hasDerivWithinAt)
      unit_fraction_injOn]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx =>
    (beta_substitution_kernel s x hx).symm

theorem branch_cut_integrable :
    Specs.D12Complex.Ch08.BranchCutIntegral.branch_cut_integrable_type := by
  intro s hs hs1
  have hb : IntegrableOn (fun x : ℝ => x ^ (s - 1) * (1 - x) ^ (-s)) (Ioo 0 1) := by
    simpa using real_beta_integrable hs (sub_pos.mpr hs1)
  rw [← unit_fraction_image] at hb
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (hasDerivAt_unit_fraction x hx).hasDerivWithinAt)
    unit_fraction_injOn _).mp hb
  exact h.congr_fun (fun x hx => beta_substitution_kernel s x hx) measurableSet_Ioi

theorem branch_cut_integral :
    Specs.D12Complex.Ch08.BranchCutIntegral.branch_cut_integral_type := by
  intro s hs hs1
  exact (integral_eq_beta s).trans (real_beta_integral hs hs1)

/-- Integrability yields the independent ordinary limit at the finite open endpoint. -/
lemma tendsto_integral_left {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 0 1)) :
    Tendsto (fun ε : ℝ => ∫ x in ε..1, f x) (𝓝[>] 0)
      (𝓝 (∫ x in Ioc (0 : ℝ) 1, f x)) := by
  have ha : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (aecover_Ioc_of_Ioc (μ := volume) ha
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1))).integral_tendsto_of_countably_generated hf
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    ha.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
  rw [intervalIntegral.integral_of_le hε1.le,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_self_of_subset_left (Ioc_subset_Ioc_left (show 0 ≤ ε from le_of_lt hε))]

theorem branch_cut_improper :
    Specs.D12Complex.Ch08.BranchCutIntegral.branch_cut_improper_type := by
  intro s hs hs1
  have h := branch_cut_integrable s hs hs1
  have hleft := h.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
  have hright := h.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  refine ⟨tendsto_integral_left hleft,
    intervalIntegral_tendsto_integral_Ioi 1 hright tendsto_id,
    ?_, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, id_eq] using tendsto_integral_left hleft.norm
  · simpa only [Real.norm_eq_abs, id_eq] using
      intervalIntegral_tendsto_integral_Ioi 1 hright.norm tendsto_id
  · rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_interval_add_Ioi h hright]
    exact branch_cut_integral s hs hs1

lemma kernel_intervalIntegrable (s : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (s - 1) / (1 + x)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := (lt_min ha hb).trans_le hx.1
  exact ((continuousAt_id.rpow_const (Or.inl hx0.ne')).div
    (continuousAt_const.add continuousAt_id) (by change 1 + x ≠ 0; linarith)).continuousWithinAt

lemma inverse_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := (lt_min ha hb).trans_le hx.1
  exact (continuousAt_inv₀ hx0.ne').continuousWithinAt

theorem branch_cut_diverges_zero :
    Specs.D12Complex.Ch08.BranchCutIntegral.branch_cut_diverges_zero_type := by
  have ht : Tendsto (fun ε : ℝ => (1 / 2 : ℝ) * (-Real.log ε)) (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' (𝓝[>] 0) ?_ ht
  have ha : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    ha.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
  have h : (∫ x in ε..1, (1 / 2 : ℝ) * x⁻¹) ≤
      ∫ x in ε..1, x ^ ((0 : ℝ) - 1) / (1 + x) := by
    apply intervalIntegral.integral_mono_on hε1.le
      ((inverse_intervalIntegrable hε zero_lt_one).const_mul _) (kernel_intervalIntegrable 0 hε zero_lt_one)
    intro x hx
    have hx0 : 0 < x := hε.trans_le hx.1
    simp only [zero_sub, Real.rpow_neg_one]
    apply (le_div_iff₀ (by linarith : 0 < 1 + x)).mpr
    have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    nlinarith [mul_nonneg hinv (sub_nonneg.mpr hx.2)]
  simpa only [intervalIntegral.integral_const_mul, integral_inv_of_pos hε zero_lt_one,
    one_div, Real.log_inv] using h

theorem branch_cut_diverges_one :
    Specs.D12Complex.Ch08.BranchCutIntegral.branch_cut_diverges_one_type := by
  have ht : Tendsto (fun R : ℝ => (1 / 2 : ℝ) * Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  have h : (∫ x in (1 : ℝ)..R, (1 / 2 : ℝ) * x⁻¹) ≤
      ∫ x in (1 : ℝ)..R, x ^ ((1 : ℝ) - 1) / (1 + x) := by
    apply intervalIntegral.integral_mono_on hR.le
      ((inverse_intervalIntegrable zero_lt_one (zero_lt_one.trans hR)).const_mul _)
      (kernel_intervalIntegrable 1 zero_lt_one (zero_lt_one.trans hR))
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    simp only [sub_self, Real.rpow_zero]
    apply (le_div_iff₀ (by linarith : 0 < 1 + x)).mpr
    have hcancel : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
    have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).mpr hx.1
    nlinarith
  simpa only [intervalIntegral.integral_const_mul,
    integral_inv_of_pos zero_lt_one (zero_lt_one.trans hR), div_one] using h

end D12Complex.BranchCutIntegral
