import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.VolterraPowerAsymptotic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2HilbertSchmidt
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.VolterraPowerAsymptotic
open VolterraPowerAsymptoticSpec
open VolterraSingularSystemSpec

lemma powerKernelFunction_measurable (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    Measurable (powerKernelFunction 𝕜 n) := by
  unfold powerKernelFunction
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    (RCLike.continuous_ofReal.measurable.comp
      (((measurable_fst.sub measurable_snd).pow_const n).div_const _)) measurable_const

lemma powerKernelFunction_bound (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (n : ℕ) (p : ℝ × ℝ) (ht : p.1 ∈ Ioo 0 T) (hs : p.2 ∈ Ioo 0 T) :
    ‖powerKernelFunction 𝕜 n p‖ ≤ T ^ n / (n.factorial : ℝ) := by
  unfold powerKernelFunction
  split_ifs with h
  · rw [RCLike.norm_ofReal, abs_of_nonneg
      (div_nonneg (pow_nonneg (sub_nonneg.mpr h.le) _) (Nat.cast_nonneg _))]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (sub_nonneg.mpr h.le) (by linarith [ht.2, hs.1]) _)
      (Nat.cast_nonneg _)
  · simpa using div_nonneg (pow_nonneg hT.le n) (Nat.cast_nonneg n.factorial)

lemma interval_prod_ae_mem (T : ℝ) :
    ∀ᵐ p ∂(intervalMeasure T).prod (intervalMeasure T),
      p.1 ∈ Ioo 0 T ∧ p.2 ∈ Ioo 0 T := by
  have ha := (Measure.quasiMeasurePreserving_fst
    (μ := intervalMeasure T) (ν := intervalMeasure T)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioo)
  have hb := (Measure.quasiMeasurePreserving_snd
    (μ := intervalMeasure T) (ν := intervalMeasure T)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioo)
  exact ha.and hb

lemma powerKernelFunction_memLp (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (n : ℕ) :
    MemLp (powerKernelFunction 𝕜 n) 2 ((intervalMeasure T).prod (intervalMeasure T)) := by
  exact MemLp.of_bound (powerKernelFunction_measurable 𝕜 n).aestronglyMeasurable
    (T ^ n / (n.factorial : ℝ))
    ((interval_prod_ae_mem T).mono fun p hp => powerKernelFunction_bound 𝕜 T hT n p hp.1 hp.2)

lemma integral_shifted_power (n : ℕ) (s t : ℝ) (hst : s ≤ t) :
    (∫ r in Ioo s t, (r-s)^n / (n.factorial : ℝ)) =
      (t-s)^(n+1) / ((n+1).factorial : ℝ) := by
  rw [integral_div, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hst,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^n),
    integral_pow, sub_self, zero_pow (by omega : n+1 ≠ 0), sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_div, mul_comm (n + 1 : ℝ)]

lemma powerKernelFunction_recurrence (𝕜 : Type) [RCLike 𝕜] (T : ℝ)
    (n : ℕ) (t s : ℝ) (ht : t ∈ Ioo 0 T) (hs : s ∈ Ioo 0 T) :
    (∫ r, powerKernelFunction 𝕜 0 (t,r) * powerKernelFunction 𝕜 n (r,s)
      ∂intervalMeasure T) = powerKernelFunction 𝕜 (n+1) (t,s) := by
  have heq : (fun r => powerKernelFunction 𝕜 0 (t,r) * powerKernelFunction 𝕜 n (r,s)) =
      (Ioo s t).indicator (fun r => (((r-s)^n / (n.factorial : ℝ) : ℝ) : 𝕜)) := by
    funext r
    by_cases hr : r < t <;> by_cases hr' : s < r <;>
      simp [powerKernelFunction, hr, hr', Set.mem_Ioo, and_comm]
  rw [heq, integral_indicator measurableSet_Ioo, intervalMeasure,
    Measure.restrict_restrict measurableSet_Ioo]
  have hset : Ioo s t ∩ Ioo 0 T = Ioo s t := by
    ext r
    simp only [mem_inter_iff, mem_Ioo]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, hs.1.trans h.1, h.2.trans ht.2⟩
  rw [hset, integral_ofReal]
  by_cases hst : s < t
  · rw [powerKernelFunction, ite_eq_left hst, integral_shifted_power n s t hst.le]
  · rw [powerKernelFunction, ite_eq_right hst, Ioo_eq_empty_of_le (le_of_not_gt hst)]
    simp

lemma powerKernelFunction_zero (𝕜 : Type) [RCLike 𝕜] :
    powerKernelFunction 𝕜 0 = kernelFunction 𝕜 := by
  funext p
  simp [powerKernelFunction, kernelFunction]

lemma composition_integrable (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (n : ℕ) (t : ℝ) (u : ℝ → 𝕜) (hu : MemLp u 2 (intervalMeasure T)) :
    Integrable (fun p : ℝ × ℝ => powerKernelFunction 𝕜 0 (t,p.1) *
      (powerKernelFunction 𝕜 n p * u p.2))
      ((intervalMeasure T).prod (intervalMeasure T)) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => powerKernelFunction 𝕜 0 (t,p.1) *
        (powerKernelFunction 𝕜 n p * u p.2))
      ((intervalMeasure T).prod (intervalMeasure T)) :=
    (((powerKernelFunction_measurable 𝕜 0).comp
      (measurable_const.prodMk measurable_fst)).aestronglyMeasurable).mul
      ((powerKernelFunction_measurable 𝕜 n).aestronglyMeasurable.mul
        hu.aestronglyMeasurable.comp_snd)
  apply (((hu.integrable (by norm_num)).norm.comp_snd (intervalMeasure T)).const_mul
    (T ^ n / (n.factorial : ℝ))).mono' hm
  filter_upwards [interval_prod_ae_mem T] with p hp
  rw [norm_mul, norm_mul]
  have h0 : ‖powerKernelFunction 𝕜 0 (t,p.1)‖ ≤ 1 := by
    rw [powerKernelFunction_zero]
    dsimp [kernelFunction]
    split_ifs <;> simp
  calc
    _ ≤ 1 * ((T^n / (n.factorial : ℝ)) * ‖u p.2‖) :=
      mul_le_mul h0
        (mul_le_mul_of_nonneg_right (powerKernelFunction_bound 𝕜 T hT n p hp.1 hp.2)
          (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := one_mul _

lemma kernel_composition (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) (n : ℕ) :
    operator 𝕜 T * L2KernelSpec.OperatorValue (intervalMeasure T) (intervalMeasure T)
      ((powerKernelFunction_memLp 𝕜 T hT n).toLp _) =
    L2KernelSpec.OperatorValue (intervalMeasure T) (intervalMeasure T)
      ((powerKernelFunction_memLp 𝕜 T hT (n+1)).toLp _) := by
  ext1 u
  simp only [mul_apply_eq_comp]
  apply Lp.ext
  have h0 := L2Kernel.kernel_representative_formula (intervalMeasure T) (intervalMeasure T)
    (kernelFunction 𝕜)
    (L2KernelSpec.OperatorValue (intervalMeasure T) (intervalMeasure T)
      ((powerKernelFunction_memLp 𝕜 T hT n).toLp _) u)
    (kernel_memLp 𝕜 T) (Lp.memLp _)
  simp only [Lp.toLp_coeFn] at h0
  have hn := L2Kernel.kernel_representative_formula (intervalMeasure T) (intervalMeasure T)
    (powerKernelFunction 𝕜 n) u (powerKernelFunction_memLp 𝕜 T hT n) (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hn
  have hn1 := L2Kernel.kernel_representative_formula (intervalMeasure T) (intervalMeasure T)
    (powerKernelFunction 𝕜 (n+1)) u (powerKernelFunction_memLp 𝕜 T hT (n+1)) (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hn1
  filter_upwards [h0, hn1, ae_restrict_mem measurableSet_Ioo] with t ht ht' htm
  change _ = _ at ht
  dsimp only [operator, kernel] at ⊢
  rw [ht, ht', ← powerKernelFunction_zero 𝕜]
  calc
    _ = ∫ r, powerKernelFunction 𝕜 0 (t,r) *
        (∫ s, powerKernelFunction 𝕜 n (r,s) * u s ∂intervalMeasure T)
        ∂intervalMeasure T := by
      apply integral_congr_ae
      filter_upwards [hn] with r hr
      rw [hr]
    _ = ∫ r, ∫ s, powerKernelFunction 𝕜 0 (t,r) *
        (powerKernelFunction 𝕜 n (r,s) * u s) ∂intervalMeasure T ∂intervalMeasure T := by
      congr 1
      funext r
      rw [integral_const_mul]
    _ = ∫ s, ∫ r, powerKernelFunction 𝕜 0 (t,r) *
        (powerKernelFunction 𝕜 n (r,s) * u s) ∂intervalMeasure T ∂intervalMeasure T :=
      integral_integral_swap (composition_integrable 𝕜 T hT n t u (Lp.memLp u))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      simp_rw [← mul_assoc]
      rw [integral_mul_const, powerKernelFunction_recurrence 𝕜 T n t s htm hs]

lemma power_kernel_formula_aux (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) (n : ℕ) :
    operator 𝕜 T ^ (n+1) =
      L2KernelSpec.OperatorValue (intervalMeasure T) (intervalMeasure T)
        ((powerKernelFunction_memLp 𝕜 T hT n).toLp _) := by
  induction n with
  | zero => simp [powerKernelFunction_zero, operator, kernel]
  | succ n ih =>
    rw [pow_succ', ih]
    exact kernel_composition 𝕜 T hT n

theorem power_kernel_memLp : PowerKernelMemLp := powerKernelFunction_memLp

theorem power_kernel_formula : PowerKernelFormula := by
  intro 𝕜 _ T hT n hk
  exact power_kernel_formula_aux 𝕜 T hT n

theorem power_integral_formula : PowerIntegralFormula := by
  intro 𝕜 _ T hT n u
  rw [power_kernel_formula_aux 𝕜 T hT n]
  have h := L2Kernel.kernel_representative_formula (intervalMeasure T) (intervalMeasure T)
    (powerKernelFunction 𝕜 n) u (powerKernelFunction_memLp 𝕜 T hT n) (Lp.memLp u)
  simpa only [Lp.toLp_coeFn] using h


lemma rescaledKernel_nonneg (n : ℕ) (p : ℝ × ℝ) : 0 ≤ rescaledKernel n p := by
  unfold rescaledKernel
  split_ifs with h
  · have hn : 0 < (n : ℝ) := lt_of_le_of_lt (add_nonneg h.1 h.2.1) h.2.2
    exact pow_nonneg (sub_nonneg.mpr ((div_le_one hn).mpr h.2.2.le)) _
  · exact le_rfl

lemma rescaledKernel_measurable (n : ℕ) : Measurable (rescaledKernel n) := by
  apply Measurable.ite
    ((measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const)))
    _ measurable_const
  exact (measurable_const.sub ((measurable_fst.add measurable_snd).div_const _)).pow_const _

lemma limitingKernel_continuous : Continuous limitingKernel := by
  unfold limitingKernel
  fun_prop

/-- On the positive quadrant the cutoff disappears eventually. -/
theorem pointwise_limit : PointwiseLimit := by
  intro p ha hb
  have hbase : Tendsto (fun n : ℕ => 1 - (p.1 + p.2) / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hpow : Tendsto (fun n : ℕ => (1 - (p.1 + p.2) / n) ^ n)
      atTop (𝓝 (Real.exp (-(p.1 + p.2)))) := by
    simpa only [neg_div, ← sub_eq_add_neg] using
      Real.tendsto_one_add_div_pow_exp (-(p.1 + p.2))
  have h := hpow.div hbase (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  have he : limitingKernel p = Real.exp (-(p.1 + p.2)) := by
    unfold limitingKernel
    congr 1
    ring
  rw [he]
  apply h.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (p.1 + p.2)), eventually_ge_atTop 1] with n hn hn1
  rw [rescaledKernel, ite_eq_left ⟨ha, hb, hn⟩]
  have hpos : 0 < (1 - (p.1 + p.2) / (n : ℝ)) := by
    have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (add_nonneg ha hb) hn
    exact sub_pos.mpr ((div_lt_one hn0).mpr hn)
  change (1 - (p.1 + p.2) / (n : ℝ)) ^ n /
    (1 - (p.1 + p.2) / (n : ℝ)) = _
  conv_lhs => enter [1, 2]; rw [← Nat.sub_add_cancel hn1]
  rw [pow_succ, mul_div_cancel_right₀ _ hpos.ne']

theorem exponential_domination : ExponentialDomination := by
  intro n hn p
  refine ⟨rescaledKernel_nonneg n p, ?_⟩
  unfold rescaledKernel
  split_ifs with h
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hbase : 0 ≤ 1 - (p.1 + p.2) / (n : ℝ) :=
      sub_nonneg.mpr ((div_le_one hn0).mpr h.2.2.le)
    calc
      _ ≤ Real.exp (-((p.1 + p.2) / (n : ℝ))) ^ (n - 1) :=
        pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _) _
      _ = Real.exp ((n - 1 : ℕ) * (-((p.1 + p.2) / (n : ℝ)))) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hx : 0 ≤ p.1 + p.2 := add_nonneg h.1 h.2.1
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        apply (mul_le_mul_iff_right₀ hn0).mp
        field_simp
        nlinarith [mul_nonneg hx (sub_nonneg.mpr hn2)]
  · exact (Real.exp_pos _).le


theorem positive_part_formula : PositivePartFormula := by
  intro n hn p
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  by_cases h : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 < (n : ℝ)
  · have hp : p ∈ Icc (0 : ℝ) n ×ˢ Icc (0 : ℝ) n := by
      exact ⟨⟨h.1, by linarith [h.2.1]⟩, ⟨h.2.1, by linarith [h.1]⟩⟩
    rw [rescaledKernel, ite_eq_left h, indicator_of_mem hp, max_eq_left]
    exact sub_nonneg.mpr ((div_le_one hn0).mpr h.2.2.le)
  · rw [rescaledKernel, ite_eq_right h]
    by_cases hp : p ∈ Icc (0 : ℝ) n ×ˢ Icc (0 : ℝ) n
    · have hsum : (n : ℝ) ≤ p.1 + p.2 := by
        by_contra hs
        exact h ⟨hp.1.1, hp.2.1, lt_of_not_ge hs⟩
      rw [indicator_of_mem hp, max_eq_right
        (sub_nonpos.mpr ((one_le_div hn0).mpr hsum)), zero_pow (by omega : n - 1 ≠ 0)]
    · rw [indicator_of_notMem hp]

lemma quadrant_ae_nonneg : ∀ᵐ p ∂quadrantMeasure, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  have ha := (Measure.quasiMeasurePreserving_fst
    (μ := halfLineMeasure) (ν := halfLineMeasure)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioi)
  have hb := (Measure.quasiMeasurePreserving_snd
    (μ := halfLineMeasure) (ν := halfLineMeasure)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ha, hb] with p ha hb
  exact ⟨ha.le, hb.le⟩

lemma integrable_exponential_bound :
    Integrable (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2))
      quadrantMeasure :=
  (integrableOn_exp_neg_Ioi 0).mul_prod (integrableOn_exp_neg_Ioi 0)

lemma limitingKernel_le_bound (p : ℝ × ℝ) (ha : 0 ≤ p.1) (hb : 0 ≤ p.2) :
    limitingKernel p ≤ Real.exp (-(p.1 + p.2) / 2) := by
  apply Real.exp_le_exp.mpr
  linarith

lemma squared_error_bound (n : ℕ) (hn : 2 ≤ n) (p : ℝ × ℝ)
    (ha : 0 ≤ p.1) (hb : 0 ≤ p.2) :
    ‖(rescaledKernel n p - limitingKernel p) ^ 2‖ ≤
      Real.exp (-p.1) * Real.exp (-p.2) := by
  obtain ⟨hq0, hq⟩ := exponential_domination n hn p
  have hf0 : 0 ≤ limitingKernel p := (Real.exp_pos _).le
  have hf := limitingKernel_le_bound p ha hb
  have habs : |rescaledKernel n p - limitingKernel p| ≤
      Real.exp (-(p.1 + p.2) / 2) := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ = |rescaledKernel n p - limitingKernel p| ^ 2 := (sq_abs _).symm
    _ ≤ Real.exp (-(p.1 + p.2) / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = Real.exp (-p.1) * Real.exp (-p.2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

/-- Dominated convergence for the squared difference, on the fixed quadrant. -/
theorem squared_error_convergence : SquaredErrorConvergence := by
  unfold SquaredErrorConvergence
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun p => (rescaledKernel n p - limitingKernel p) ^ 2) quadrantMeasure := by
    exact (((rescaledKernel_measurable n).sub limitingKernel_continuous.measurable).pow_const 2).aestronglyMeasurable
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := quadrantMeasure) (f := fun _ : ℝ × ℝ => (0 : ℝ))
    (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2))
    (Eventually.of_forall hm)
    (eventually_atTop.mpr ⟨2, fun n hn => quadrant_ae_nonneg.mono fun p hp =>
      squared_error_bound n hn p hp.1 hp.2⟩)
    integrable_exponential_bound
    (quadrant_ae_nonneg.mono fun p hp => by
      simpa using ((pointwise_limit p hp.1 hp.2).sub
        (tendsto_const_nhds (x := limitingKernel p))).pow 2)
  simpa using h


lemma square_le_exponential_bound {x : ℝ} (hx0 : 0 ≤ x) (p : ℝ × ℝ)
    (hx : x ≤ Real.exp (-(p.1 + p.2) / 2)) :
    ‖x ^ 2‖ ≤ Real.exp (-p.1) * Real.exp (-p.2) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ Real.exp (-(p.1 + p.2) / 2) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

theorem kernel_memLp : KernelMemLp := by
  intro 𝕜 _
  constructor
  · intro n hn
    have hq : MemLp (rescaledKernel n) 2 quadrantMeasure := by
      apply (memLp_two_iff_integrable_sq (rescaledKernel_measurable n).aestronglyMeasurable).mpr
      apply integrable_exponential_bound.mono'
        ((rescaledKernel_measurable n).pow_const 2).aestronglyMeasurable
      exact Eventually.of_forall fun p => square_le_exponential_bound
        (rescaledKernel_nonneg n p) p (exponential_domination n hn p).2
    exact hq.ofReal
  · have hf : MemLp limitingKernel 2 quadrantMeasure := by
      apply (memLp_two_iff_integrable_sq limitingKernel_continuous.aestronglyMeasurable).mpr
      apply integrable_exponential_bound.mono'
        (limitingKernel_continuous.pow 2).aestronglyMeasurable
      exact quadrant_ae_nonneg.mono fun p hp => square_le_exponential_bound
        (Real.exp_pos _).le p (limitingKernel_le_bound p hp.1 hp.2)
    exact hf.ofReal

/-- The scalar-valued L² error has exactly the real squared error integral. -/
lemma kernel_error_norm_sq (𝕜 : Type) [RCLike 𝕜] (n : ℕ)
    (hq : MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure)
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure) :
    ‖hq.toLp _ - hf.toLp _‖ ^ 2 =
      ∫ p, (rescaledKernel n p - limitingKernel p) ^ 2 ∂quadrantMeasure := by
  have heq : hq.toLp _ - hf.toLp _ = (hq.sub hf).toLp _ :=
    Lp.ext ((Lp.coeFn_sub _ _).trans (hq.coeFn_toLp.sub hf.coeFn_toLp)
      |>.trans (hq.sub hf).coeFn_toLp.symm)
  rw [heq, ← L2Kernel.integral_sq_norm _ (hq.sub hf)]
  congr 1
  funext p
  change ‖(rescaledKernel n p : 𝕜) - (limitingKernel p : 𝕜)‖ ^ 2 = _
  rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, sq_abs]

theorem kernel_l2_convergence : KernelL2Convergence := by
  intro 𝕜 _ hq hf
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (squared_error_convergence.comp (tendsto_add_atTop_nat 2))
  have hsq : Tendsto (fun n : ℕ => ‖(hq (n+2) (by omega)).toLp _ - hf.toLp _‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [kernel_error_norm_sq, Function.comp_def] using hs
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

theorem kernel_operator_convergence : KernelOperatorConvergence := by
  intro 𝕜 _ hq hf
  exact (L2KernelCompact.kernelAssignment (𝕜 := 𝕜) halfLineMeasure halfLineMeasure).continuous.continuousAt.tendsto.comp (kernel_l2_convergence 𝕜 hq hf)


lemma exponentialVector_memLp (𝕜 : Type) [RCLike 𝕜] :
    MemLp (fun t : ℝ => (Real.exp (-t) : 𝕜)) 2 halfLineMeasure := by
  have h : MemLp (fun t : ℝ => Real.exp (-t)) 2 halfLineMeasure := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    have heq : (fun t : ℝ => Real.exp (-t) ^ 2) =
        (fun t : ℝ => Real.exp ((-2) * t)) := by
      funext t
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [heq]
    exact integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0
  exact h.ofReal

def exponentialVector (𝕜 : Type) [RCLike 𝕜] : Lp 𝕜 2 halfLineMeasure :=
  (exponentialVector_memLp 𝕜).toLp (fun t => (Real.exp (-t) : 𝕜))

lemma exponentialVector_norm_sq (𝕜 : Type) [RCLike 𝕜] :
    ‖exponentialVector 𝕜‖ ^ 2 = 1 / 2 := by
  rw [exponentialVector, ← L2Kernel.integral_sq_norm]
  calc
    _ = ∫ t : ℝ in Ioi 0, Real.exp ((-2) * t) := by
      congr 1
      funext t
      rw [RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
      congr 1
      norm_num
    _ = 1 / 2 := by
      rw [integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
      norm_num

lemma limitingKernel_eq_productVector (𝕜 : Type) [RCLike 𝕜]
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure) :
    hf.toLp _ = L2HilbertSchmidt.productVector halfLineMeasure halfLineMeasure
      (exponentialVector 𝕜) (exponentialVector 𝕜) := by
  apply Lp.ext
  filter_upwards [hf.coeFn_toLp,
    L2HilbertSchmidt.productVector_coe halfLineMeasure halfLineMeasure
      (exponentialVector 𝕜) (exponentialVector 𝕜),
    (Measure.quasiMeasurePreserving_fst (μ := halfLineMeasure) (ν := halfLineMeasure)).ae_eq_comp (exponentialVector_memLp 𝕜).coeFn_toLp,
    (Measure.quasiMeasurePreserving_snd (μ := halfLineMeasure) (ν := halfLineMeasure)).ae_eq_comp (exponentialVector_memLp 𝕜).coeFn_toLp] with p hp hk ha hb
  change exponentialVector 𝕜 p.1 = _ at ha
  change exponentialVector 𝕜 p.2 = _ at hb
  simp only [Function.comp_apply] at ha hb
  rw [hp, hk, ha, hb, RCLike.conj_ofReal, ← RCLike.ofReal_mul]
  congr 1
  simp only [limitingKernel, sub_eq_add_neg, Real.exp_add]

/-- The limiting integral operator is the actual rank-one map v ↦ ⟪e,v⟫ e. -/
lemma limitingOperator_eq_rankOne (𝕜 : Type) [RCLike 𝕜]
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure) :
    L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure (hf.toLp _) =
      InnerProductSpace.rankOne 𝕜 (exponentialVector 𝕜) (exponentialVector 𝕜) := by
  rw [limitingKernel_eq_productVector 𝕜 hf]
  ext1 u
  apply ext_inner_left 𝕜
  intro v
  rw [InnerProductSpace.inner_right_rankOne_apply]
  exact (L2HilbertSchmidt.productVector_coefficient halfLineMeasure halfLineMeasure
    (L2HilbertSchmidt.productVector halfLineMeasure halfLineMeasure
      (exponentialVector 𝕜) (exponentialVector 𝕜)) v u).symm.trans
    (L2HilbertSchmidt.productVector_inner halfLineMeasure halfLineMeasure
      v (exponentialVector 𝕜) u (exponentialVector 𝕜))

theorem limiting_operator_norm : LimitingOperatorNorm := by
  intro 𝕜 _ hf
  rw [limitingOperator_eq_rankOne 𝕜 hf, InnerProductSpace.norm_rankOne, ← pow_two]
  exact exponentialVector_norm_sq 𝕜


theorem hilbertSchmidt_convergence : HilbertSchmidtConvergence := by
  intro 𝕜 _ hq hf
  dsimp only
  have hmap (n : ℕ) :
      L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
        ((hq (n+2) (by omega)).toLp _) -
        L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure (hf.toLp _) =
      L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
        ((hq (n+2) (by omega)).toLp _ - hf.toLp _) :=
    ((L2KernelCompact.kernelAssignment (𝕜 := 𝕜) halfLineMeasure halfLineMeasure).map_sub _ _).symm
  constructor
  · intro n
    rw [hmap]
    exact L2HilbertSchmidt.kernel_hilbertSchmidt halfLineMeasure halfLineMeasure _
  · have heq (n : ℕ) : Real.sqrt
        (ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue
          (L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
            ((hq (n+2) (by omega)).toLp _) -
           L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure (hf.toLp _))).toReal =
        ‖(hq (n+2) (by omega)).toLp _ - hf.toLp _‖ := by
      rw [hmap]
      change Real.sqrt
        (ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.hilbertSchmidtSquare
          (L2Kernel.kernelOperator halfLineMeasure halfLineMeasure
            ((hq (n+2) (by omega)).toLp _ - hf.toLp _))).toReal = _
      rw [L2HilbertSchmidt.kernel_square_norm, ENNReal.toReal_ofReal (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]
    simp_rw [heq]
    exact tendsto_iff_norm_sub_tendsto_zero.mp (kernel_l2_convergence 𝕜 hq hf)

/-- The analytic part of the asymptotic, isolated from the coordinate bridge. -/
theorem normalized_limit_of_rescaled_norm_identity (hbridge : RescaledNormIdentity) :
    NormalizedPowerNormLimit := by
  intro 𝕜 _ T hT
  obtain ⟨hq, hf⟩ := kernel_memLp 𝕜
  have hl := (kernel_operator_convergence 𝕜 hq hf).norm
  rw [limiting_operator_norm 𝕜 hf] at hl
  apply (tendsto_add_atTop_iff_nat 2).mp
  convert hl using 1
  funext n
  exact (hbridge 𝕜 T hT (n+2) (by omega) (hq (n+2) (by omega))).symm

theorem asymptotic_of_normalized_limit (h : NormalizedPowerNormLimit) :
    PowerNormAsymptotic := by
  intro 𝕜 _ T hT
  have hl := (h 𝕜 T hT).const_mul 2
  norm_num at hl
  convert hl using 1
  funext n
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp


lemma weighted_kernel_intertwining
    (𝕜 : Type) [RCLike 𝕜] (r : ℝ) (hr : 0 < r)
    (μ ν μ' ν' : Measure ℝ)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite μ'] [SigmaFinite ν']
    (f g : ℝ → ℝ)
    (hf : MeasurePreserving f (ENNReal.ofReal r • μ') μ)
    (hg : MeasurePreserving g (ENNReal.ofReal r • ν') ν)
    (hgm : MeasurableEmbedding g)
    (U : Lp 𝕜 2 μ ≃ₗᵢ[𝕜] Lp 𝕜 2 μ')
    (V : Lp 𝕜 2 ν ≃ₗᵢ[𝕜] Lp 𝕜 2 ν')
    (hU : ∀ u, (U u : ℝ → 𝕜) =ᵐ[μ'] fun x => (Real.sqrt r : 𝕜) * u (f x))
    (hV : ∀ u, (V u : ℝ → 𝕜) =ᵐ[ν'] fun x => (Real.sqrt r : 𝕜) * u (g x))
    (k k' : ℝ × ℝ → 𝕜)
    (hk : MemLp k 2 (μ.prod ν)) (hk' : MemLp k' 2 (μ'.prod ν'))
    (he : k' =ᵐ[μ'.prod ν'] fun p => (r : 𝕜) * k (f p.1, g p.2)) :
    (L2KernelSpec.OperatorValue μ' ν' (hk'.toLp k')).comp (V : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 ν') =
      (U : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ').comp (L2KernelSpec.OperatorValue μ ν (hk.toLp k)) := by
  ext1 u
  apply Lp.ext
  have hK := L2Kernel.kernel_representative_formula μ ν k u hk (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hK
  have hKf : ∀ᵐ x ∂μ',
      (L2KernelSpec.OperatorValue μ ν (hk.toLp k) u) (f x) =
        ∫ y, k (f x, y) * u y ∂ν :=
    (ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hr)).mp
      (hf.quasiMeasurePreserving.ae_eq_comp hK)
  have hK' := L2Kernel.kernel_representative_formula μ' ν' k' (V u) hk' (Lp.memLp (V u))
  simp only [Lp.toLp_coeFn] at hK'
  filter_upwards [hK', hU (L2KernelSpec.OperatorValue μ ν (hk.toLp k) u),
    hKf, Measure.ae_ae_of_ae_prod he] with x hx hUx hKx hex
  change (L2KernelSpec.OperatorValue μ' ν' (hk'.toLp k') (V u)) x =
    (U (L2KernelSpec.OperatorValue μ ν (hk.toLp k) u)) x
  rw [hx, hUx, hKx]
  calc
    _ = ∫ y, (Real.sqrt r : 𝕜) * ((r : 𝕜) * (k (f x, g y) * u (g y))) ∂ν' := by
      apply integral_congr_ae
      filter_upwards [hex, hV u] with y hy huy
      rw [hy, huy]
      ring
    _ = (Real.sqrt r : 𝕜) * ((r : 𝕜) * ∫ y, k (f x, g y) * u (g y) ∂ν') := by
      rw [integral_const_mul, integral_const_mul]
    _ = (Real.sqrt r : 𝕜) * ∫ y, k (f x, g y) * u (g y) ∂(ENNReal.ofReal r • ν') := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hr.le, RCLike.real_smul_eq_coe_mul]
    _ = _ := by rw [hg.integral_comp hgm (fun y => k (f x, y) * u y)]

lemma weighted_kernel_norm
    (𝕜 : Type) [RCLike 𝕜] (r : ℝ) (hr : 0 < r)
    (μ ν μ' ν' : Measure ℝ)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite μ'] [SigmaFinite ν']
    (f g : ℝ → ℝ)
    (hf : MeasurePreserving f (ENNReal.ofReal r • μ') μ)
    (hg : MeasurePreserving g (ENNReal.ofReal r • ν') ν)
    (hgm : MeasurableEmbedding g)
    (U : Lp 𝕜 2 μ ≃ₗᵢ[𝕜] Lp 𝕜 2 μ')
    (V : Lp 𝕜 2 ν ≃ₗᵢ[𝕜] Lp 𝕜 2 ν')
    (hU : ∀ u, (U u : ℝ → 𝕜) =ᵐ[μ'] fun x => (Real.sqrt r : 𝕜) * u (f x))
    (hV : ∀ u, (V u : ℝ → 𝕜) =ᵐ[ν'] fun x => (Real.sqrt r : 𝕜) * u (g x))
    (k k' : ℝ × ℝ → 𝕜)
    (hk : MemLp k 2 (μ.prod ν)) (hk' : MemLp k' 2 (μ'.prod ν'))
    (he : k' =ᵐ[μ'.prod ν'] fun p => (r : 𝕜) * k (f p.1, g p.2)) :
    ‖L2KernelSpec.OperatorValue μ' ν' (hk'.toLp k')‖ =
      ‖L2KernelSpec.OperatorValue μ ν (hk.toLp k)‖ := by
  have h := congrArg norm (weighted_kernel_intertwining 𝕜 r hr μ ν μ' ν' f g hf hg hgm U V hU hV k k' hk hk' he)
  simpa only [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp] using h


namespace L2Restriction

variable {X : Type*} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
  (μ : Measure X) [SigmaFinite μ] (s : Set X) (hs : MeasurableSet s)

/-- Restrict a class to a smaller measure. -/
def restrictL2 (u : Lp 𝕜 2 μ) : Lp 𝕜 2 (μ.restrict s) :=
  ((Lp.memLp u).restrict s).toLp u

lemma restrictL2_ae (u : Lp 𝕜 2 μ) :
    (restrictL2 μ s u : X → 𝕜) =ᵐ[μ.restrict s] u :=
  MemLp.coeFn_toLp _

lemma restrictL2_norm_le (u : Lp 𝕜 2 μ) : ‖restrictL2 μ s u‖ ≤ ‖u‖ := by
  rw [restrictL2, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top (eLpNorm_mono_measure u Measure.restrict_le_self)

/-- Extension by zero from the restricted measure. -/
def extendL2 (u : Lp 𝕜 2 (μ.restrict s)) : Lp 𝕜 2 μ :=
  ((memLp_indicator_iff_restrict hs.nullMeasurableSet).mpr (Lp.memLp u)).toLp (s.indicator u)

lemma extendL2_ae (u : Lp 𝕜 2 (μ.restrict s)) :
    (extendL2 μ s hs u : X → 𝕜) =ᵐ[μ] s.indicator u :=
  MemLp.coeFn_toLp _

lemma extendL2_norm (u : Lp 𝕜 2 (μ.restrict s)) : ‖extendL2 μ s hs u‖ = ‖u‖ := by
  rw [extendL2, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, Lp.norm_def]

lemma restrictL2_extendL2 (u : Lp 𝕜 2 (μ.restrict s)) :
    restrictL2 μ s (extendL2 μ s hs u) = u := by
  apply Lp.ext
  filter_upwards [restrictL2_ae μ s (extendL2 μ s hs u),
    ae_restrict_of_ae (extendL2_ae μ s hs u),
    indicator_ae_eq_restrict hs.nullMeasurableSet (f := (u : X → 𝕜))] with x h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃)

include hs in
lemma integral_restrict_supported (k : X × X → 𝕜)
    (hsupport : ∀ p, p ∉ s ×ˢ s → k p = 0) (u : X → 𝕜) :
    s.indicator (fun x => ∫ y, k (x,y) * u y ∂μ.restrict s) =
      fun x => ∫ y, k (x,y) * u y ∂μ := by
  funext x
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, ← integral_indicator hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ s
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy]
        change 0 = k (x,y) * u y
        rw [hsupport (x,y) (by simp [hy]), zero_mul]
  · rw [indicator_of_notMem hx]
    symm
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun y => by
      change k (x,y) * u y = 0
      rw [hsupport (x,y) (by simp [hx]), zero_mul]

lemma kernel_restrict_intertwine (k : X × X → 𝕜)
    (hk : MemLp k 2 (μ.prod μ))
    (hkr : MemLp k 2 ((μ.restrict s).prod (μ.restrict s)))
    (hsupport : ∀ p, p ∉ s ×ˢ s → k p = 0) (u : Lp 𝕜 2 μ) :
    ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (hk.toLp k) u =
      extendL2 μ s hs
        (ExpandedFA.PartV.L2KernelSpec.OperatorValue (μ.restrict s) (μ.restrict s)
          (hkr.toLp k) (restrictL2 μ s u)) := by
  apply Lp.ext
  have hbig := ExpandedFA.PartV.L2Kernel.kernel_representative_formula μ μ
    k u hk (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hbig
  have hsmall := ExpandedFA.PartV.L2Kernel.kernel_representative_formula
    (μ.restrict s) (μ.restrict s) k u hkr ((Lp.memLp u).restrict s)
  have hsmall' := (ae_eq_restrict_iff_indicator_ae_eq hs).mp hsmall
  have hext := extendL2_ae μ s hs
    (ExpandedFA.PartV.L2KernelSpec.OperatorValue (μ.restrict s) (μ.restrict s)
      (hkr.toLp k) (restrictL2 μ s u))
  rw [integral_restrict_supported μ s hs k hsupport u] at hsmall'
  exact hbig.trans (hext.trans hsmall').symm

include hs in
lemma kernel_restrict_norm (k : X × X → 𝕜)
    (hk : MemLp k 2 (μ.prod μ))
    (hkr : MemLp k 2 ((μ.restrict s).prod (μ.restrict s)))
    (hsupport : ∀ p, p ∉ s ×ˢ s → k p = 0) :
    ‖ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (hk.toLp k)‖ =
      ‖ExpandedFA.PartV.L2KernelSpec.OperatorValue (μ.restrict s) (μ.restrict s)
        (hkr.toLp k)‖ := by
  let A := ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (hk.toLp k)
  let B := ExpandedFA.PartV.L2KernelSpec.OperatorValue (μ.restrict s) (μ.restrict s)
        (hkr.toLp k)
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro u
    rw [kernel_restrict_intertwine μ s hs k hk hkr hsupport u, extendL2_norm]
    exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (restrictL2_norm_le μ s u)
      (norm_nonneg B))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro u
    have h := kernel_restrict_intertwine μ s hs k hk hkr hsupport (extendL2 μ s hs u)
    rw [restrictL2_extendL2] at h
    have hn := congrArg norm h
    rw [extendL2_norm] at hn
    rw [← hn]
    exact (A.le_opNorm _).trans_eq (congrArg (fun r => ‖A‖ * r) (extendL2_norm μ s hs u))

lemma halfLine_restrict (N : ℝ) :
    ExpandedFA.PartV.VolterraPowerAsymptoticSpec.halfLineMeasure.restrict (Iio N) =
      ExpandedFA.PartV.VolterraSingularSystemSpec.intervalMeasure N := by
  rw [Measure.restrict_restrict measurableSet_Iio]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
  exact and_comm

lemma rescaledKernel_support (n : ℕ) (p : ℝ × ℝ)
    (hp : p ∉ Iio (n : ℝ) ×ˢ Iio (n : ℝ)) :
    ExpandedFA.PartV.VolterraPowerAsymptoticSpec.rescaledKernel n p = 0 := by
  unfold ExpandedFA.PartV.VolterraPowerAsymptoticSpec.rescaledKernel
  split_ifs with h
  · have h₁ : p.1 < n := by linarith [h.2.1, h.2.2]
    have h₂ : p.2 < n := by linarith [h.1, h.2.2]
    exact False.elim (hp ⟨h₁,h₂⟩)
  · rfl

lemma rescaledKernel_interval_memLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ)
    (hq : MemLp (fun p =>
      (ExpandedFA.PartV.VolterraPowerAsymptoticSpec.rescaledKernel n p : 𝕜)) 2
      ExpandedFA.PartV.VolterraPowerAsymptoticSpec.quadrantMeasure) :
    MemLp (fun p => (ExpandedFA.PartV.VolterraPowerAsymptoticSpec.rescaledKernel n p : 𝕜))
      2 ((ExpandedFA.PartV.VolterraSingularSystemSpec.intervalMeasure n).prod
        (ExpandedFA.PartV.VolterraSingularSystemSpec.intervalMeasure n)) := by
  have h := hq.restrict (Iio (n : ℝ) ×ˢ Iio (n : ℝ))
  rw [← Measure.prod_restrict, halfLine_restrict] at h
  exact h

lemma kernel_norm_measure_congr (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (h : μ = ν) (k : X × X → 𝕜) (hμ : MemLp k 2 (μ.prod μ))
    (hν : MemLp k 2 (ν.prod ν)) :
    ‖ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (hμ.toLp k)‖ =
      ‖ExpandedFA.PartV.L2KernelSpec.OperatorValue ν ν (hν.toLp k)‖ := by
  subst ν
  rfl

lemma rescaledKernel_extension_norm (𝕜 : Type) [RCLike 𝕜] (n : ℕ)
    (hq : MemLp (fun p =>
      (ExpandedFA.PartV.VolterraPowerAsymptoticSpec.rescaledKernel n p : 𝕜)) 2
      ExpandedFA.PartV.VolterraPowerAsymptoticSpec.quadrantMeasure) :
    ‖ExpandedFA.PartV.L2KernelSpec.OperatorValue
      ExpandedFA.PartV.VolterraPowerAsymptoticSpec.halfLineMeasure
      ExpandedFA.PartV.VolterraPowerAsymptoticSpec.halfLineMeasure (hq.toLp _)‖ =
    ‖ExpandedFA.PartV.L2KernelSpec.OperatorValue
      (ExpandedFA.PartV.VolterraSingularSystemSpec.intervalMeasure n)
      (ExpandedFA.PartV.VolterraSingularSystemSpec.intervalMeasure n)
      ((rescaledKernel_interval_memLp 𝕜 n hq).toLp _)‖ := by
  have hr := rescaledKernel_interval_memLp 𝕜 n hq
  rw [← halfLine_restrict] at hr
  have h := kernel_restrict_norm _ _ measurableSet_Iio _ hq hr (by
    intro p hp
    rw [rescaledKernel_support n p hp, RCLike.ofReal_zero])
  exact h.trans (kernel_norm_measure_congr _ _ (halfLine_restrict n) _ hr
    (rescaledKernel_interval_memLp 𝕜 n hq))


end L2Restriction


lemma rescaled_power_kernel (𝕜 : Type) [RCLike 𝕜]
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((T / n : ℝ) : 𝕜) * powerKernelFunction 𝕜 (n-1)
      (T * (1 - a / n), T * b / n) =
    ((T ^ n / (n.factorial : ℝ) : ℝ) : 𝕜) * (rescaledKernel n (a,b) : 𝕜) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hiff : T * b / (n : ℝ) < T * (1 - a / n) ↔ a + b < n := by
    rw [div_lt_iff₀ hnR]
    have hmul : T * (1 - a / (n : ℝ)) * n = T * ((n : ℝ) - a) := by
      field_simp
    rw [hmul]
    constructor <;> intro h <;> nlinarith
  have hbase : T * (1 - a / (n : ℝ)) - T * b / n =
      T * (1 - (a+b)/n) := by ring
  unfold powerKernelFunction rescaledKernel
  simp only [ha, hb, true_and, hiff]
  split_ifs with h
  · simp only [← RCLike.ofReal_mul]
    congr 1
    rw [hbase, mul_pow]
    have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n-1).factorial : ℝ) := by
      have heq : n = (n-1)+1 := by omega
      have h := Nat.factorial_succ (n-1)
      rw [← heq] at h
      exact_mod_cast h
    rw [hfac]
    have hp : T ^ n = T * T ^ (n-1) := by
      conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
      ring
    rw [hp]
    ring
  · simp
lemma rescaled_power_kernel_affine (𝕜 : Type) [RCLike 𝕜]
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((T / n : ℝ) : 𝕜) * powerKernelFunction 𝕜 (n-1)
      (T - (T / n) * a, (T / n) * b) =
    ((T ^ n / (n.factorial : ℝ) : ℝ) : 𝕜) * (rescaledKernel n (a,b) : 𝕜) := by
  have hf : T - (T / (n : ℝ)) * a = T * (1 - a / n) := by ring
  have hg : (T / (n : ℝ)) * b = T * b / n := by ring
  rw [hf, hg]
  exact rescaled_power_kernel 𝕜 T hT n hn a b ha hb

lemma rescaled_power_kernel_ae (𝕜 : Type) [RCLike 𝕜]
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n) :
    (fun p : ℝ × ℝ => ((T / n : ℝ) : 𝕜) * powerKernelFunction 𝕜 (n-1)
      (T - (T / n) * p.1, (T / n) * p.2)) =ᵐ[
        (intervalMeasure n).prod (intervalMeasure n)]
    fun p => ((T ^ n / (n.factorial : ℝ) : ℝ) : 𝕜) * (rescaledKernel n p : 𝕜) := by
  have ha := (Measure.quasiMeasurePreserving_fst
    (μ := intervalMeasure n) (ν := intervalMeasure n)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioo)
  have hb := (Measure.quasiMeasurePreserving_snd
    (μ := intervalMeasure n) (ν := intervalMeasure n)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [ha, hb] with p hp hq
  exact rescaled_power_kernel_affine 𝕜 T hT n hn p.1 p.2 hp.1.le hq.1.le

lemma rescaled_power_kernel_memLp (𝕜 : Type) [RCLike 𝕜]
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n)
    (hq : MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure) :
    MemLp (fun p : ℝ × ℝ => ((T / n : ℝ) : 𝕜) * powerKernelFunction 𝕜 (n-1)
      (T - (T / n) * p.1, (T / n) * p.2)) 2
      ((intervalMeasure n).prod (intervalMeasure n)) := by
  exact ((L2Restriction.rescaledKernel_interval_memLp 𝕜 n hq).const_mul
    ((T ^ n / (n.factorial : ℝ) : ℝ) : 𝕜)).ae_eq
      (rescaled_power_kernel_ae 𝕜 T hT n hn).symm

lemma kernel_norm_of_ae_scalar (𝕜 : Type) [RCLike 𝕜]
    (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (k q : ℝ × ℝ → 𝕜) (hk : MemLp k 2 (μ.prod ν))
    (hq : MemLp q 2 (μ.prod ν)) (c : ℝ) (hc : 0 ≤ c)
    (heq : k =ᵐ[μ.prod ν] fun p => (c : 𝕜) * q p) :
    ‖L2KernelSpec.OperatorValue μ ν (hk.toLp _)‖ =
      c * ‖L2KernelSpec.OperatorValue μ ν (hq.toLp _)‖ := by
  have hLp : hk.toLp k = (c : 𝕜) • hq.toLp q := by
    apply Lp.ext
    filter_upwards [hk.coeFn_toLp, hq.coeFn_toLp,
      Lp.coeFn_smul (c : 𝕜) (hq.toLp q), heq] with p hp hq' hc' heq'
    rw [hp, hc', Pi.smul_apply, smul_eq_mul, hq', heq']
  rw [hLp]
  change ‖L2Kernel.kernelOperator μ ν ((c : 𝕜) • hq.toLp q)‖ = _
  rw [L2KernelCompact.kernelOperator_smul μ ν, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg hc]
  rfl

lemma normalize_rescaled_norm (n : ℕ) (T q v : ℝ) (hT : 0 < T)
    (heq : v = T ^ n / (n.factorial : ℝ) * q) :
    q = (n.factorial : ℝ) * v / T ^ n := by
  have hTn : T ^ n ≠ 0 := pow_ne_zero _ hT.ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [heq]
  field_simp


namespace AffineL2
open MeasureTheory.Measure
variable {𝕜 : Type} [RCLike 𝕜] {X : Type*} [MeasurableSpace X]
  (μ : Measure X) (r : ℝ) (hr : 0 < r)

include hr
lemma unweight_memLp (u : Lp 𝕜 2 (ENNReal.ofReal r • μ)) : MemLp u 2 μ := by
  apply (Lp.memLp u).of_measure_le_smul (c := (ENNReal.ofReal r)⁻¹) (by simpa using hr)
  simp [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top]

def unweight : Lp 𝕜 2 (ENNReal.ofReal r • μ) →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun u := (unweight_memLp μ r hr u).toLp u
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(unweight_memLp μ r hr (u+v)).coeFn_toLp,
      Lp.coeFn_add (unweight_memLp μ r hr u |>.toLp u) (unweight_memLp μ r hr v |>.toLp v),
      (unweight_memLp μ r hr u).coeFn_toLp, (unweight_memLp μ r hr v).coeFn_toLp,
      (ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hr)).mp (Lp.coeFn_add u v)] with x h1 h2 h3 h4 h5
    exact h1.trans (h5.trans (h2.trans (by simpa only [Pi.add_apply,h3,h4])).symm)
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(unweight_memLp μ r hr (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((unweight_memLp μ r hr u).toLp u),
      (unweight_memLp μ r hr u).coeFn_toLp,
      (ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hr)).mp (Lp.coeFn_smul c u)] with x h1 h2 h3 h4
    simpa only [RingHom.id_apply] using h1.trans (h4.trans (h2.trans (by simpa only [Pi.smul_apply,h3])).symm)

lemma coe_unweight (u : Lp 𝕜 2 (ENNReal.ofReal r • μ)) :
    unweight μ r hr u =ᵐ[μ] u := (unweight_memLp μ r hr u).coeFn_toLp

lemma norm_unweight (u : Lp 𝕜 2 (ENNReal.ofReal r • μ)) :
    ‖u‖ ^ 2 = r * ‖unweight μ r hr u‖ ^ 2 := by
  conv_lhs => rw [← Lp.toLp_coeFn u (Lp.memLp u)]
  rw [← ExpandedFA.PartV.L2Kernel.integral_sq_norm _ (Lp.memLp u), integral_smul_measure]
  rw [ENNReal.toReal_ofReal hr.le, smul_eq_mul]
  congr 1
  exact ExpandedFA.PartV.L2Kernel.integral_sq_norm _ (unweight_memLp μ r hr u)

def normalize : Lp 𝕜 2 (ENNReal.ofReal r • μ) →ₗᵢ[𝕜] Lp 𝕜 2 μ where
  toLinearMap := (Real.sqrt r : 𝕜) • unweight μ r hr
  norm_map' u := by
    have h := norm_unweight μ r hr u
    have hs : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
    have hnorm : ‖(Real.sqrt r : 𝕜)‖ = Real.sqrt r := by simp [abs_of_nonneg hs]
    change ‖(Real.sqrt r : 𝕜) • unweight μ r hr u‖ = ‖u‖
    rw [norm_smul, hnorm]
    have heq : (Real.sqrt r * ‖unweight μ r hr u‖)^2 = ‖u‖^2 := by
      rw [mul_pow, Real.sq_sqrt hr.le, ← h]
    nlinarith [mul_nonneg hs (norm_nonneg (unweight μ r hr u)), norm_nonneg u]

lemma coe_normalize (u : Lp 𝕜 2 (ENNReal.ofReal r • μ)) :
    normalize μ r hr u =ᵐ[μ] fun x => (Real.sqrt r : 𝕜) * u x := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt r : 𝕜) (unweight μ r hr u),
    coe_unweight μ r hr u] with x hx hy
  change ((Real.sqrt r : 𝕜) • unweight μ r hr u : Lp 𝕜 2 μ) x = _
  simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx

lemma normalize_surjective : Function.Surjective (normalize (𝕜 := 𝕜) μ r hr) := by
  intro v
  let w : Lp 𝕜 2 (ENNReal.ofReal r • μ) :=
    (((Lp.memLp v).const_smul (Real.sqrt r : 𝕜)⁻¹).smul_measure ENNReal.ofReal_ne_top).toLp _
  refine ⟨w, Lp.ext ?_⟩
  have hw : w =ᵐ[μ] fun x => (Real.sqrt r : 𝕜)⁻¹ * v x :=
    (ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hr)).mp
      (MemLp.coeFn_toLp _)
  filter_upwards [coe_normalize μ r hr w, hw] with x hx hy
  rw [hx, hy, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (Real.sqrt_pos.mpr hr).ne'

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)

def weightedPullback (e : Y ≃ᵐ X)
    (he : MeasurePreserving e (ENNReal.ofReal r • ν) μ) :
    Lp 𝕜 2 μ ≃ₗᵢ[𝕜] Lp 𝕜 2 ν :=
  LinearIsometryEquiv.ofSurjective
    ((normalize ν r hr).comp (Lp.compMeasurePreservingₗᵢ 𝕜 e he)) (by
      apply (normalize_surjective ν r hr).comp
      intro w
      refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) w, ?_⟩
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving e.symm (he.symm e) w) he,
        he.quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_compMeasurePreserving w (he.symm e))] with x hx hy
      change (Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) w)) x = w x
      simpa only [Function.comp_apply, e.symm_apply_apply] using hx.trans hy)

lemma coe_weightedPullback (e : Y ≃ᵐ X)
    (he : MeasurePreserving e (ENNReal.ofReal r • ν) μ) (u : Lp 𝕜 2 μ) :
    weightedPullback μ r hr ν e he u =ᵐ[ν]
      fun x => (Real.sqrt r : 𝕜) * u (e x) := by
  have h : Lp.compMeasurePreserving e he u =ᵐ[ν] u ∘ e :=
    (ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hr)).mp
      (Lp.coeFn_compMeasurePreserving u he)
  filter_upwards [coe_normalize ν r hr (Lp.compMeasurePreserving e he u), h] with x hx hy
  exact hx.trans (congrArg ((Real.sqrt r : 𝕜) * ·) hy)
end AffineL2

namespace AffineL2
open MeasureTheory.Measure

lemma scale_preserving (r N : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun x : ℝ => r*x)
      (ENNReal.ofReal r • volume.restrict (Ioo 0 N))
      (volume.restrict (Ioo 0 (r*N))) := by
  have hg : MeasurePreserving (fun x : ℝ => r*x) (ENNReal.ofReal r • volume) volume := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [Measure.map_smul (ENNReal.ofReal r) (measurable_const_mul r).aemeasurable]
    simpa only [abs_of_pos hr] using Real.smul_map_volume_mul_left hr.ne'
  have hp : (fun x : ℝ => r*x) ⁻¹' Ioo 0 (r*N) = Ioo 0 N := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · intro h
      exact ⟨(mul_pos_iff_of_pos_left hr).mp h.1,
        (mul_lt_mul_iff_right₀ hr).mp h.2⟩
    · intro h
      exact ⟨mul_pos hr h.1, (mul_lt_mul_iff_right₀ hr).mpr h.2⟩
  simpa only [hp, Measure.restrict_smul] using hg.restrict_preimage (s := Ioo 0 (r*N)) measurableSet_Ioo

lemma reflection_preserving (T : ℝ) :
    MeasurePreserving (fun x : ℝ => T-x)
      (volume.restrict (Ioo 0 T)) (volume.restrict (Ioo 0 T)) := by
  have hn : MeasurePreserving (fun x : ℝ => -x) volume volume := by
    refine ⟨measurable_neg, ?_⟩
    simpa using Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num)
  have hg : MeasurePreserving (fun x : ℝ => T-x) volume volume :=
    (measurePreserving_add_left volume T).comp hn
  have hp : (fun x : ℝ => T-x) ⁻¹' Ioo 0 T = Ioo 0 T := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simpa only [hp] using hg.restrict_preimage (s := Ioo 0 T) measurableSet_Ioo

lemma input_preserving (T N : ℝ) (hT : 0 < T) (hN : 0 < N) :
    MeasurePreserving (fun x : ℝ => T/N*x)
      (ENNReal.ofReal (T/N) • volume.restrict (Ioo 0 N))
      (volume.restrict (Ioo 0 T)) := by
  simpa only [div_mul_cancel₀ T hN.ne'] using scale_preserving (T/N) N (div_pos hT hN)

lemma output_preserving (T N : ℝ) (hT : 0 < T) (hN : 0 < N) :
    MeasurePreserving (fun x : ℝ => T-T/N*x)
      (ENNReal.ofReal (T/N) • volume.restrict (Ioo 0 N))
      (volume.restrict (Ioo 0 T)) :=
  (reflection_preserving T).comp (input_preserving T N hT hN)


def input_measurableEquiv (T N : ℝ) (hT : 0 < T) (hN : 0 < N) : ℝ ≃ᵐ ℝ :=
  MeasurableEquiv.mulLeft₀ (T/N) (div_pos hT hN).ne'

@[simp] lemma input_measurableEquiv_apply (T N : ℝ) (hT : 0 < T) (hN : 0 < N) (x : ℝ) :
    input_measurableEquiv T N hT hN x = T/N*x := rfl

def output_measurableEquiv (T N : ℝ) (hT : 0 < T) (hN : 0 < N) : ℝ ≃ᵐ ℝ :=
  (input_measurableEquiv T N hT hN).trans (MeasurableEquiv.subLeft T)

@[simp] lemma output_measurableEquiv_apply (T N : ℝ) (hT : 0 < T) (hN : 0 < N) (x : ℝ) :
    output_measurableEquiv T N hT hN x = T-T/N*x := rfl

end AffineL2


lemma rescaled_norm_from_affine
    (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 2 ≤ n)
    (hq : MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure)
    (hf : MeasurePreserving (fun x : ℝ => T-T/n*x)
      (ENNReal.ofReal (T/n) • intervalMeasure n) (intervalMeasure T))
    (hg : MeasurePreserving (fun x : ℝ => T/n*x)
      (ENNReal.ofReal (T/n) • intervalMeasure n) (intervalMeasure T))
    (hgm : MeasurableEmbedding (fun x : ℝ => T/n*x))
    (U V : Space 𝕜 T ≃ₗᵢ[𝕜] Space 𝕜 n)
    (hU : ∀ u, (U u : ℝ → 𝕜) =ᵐ[intervalMeasure n]
      fun x => (Real.sqrt (T/n) : 𝕜) * u (T-T/n*x))
    (hV : ∀ u, (V u : ℝ → 𝕜) =ᵐ[intervalMeasure n]
      fun x => (Real.sqrt (T/n) : 𝕜) * u (T/n*x)) :
    ‖L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure (hq.toLp _)‖ =
      (n.factorial : ℝ) * ‖operator 𝕜 T ^ n‖ / T ^ n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let pk := powerKernelFunction 𝕜 (n-1)
  let sk : ℝ × ℝ → 𝕜 := fun p => ((T/n : ℝ) : 𝕜) *
    pk (T-T/n*p.1, T/n*p.2)
  have hpk := powerKernelFunction_memLp 𝕜 T hT (n-1)
  have hsk := rescaled_power_kernel_memLp 𝕜 T hT n (by omega) hq
  have hqN := L2Restriction.rescaledKernel_interval_memLp 𝕜 n hq
  have hscale := weighted_kernel_norm 𝕜 (T/n) (div_pos hT hnR)
    (intervalMeasure T) (intervalMeasure T) (intervalMeasure n) (intervalMeasure n)
    (fun x : ℝ => T-T/n*x) (fun x : ℝ => T/n*x) hf hg hgm
    U V hU hV pk sk hpk hsk (Eventually.of_forall fun _ => rfl)
  have hscalar := kernel_norm_of_ae_scalar 𝕜 (intervalMeasure n) (intervalMeasure n)
    sk (fun p => (rescaledKernel n p : 𝕜)) hsk hqN
    (T^n/(n.factorial : ℝ)) (div_nonneg (pow_nonneg hT.le _) (Nat.cast_nonneg _))
    (rescaled_power_kernel_ae 𝕜 T hT n (by omega))
  have hpower := power_kernel_formula 𝕜 T hT (n-1) hpk
  rw [show n-1+1=n by omega] at hpower
  have heq : ‖operator 𝕜 T ^ n‖ = T^n/(n.factorial : ℝ) *
      ‖L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure (hq.toLp _)‖ := by
    rw [L2Restriction.rescaledKernel_extension_norm 𝕜 n hq]
    exact (congrArg norm hpower).trans (hscale.symm.trans hscalar)
  exact normalize_rescaled_norm n T _ _ hT heq

theorem rescaled_norm_identity : RescaledNormIdentity := by
  intro 𝕜 _ T hT n hn hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < T/(n : ℝ) := div_pos hT hnR
  let eIn := AffineL2.input_measurableEquiv T n hT hnR
  let eOut := AffineL2.output_measurableEquiv T n hT hnR
  have hf : MeasurePreserving eOut
      (ENNReal.ofReal (T/n) • intervalMeasure n) (intervalMeasure T) :=
    AffineL2.output_preserving T n hT hnR
  have hg : MeasurePreserving eIn
      (ENNReal.ofReal (T/n) • intervalMeasure n) (intervalMeasure T) :=
    AffineL2.input_preserving T n hT hnR
  let U : Space 𝕜 T ≃ₗᵢ[𝕜] Space 𝕜 n :=
    AffineL2.weightedPullback (intervalMeasure T) (T/n) hr (intervalMeasure n) eOut hf
  let V : Space 𝕜 T ≃ₗᵢ[𝕜] Space 𝕜 n :=
    AffineL2.weightedPullback (intervalMeasure T) (T/n) hr (intervalMeasure n) eIn hg
  apply rescaled_norm_from_affine 𝕜 T hT n hn hq hf hg eIn.measurableEmbedding U V
  · intro u
    exact AffineL2.coe_weightedPullback (intervalMeasure T) (T/n) hr
      (intervalMeasure n) eOut hf u
  · intro u
    exact AffineL2.coe_weightedPullback (intervalMeasure T) (T/n) hr
      (intervalMeasure n) eIn hg u


/-- The sharp normalized norm limit for the original L² integration operator. -/
theorem normalized_power_norm_limit : NormalizedPowerNormLimit :=
  normalized_limit_of_rescaled_norm_identity rescaled_norm_identity

/-- The ratio to T^n/(2 n!) converges to one, over either scalar field. -/
theorem power_norm_asymptotic : PowerNormAsymptotic :=
  asymptotic_of_normalized_limit normalized_power_norm_limit

end ExpandedFA.PartV.VolterraPowerAsymptotic
