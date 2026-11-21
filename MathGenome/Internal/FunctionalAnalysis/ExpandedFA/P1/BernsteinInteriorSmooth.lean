import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BernsteinInteriorSmooth
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Bernstein
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace ExpandedFA.P1.BernsteinInteriorSmooth
open MeasureTheory Set Filter Bernstein
open scoped Topology NNReal ENNReal

/-- A uniform bound, valid on every closed positive time half-line. -/
theorem polynomial_exp_bound (m : ℕ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : a ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    r ^ m * Real.exp (-r * t) ≤ (m.factorial : ℝ) / a ^ m := by
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have hap : 0 < a ^ m := pow_pos ha _
  have h := Real.pow_div_factorial_le_exp (a * r) (mul_nonneg ha.le hr) m
  have hpow : a ^ m * r ^ m ≤ (m.factorial : ℝ) * Real.exp (a * r) := by
    simpa only [mul_pow, mul_comm] using (div_le_iff₀ hfac).mp h
  have he : Real.exp (a * r) * Real.exp (-r * a) = 1 := by
    rw [← Real.exp_add, show a * r + -r * a = 0 by ring, Real.exp_zero]
  have hb : r ^ m * Real.exp (-r * a) ≤ (m.factorial : ℝ) / a ^ m := by
    apply (le_div_iff₀ hap).mpr
    nlinarith [mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-r * a)).le]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
    (pow_nonneg hr _)).trans hb

def signedKernel (m : ℕ) (t : ℝ) (rate : ℝ≥0∞) : ℝ :=
  (-rate.toReal) ^ m * Real.exp (-rate.toReal * t)

def signedMoment (ν : Measure ℝ≥0∞) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ rate in ({∞}ᶜ : Set ℝ≥0∞), signedKernel m t rate ∂ν

theorem signedKernel_measurable (m : ℕ) (t : ℝ) : Measurable (signedKernel m t) := by
  unfold signedKernel
  fun_prop

theorem signedKernel_norm_bound (m : ℕ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : a ≤ t)
    (rate : ℝ≥0∞) : ‖signedKernel m t rate‖ ≤ (m.factorial : ℝ) / a ^ m := by
  simpa [signedKernel, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg rate.toReal_nonneg, abs_of_pos (Real.exp_pos _)] using
    polynomial_exp_bound m ha ht rate.toReal_nonneg

theorem signedKernel_integrable (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν]
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (signedKernel m t) (ν.restrict {∞}ᶜ) := by
  apply Integrable.mono' (integrable_const ((m.factorial : ℝ) / t ^ m))
    (signedKernel_measurable m t).aestronglyMeasurable
  exact Eventually.of_forall (signedKernel_norm_bound m ht le_rfl)

theorem signedKernel_hasDerivAt (m : ℕ) (rate : ℝ≥0∞) (t : ℝ) :
    HasDerivAt (fun x => signedKernel m x rate) (signedKernel (m + 1) t rate) t := by
  convert (((hasDerivAt_id t).const_mul (-rate.toReal)).exp.const_mul
    ((-rate.toReal) ^ m)) using 1 <;> simp [signedKernel, pow_succ]
  ring

theorem signedMoment_hasDerivAt (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν]
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedMoment ν m) (signedMoment ν (m + 1) t) t := by
  have hhalf : 0 < t / 2 := half_pos ht
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν.restrict {∞}ᶜ) (F := signedKernel m) (F' := signedKernel (m + 1))
    (bound := fun _ => ((m + 1).factorial : ℝ) / (t / 2) ^ (m + 1))
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall fun x => (signedKernel_measurable m x).aestronglyMeasurable)
    (signedKernel_integrable ν m ht)
    (signedKernel_measurable (m + 1) t).aestronglyMeasurable
    (Eventually.of_forall fun rate x hx => signedKernel_norm_bound (m + 1) hhalf hx.le rate)
    (integrable_const _)
    (Eventually.of_forall fun rate x _ => signedKernel_hasDerivAt m rate x)).2

theorem signedMoment_contDiffOn_nat (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν] (n : ℕ) :
    ∀ m, ContDiffOn ℝ n (signedMoment ν m) (Ioi 0) := by
  induction n with
  | zero =>
    intro m
    apply contDiffOn_zero.mpr
    intro t ht
    exact (signedMoment_hasDerivAt ν m ht).continuousAt.continuousWithinAt
  | succ n ih =>
    intro m
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht => (signedMoment_hasDerivAt ν m ht).differentiableAt.differentiableWithinAt,
      ?_, (ih (m + 1)).congr (fun t ht => (signedMoment_hasDerivAt ν m ht).deriv)⟩
    simp

theorem signedMoment_iteratedDeriv (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν] (m : ℕ) :
    EqOn (iteratedDeriv m (signedMoment ν 0)) (signedMoment ν m) (Ioi 0) := by
  induction m with
  | zero => intro t _; simp
  | succ m ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv m (signedMoment ν 0) =ᶠ[𝓝 t] signedMoment ν m := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact ih hx
    exact ((signedMoment_hasDerivAt ν m ht).congr_of_eventuallyEq heq).deriv

/-- The infinity atom contributes zero on the entire open time half-line. -/
theorem realLaplaceTransform_eq (ν : Measure ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    realLaplaceTransform ν t = signedMoment ν 0 t := by
  unfold realLaplaceTransform laplaceTransform signedMoment
  rw [← integral_indicator (measurableSet_singleton ∞).compl]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro rate
  induction rate using ENNReal.recTopCoe with
  | top =>
    have hne : t.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr ht)
    simp [kernel_interpretation.2, hne]
  | coe r =>
    simp [kernel_interpretation.1, signedKernel, Real.coe_toNNReal t ht.le]

theorem interior_smooth : Specs.ExpandedFA.P1.BernsteinInteriorSmooth.InteriorSmooth := by
  intro ν _
  apply (contDiffOn_infty.mpr fun n => signedMoment_contDiffOn_nat ν n 0).congr
  intro t ht
  exact realLaplaceTransform_eq ν ht

theorem signedMoment_eq (ν : Measure ℝ≥0∞) (m : ℕ) (t : ℝ) :
    signedMoment ν m t = (-1 : ℝ) ^ m * laplaceMoment ν m t := by
  rw [signedMoment, laplaceMoment, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun rate => by rw [signedKernel, neg_pow, mul_assoc]

theorem moment_integrable (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν]
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun rate : ℝ≥0∞ => rate.toReal ^ m * Real.exp (-rate.toReal * t))
      (ν.restrict {∞}ᶜ) := by
  apply Integrable.mono' (integrable_const ((m.factorial : ℝ) / t ^ m))
    (by fun_prop)
  apply Eventually.of_forall
  intro rate
  simpa [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg rate.toReal_nonneg,
    abs_of_pos (Real.exp_pos _)] using polynomial_exp_bound m ht le_rfl rate.toReal_nonneg

theorem alternating_derivatives :
    Specs.ExpandedFA.P1.BernsteinInteriorSmooth.AlternatingDerivatives := by
  intro ν _ m t ht
  refine ⟨moment_integrable ν m ht, ?_, ?_⟩
  · have heq : EqOn (realLaplaceTransform ν) (signedMoment ν 0) (Ioi 0) :=
      fun _ hx => realLaplaceTransform_eq ν hx
    rw [heq.iteratedDeriv_of_isOpen isOpen_Ioi m ht,
      signedMoment_iteratedDeriv ν m ht, signedMoment_eq]
    rw [← mul_assoc, ← mul_pow]
    simp
  · exact integral_nonneg fun rate => mul_nonneg (pow_nonneg rate.toReal_nonneg _)
      (Real.exp_pos _).le

theorem endpoint_counterexample :
    Specs.ExpandedFA.P1.BernsteinInteriorSmooth.EndpointCounterexample := by
  refine ⟨fun hs _ t => infinityExponential_mem.2.2 hs t, ?_⟩
  rintro ⟨ν, hν, heq⟩
  let := hν
  have hcont := finiteTransform_right_continuous ν
  rw [← heq] at hcont
  have hzero : Tendsto infinityExponential (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [infinityExponential, ne_of_gt (mem_Ioi.mp ht)]
  have := tendsto_nhds_unique hcont hzero
  simp [infinityExponential] at this

end ExpandedFA.P1.BernsteinInteriorSmooth
