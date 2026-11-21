import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ExponentialTails
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperContinuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter MeasureTheory Topology
namespace D04.ExponentialTails
open Specs.D04.C08.ExponentialTails.Model

lemma continuous_moment (j : ℕ) (a : ℝ) : Continuous (moment j a) := by
  unfold moment
  fun_prop

lemma continuous_kernel (j : ℕ) (a : ℝ) : Continuous (kernel j a) := by
  unfold kernel
  fun_prop

lemma proper_eq_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f)
    {u v : ℝ} (huv : u ≤ v) : proper f u v = ∫ x in u..v, f x := by
  have hi := SingleVariableAnalysis.ParameterIntegral.real_integrable_of_continuousOn huv hf.continuousOn
  rw [proper, dite_eq_left hi]
  let F : ℝ → ℝ := fun y => ∫ x in u..y, f x
  have hd (x : ℝ) : HasDerivAt F (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have he := SingleVariableAnalysis.Riemann.real_ftc_second F f u v huv
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x) hi
  simpa only [F, intervalIntegral.integral_same, sub_zero] using he

lemma proper_tendsto {f : ℝ → ℝ} (hf : Continuous f) (hi : IntegrableOn f (Ioi 0)) :
    Tendsto (fun R => proper f 0 R) atTop (𝓝 (∫ x in Ioi (0 : ℝ), f x)) := by
  apply (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact (proper_eq_intervalIntegral hf hR).symm

theorem parameter_derivative : Specs.D04.C08.ExponentialTails.parameter_derivativeType := by
  intro j x a
  have he : (fun b => Real.exp (-b * x)) = fun b => Real.exp ((-x) * b) := by
    funext b
    congr 1
    ring
  rw [he, iteratedDeriv_exp_const_mul]
  simp [kernel, mul_comm]

theorem polynomial_bound : Specs.D04.C08.ExponentialTails.polynomial_boundType := by
  intro j a₀ x ha hx
  have h := Real.pow_div_factorial_le_exp (a₀ * x / 2) (show 0 ≤ a₀ * x / 2 by positivity) j
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hh := (div_le_iff₀ hf).mp h
  have ht : (a₀ * x / 2) ^ j * (2 / a₀) ^ j = x ^ j := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc
    x ^ j = (a₀ * x / 2) ^ j * (2 / a₀) ^ j := ht.symm
    _ ≤ (Real.exp (a₀ * x / 2) * (j.factorial : ℝ)) * (2 / a₀) ^ j :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

lemma kernel_eq_signed_moment (j : ℕ) (a x : ℝ) :
    kernel j a x = (-1 : ℝ) ^ j * moment j a x := by
  unfold kernel moment
  rw [neg_pow]
  ring

lemma norm_kernel (j : ℕ) (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖kernel j a x‖ = moment j a x := by
  simp [kernel, moment, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx,
    abs_of_pos (Real.exp_pos _)]

theorem domination : Specs.D04.C08.ExponentialTails.dominationType := by
  intro j a₀ a x _ha haa hx
  rw [norm_kernel j a hx]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx _)
  exact Real.exp_le_exp.mpr (by nlinarith)

lemma moment_bound (j : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    moment j a x ≤ (j.factorial : ℝ) * (2 / a) ^ j * Real.exp (-(a / 2) * x) := by
  have h := mul_le_mul_of_nonneg_right (polynomial_bound j ha hx) (Real.exp_pos (-a*x)).le
  calc
    moment j a x ≤ ((j.factorial : ℝ) * (2 / a) ^ j * Real.exp (a*x/2)) *
        Real.exp (-a*x) := h
    _ = _ := by
      rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
      congr 2
      ring

lemma integrable_moment (j : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (moment j a) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (show -(a/2) < 0 by linarith) 0).const_mul
    ((j.factorial : ℝ) * (2/a)^j)
  apply hi.mono' (continuous_moment j a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ moment j a x by
    exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le)]
  exact moment_bound j ha hx.le

lemma integrable_kernel (j : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (kernel j a) (Ioi 0) := by
  have he : kernel j a = fun x => (-1 : ℝ) ^ j * moment j a x :=
    funext (kernel_eq_signed_moment j a)
  rw [he]
  exact (integrable_moment j ha).const_mul _

theorem absolute_convergence : Specs.D04.C08.ExponentialTails.absolute_convergenceType := by
  intro j a ha
  refine ⟨integrable_moment j ha, ?_, ?_⟩
  · intro u v huv
    exact SingleVariableAnalysis.ParameterIntegral.real_integrable_of_continuousOn huv
      (continuous_moment j a).continuousOn
  · exact ⟨_, proper_tendsto (continuous_kernel j a).norm (integrable_kernel j ha).norm⟩

theorem uniform_absolute_tails : Specs.D04.C08.ExponentialTails.uniform_absolute_tailsType := by
  intro a₀ ha s ε hε
  have ht (j : ℕ) : ∀ᶠ R : ℝ in atTop,
      (∫ x in Ioi R, moment j a₀ x) < ε :=
    (tendsto_integral_Ioi_zero (f := moment j a₀) tendsto_id).eventually (gt_mem_nhds hε)
  have hall := (eventually_all_finset (Finset.range (s+1))).mpr (fun j _ => ht j)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hall
  refine ⟨max R₀ 0, le_max_right _ _, ?_⟩
  intro R hR T hT a haa j hj
  have hRpos : 0 ≤ R := (le_max_right _ _).trans hR
  rw [proper_eq_intervalIntegral (continuous_kernel j a).norm hT]
  have hb : (∫ x in R..T, ‖kernel j a x‖) ≤ ∫ x in R..T, moment j a₀ x :=
    intervalIntegral.integral_mono_on hT ((continuous_kernel j a).norm.intervalIntegrable _ _)
      ((continuous_moment j a₀).intervalIntegrable _ _)
      (fun x hx => domination j ha haa (hRpos.trans hx.1))
  apply lt_of_le_of_lt hb
  apply lt_of_le_of_lt _ (hR₀ R ((le_max_left _ _).trans hR) j (Finset.mem_range.mpr (by omega)))
  rw [intervalIntegral.integral_of_le hT]
  apply setIntegral_mono_set ((integrable_moment j ha).mono_set (Ioi_subset_Ioi hRpos))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg (hRpos.trans hx.le) _) (Real.exp_pos _).le
  · exact Eventually.of_forall (fun x hx => hx.1)

lemma hasDerivAt_kernel (j : ℕ) (a x : ℝ) :
    HasDerivAt (fun b => kernel j b x) (kernel (j+1) a x) a := by
  have hd := (((hasDerivAt_id a).neg.mul_const x).exp).const_mul ((-x)^j)
  convert hd using 1 <;>
    simp [kernel, pow_succ, mul_assoc, mul_comm, mul_left_comm]

lemma integral_kernel_derivative (j : ℕ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => ∫ x in Ioi (0 : ℝ), kernel j b x)
      (∫ x in Ioi (0 : ℝ), kernel (j+1) a x) a := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun b x => kernel j b x)
    (F' := fun b x => kernel (j+1) b x) (bound := moment (j+1) (a/2))
    (s := Ioi (a/2)) (Ioi_mem_nhds (by linarith : a/2 < a))
    (Eventually.of_forall (fun b => (continuous_kernel j b).aestronglyMeasurable))
    (integrable_kernel j ha) (continuous_kernel (j+1) a).aestronglyMeasurable ?_
    (integrable_moment (j+1) (by linarith : 0 < a/2)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro b hb
    exact domination (j+1) (by linarith : 0 < a/2) hb.le hx.le
  · exact Eventually.of_forall (fun x b _ => hasDerivAt_kernel j b x)

lemma iterated_integral_derivative (j : ℕ) {a : ℝ} (ha : 0 < a) :
    iteratedDeriv j (fun b => ∫ x in Ioi (0 : ℝ), Real.exp (-b*x)) a =
      ∫ x in Ioi (0 : ℝ), kernel j a x := by
  induction j generalizing a with
  | zero => simp [kernel]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv j (fun b => ∫ x in Ioi (0 : ℝ), Real.exp (-b*x)) =ᶠ[𝓝 a]
        fun b => ∫ x in Ioi (0 : ℝ), kernel j b x := by
      filter_upwards [Ioi_mem_nhds ha] with b hb
      exact ih hb
    exact he.deriv_eq.trans (integral_kernel_derivative j ha).deriv

lemma integral_exponential {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-a*x)) = 1/a := by
  simpa using integral_exp_mul_Ioi (show -a < 0 by linarith) 0

theorem improper_differentiation : Specs.D04.C08.ExponentialTails.improper_differentiationType := by
  intro j a ha
  refine ⟨integral_kernel_derivative j ha, iterated_integral_derivative j ha,
    proper_tendsto (continuous_kernel j a) (integrable_kernel j ha), ?_⟩
  have he : (fun b : ℝ => 1 / b) =ᶠ[𝓝 a]
      fun b => ∫ x in Ioi (0 : ℝ), Real.exp (-b*x) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact (integral_exponential hb).symm
  exact (Filter.EventuallyEq.iteratedDeriv_eq j he).trans (iterated_integral_derivative j ha)

lemma integral_kernel_formula (j : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), kernel j a x) =
      (-1 : ℝ)^j * (j.factorial : ℝ) / a^(j+1) := by
  induction j generalizing a with
  | zero => simpa [kernel] using integral_exponential ha
  | succ j ih =>
    have hd := (hasDerivAt_const a ((-1 : ℝ)^j * (j.factorial : ℝ))).div
      (hasDerivAt_pow (j+1) a) (pow_ne_zero _ ha.ne')
    have hv : (0 * a^(j+1) - ((-1 : ℝ)^j * (j.factorial : ℝ)) *
        ((j+1 : ℕ) * a^((j+1)-1))) / (a^(j+1))^2 =
        (-1 : ℝ)^(j+1) * ((j+1).factorial : ℝ) / a^((j+1)+1) := by
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      field_simp
      ring
    have hd' := hd.congr_deriv hv
    have he : (fun b => ∫ x in Ioi (0 : ℝ), kernel j b x) =ᶠ[𝓝 a]
        fun b => (-1 : ℝ)^j * (j.factorial : ℝ) / b^(j+1) := by
      filter_upwards [Ioi_mem_nhds ha] with b hb
      exact ih hb
    exact (integral_kernel_derivative j ha).unique (hd'.congr_of_eventuallyEq he)

lemma integral_moment_formula (j : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), moment j a x) = (j.factorial : ℝ) / a^(j+1) := by
  have he : kernel j a = fun x => (-1 : ℝ)^j * moment j a x :=
    funext (kernel_eq_signed_moment j a)
  have hk := integral_kernel_formula j ha
  rw [he, integral_const_mul] at hk
  apply (mul_left_cancel₀ (pow_ne_zero j (neg_ne_zero.mpr one_ne_zero)))
  calc
    (-1 : ℝ)^j * (∫ x in Ioi (0 : ℝ), moment j a x) =
        (-1 : ℝ)^j * (j.factorial : ℝ) / a^(j+1) := hk
    _ = _ := by ring

theorem moment_formula : Specs.D04.C08.ExponentialTails.moment_formulaType := by
  intro j a ha
  refine ⟨integral_moment_formula j ha, ?_⟩
  rw [← integral_moment_formula j ha]
  exact proper_tendsto (continuous_moment j a) (integrable_moment j ha)

theorem endpoint_convention : Specs.D04.C08.ExponentialTails.endpoint_conventionType := by
  intro j a _ha
  refine ⟨integral_Ici_eq_integral_Ioi, ?_⟩
  have hf := continuous_moment j a
  have hd := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ))
    (hf.intervalIntegrable 0 0) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have ht : Tendsto (fun δ => ∫ x in (0 : ℝ)..δ, moment j a x) (𝓝[≥] 0) (𝓝 0) := by
    simpa using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (proper_eq_intervalIntegral hf hδ).symm

end D04.ExponentialTails
