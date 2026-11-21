import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.LaplaceLocal
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.LaplaceLocalization
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Substitution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace SingleVariableAnalysis.LaplaceLocal
open Set Filter MeasureTheory
open scoped Topology

/-- On the whole compact interval the phase has a positive quadratic lower
bound. Away from the minimum, compactness replaces the local Taylor bound. -/
theorem quadratic_lower_bound (φ : ℝ → ℝ) {a b x₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Icc a b)) (hx : x₀ ∈ Ioo a b)
    (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x)
    (hd : 0 < deriv (deriv φ) x₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc a b, c * (x-x₀)^2 ≤ φ x - φ x₀ := by
  obtain ⟨r, hr, _, _, hl⟩ := LaplaceLocalization.localLower φ a b x₀ hφ hx hmin hd
  obtain ⟨η, hη, he⟩ := LaplaceLocalization.exteriorGap φ a b x₀ hφ.continuousOn hx hmin r hr
  have hab : 0 < b-a := sub_pos.mpr (hx.1.trans hx.2)
  let c := min (deriv (deriv φ) x₀ / 4) (η / (b-a)^2)
  refine ⟨c, lt_min (by positivity) (by positivity), fun x hxi => ?_⟩
  by_cases hn : |x-x₀| ≤ r
  · have hh := hl (x-x₀) hn
    simp only [add_sub_cancel] at hh
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans hh
  · have hgap := he x hxi (le_of_not_ge hn)
    have hb : |x-x₀| ≤ b-a := by
      rw [abs_le]
      constructor <;> linarith [hxi.1, hxi.2, hx.1, hx.2]
    have hs : (x-x₀)^2 ≤ (b-a)^2 := by nlinarith [sq_abs (x-x₀), abs_nonneg (x-x₀)]
    calc
      c * (x-x₀)^2 ≤ (η / (b-a)^2) * (x-x₀)^2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ ≤ (η / (b-a)^2) * (b-a)^2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = η := div_mul_cancel₀ _ (by positivity)
      _ ≤ φ x - φ x₀ := by linarith

/-- Taylor's punctured remainder quotient extends by zero at the origin. -/
theorem remainder_quotient (φ : ℝ → ℝ) {a b x₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Icc a b)) (hx : x₀ ∈ Ioo a b)
    (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) :
    Tendsto (fun h : ℝ =>
      (φ (x₀+h) - φ x₀ - deriv (deriv φ) x₀ * h^2 / 2) / h^2)
      (𝓝 0) (𝓝 0) := by
  nth_rw 1 [← nhdsNE_sup_pure (0 : ℝ)]
  rw [tendsto_sup]
  exact ⟨(LaplaceLocalization.quadraticPeano φ a b x₀ hφ hx hmin).tendsto_div_nhds_zero,
    by
      convert tendsto_pure_nhds (fun h : ℝ =>
        (φ (x₀+h) - φ x₀ - deriv (deriv φ) x₀ * h^2 / 2) / h^2) (0 : ℝ) using 1 <;>
        norm_num⟩

/-- The exponent at a fixed rescaled point tends to the quadratic exponent. -/
theorem rescaled_phase (φ : ℝ → ℝ) {a b x₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Icc a b)) (hx : x₀ ∈ Ioo a b)
    (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) (y : ℝ) :
    Tendsto (fun t : ℝ => t * (φ (x₀+y/Real.sqrt t) - φ x₀)) atTop
      (𝓝 (deriv (deriv φ) x₀ * y^2 / 2)) := by
  have hh : Tendsto (fun t : ℝ => y / Real.sqrt t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have he := ((remainder_quotient φ hφ hx hmin).comp hh).mul_const (y^2)
  have ht := he.add_const (deriv (deriv φ) x₀ * y^2 / 2)
  simp only [zero_mul, zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsq := Real.sq_sqrt ht.le
  by_cases hy : y = 0
  · simp [hy]
  · dsimp only [Function.comp_apply]
    rw [div_pow, hsq]
    field_simp
    ring

/-- The rescaled interval is precisely the inverse image of the original one. -/
theorem mem_rescaled {a b x₀ t y : ℝ} (ht : 0 < t) :
    y ∈ Icc (Real.sqrt t * (a-x₀)) (Real.sqrt t * (b-x₀)) ↔
      x₀ + y / Real.sqrt t ∈ Icc a b := by
  have hs := Real.sqrt_pos.mpr ht
  constructor
  · intro h
    have hl := (le_div_iff₀ hs).mpr (by simpa [mul_comm] using h.1)
    have hr := (div_le_iff₀ hs).mpr (by simpa [mul_comm] using h.2)
    constructor <;> linarith
  · intro h
    constructor
    · simpa [mul_comm] using (le_div_iff₀ hs).mp (by linarith [h.1] : a-x₀ ≤ y/Real.sqrt t)
    · simpa [mul_comm] using (div_le_iff₀ hs).mp (by linarith [h.2] : y/Real.sqrt t ≤ b-x₀)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extend each rescaled proper integrand by zero outside its moving interval. -/
def rescaledIntegrand (φ : ℝ → ℝ) (g : ℝ → E) (a b x₀ t : ℝ) : ℝ → E :=
  (Icc (Real.sqrt t * (a-x₀)) (Real.sqrt t * (b-x₀))).indicator
    (fun y => Real.exp (-t * (φ (x₀+y/Real.sqrt t) - φ x₀)) •
      g (x₀+y/Real.sqrt t))

/-- All fixed rescaled points eventually lie in the expanding interval. -/
theorem eventually_mem_rescaled {a b x₀ : ℝ} (hx : x₀ ∈ Ioo a b) (y : ℝ) :
    ∀ᶠ t : ℝ in atTop,
      y ∈ Icc (Real.sqrt t * (a-x₀)) (Real.sqrt t * (b-x₀)) := by
  have hh : Tendsto (fun t : ℝ => x₀+y/Real.sqrt t) atTop (𝓝 x₀) := by
    simpa using ((tendsto_const_nhds (x := y)).div_atTop
      Real.tendsto_sqrt_atTop).const_add x₀
  filter_upwards [eventually_gt_atTop (0 : ℝ), hh.eventually (Icc_mem_nhds hx.1 hx.2)] with t ht hm
  exact (mem_rescaled ht).mpr hm

/-- Pointwise convergence needs only continuity of the amplitude, including
when its value at the minimum is zero. -/
theorem rescaled_pointwise (φ : ℝ → ℝ) (g : ℝ → E) {a b x₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hx : x₀ ∈ Ioo a b)
    (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) (y : ℝ) :
    Tendsto (fun t : ℝ => rescaledIntegrand φ g a b x₀ t y) atTop
      (𝓝 (Real.exp (-(deriv (deriv φ) x₀ / 2) * y^2) • g x₀)) := by
  have hh : Tendsto (fun t : ℝ => x₀+y/Real.sqrt t) atTop (𝓝 x₀) := by
    simpa using ((tendsto_const_nhds (x := y)).div_atTop
      Real.tendsto_sqrt_atTop).const_add x₀
  have he := (rescaled_phase φ hφ hx hmin y).neg.rexp
  have hgc := hg.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have h := he.smul (hgc.tendsto.comp hh)
  have htarget : -(deriv (deriv φ) x₀ * y^2 / 2) =
      -(deriv (deriv φ) x₀ / 2) * y^2 := by ring
  rw [htarget] at h
  apply h.congr'
  filter_upwards [eventually_mem_rescaled hx y] with t ht
  change Real.exp (-(t * (φ (x₀+y/Real.sqrt t) - φ x₀))) •
    g (x₀+y/Real.sqrt t) = rescaledIntegrand φ g a b x₀ t y
  simp only [rescaledIntegrand, indicator_of_mem ht, neg_mul]

/-- A single integrable Gaussian controls every positive parameter. -/
theorem rescaled_bound (φ : ℝ → ℝ) (g : ℝ → E) {a b x₀ c M t : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc a b, ‖g x‖ ≤ M)
    (hq : ∀ x ∈ Icc a b, c * (x-x₀)^2 ≤ φ x - φ x₀)
    (ht : 0 < t) (y : ℝ) :
    ‖rescaledIntegrand φ g a b x₀ t y‖ ≤ M * Real.exp (-c * y^2) := by
  by_cases hy : y ∈ Icc (Real.sqrt t * (a-x₀)) (Real.sqrt t * (b-x₀))
  · rw [rescaledIntegrand, indicator_of_mem hy, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hm := (mem_rescaled ht).mp hy
    have hsq := Real.sq_sqrt ht.le
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    have hid : t * (y / Real.sqrt t)^2 = y^2 := by
      rw [div_pow, hsq]
      field_simp
    have hqq := mul_le_mul_of_nonneg_left (hq _ hm) ht.le
    simp only [add_sub_cancel_left] at hqq
    have he : Real.exp (-t * (φ (x₀+y/Real.sqrt t) - φ x₀)) ≤
        Real.exp (-c * y^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hid]
    calc
      _ ≤ Real.exp (-c*y^2) * M := mul_le_mul he (hb _ hm) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · simp only [rescaledIntegrand, indicator_of_notMem hy, norm_zero]
    positivity

/-- The continuous proper integral limit, after Gaussian rescaling. -/
theorem rescaled_integral_limit [CompleteSpace E] (φ : ℝ → ℝ) (g : ℝ → E) {a b x₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hx : x₀ ∈ Ioo a b)
    (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x)
    (hd : 0 < deriv (deriv φ) x₀) :
    Tendsto (fun t : ℝ => ∫ y, rescaledIntegrand φ g a b x₀ t y) atTop
      (𝓝 (Real.sqrt (2 * Real.pi / deriv (deriv φ) x₀) • g x₀)) := by
  obtain ⟨c, hc, hq⟩ := quadratic_lower_bound φ hφ hx hmin hd
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨x₀, hx.1.le, hx.2.le⟩) hg.norm
  let M := ‖g z‖
  have hm (t : ℝ) (ht : 0 < t) : AEStronglyMeasurable (rescaledIntegrand φ g a b x₀ t) := by
    apply (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
    have hmap : MapsTo (fun y : ℝ => x₀+y/Real.sqrt t)
        (Icc (Real.sqrt t*(a-x₀)) (Real.sqrt t*(b-x₀))) (Icc a b) :=
      fun y hy => (mem_rescaled ht).mp hy
    have hcont : Continuous (fun y : ℝ => x₀+y/Real.sqrt t) := by fun_prop
    exact ((((hφ.continuousOn.comp hcont.continuousOn hmap).sub continuousOn_const).const_mul (-t)).rexp.smul
      (hg.comp hcont.continuousOn hmap)).aestronglyMeasurable measurableSet_Icc
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => M * Real.exp (-c*y^2))
    ((eventually_gt_atTop (0 : ℝ)).mono fun t ht => hm t ht)
    ((eventually_gt_atTop (0 : ℝ)).mono fun t ht => ae_of_all _ fun y =>
      rescaled_bound φ g hc (norm_nonneg _) (fun x hxi => hmax hxi) hq ht y)
    ((integrable_exp_neg_mul_sq hc).const_mul M)
    (ae_of_all _ fun y => rescaled_pointwise φ g hφ hg hx hmin y)
  rw [integral_smul_const, integral_gaussian] at hlim
  convert hlim using 1
  congr 2
  field_simp

/-- Exact affine substitution and cancellation of the exponential normalizer. -/
theorem rescaled_integral_eq (φ : ℝ → ℝ) (g : ℝ → E) {a b x₀ t : ℝ}
    (hab : a ≤ b) (ht : 0 < t) :
    (∫ y, rescaledIntegrand φ g a b x₀ t y) =
      (Real.sqrt t * Real.exp (t * φ x₀)) •
        (∫ x in a..b, Real.exp (-t * φ x) • g x) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have horder : Real.sqrt t*(a-x₀) ≤ Real.sqrt t*(b-x₀) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hab _) (Real.sqrt_nonneg _)
  rw [rescaledIntegrand, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder]
  let f : ℝ → E := fun x => Real.exp (-t * (φ x - φ x₀)) • g x
  change (∫ y in Real.sqrt t*(a-x₀)..Real.sqrt t*(b-x₀), f (x₀+y/Real.sqrt t)) = _
  rw [intervalIntegral.integral_comp_add_div f hs x₀]
  have ha : x₀ + Real.sqrt t*(a-x₀)/Real.sqrt t = a := by field_simp; ring
  have hb : x₀ + Real.sqrt t*(b-x₀)/Real.sqrt t = b := by field_simp; ring
  rw [ha, hb]
  have he : f = fun x => Real.exp (t * φ x₀) • (Real.exp (-t * φ x) • g x) := by
    funext x
    dsimp [f]
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [he, intervalIntegral.integral_smul, smul_smul]

open Riemann
local notation "S" => Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.scalarRCLike

/-- Only continuous proper integrals are compared with the measure API.
The Darboux Newton–Leibniz theorem establishes the value bridge. -/
theorem scalar_darboux_bridge (k : ScalarKind) :
    letI := S k;
    ∀ (f : ℝ → Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue k)
      {a b : ℝ}, a ≤ b → ContinuousOn f (Icc a b) →
      ∀ h : Integrable k f a b, integral k f h = ∫ x in a..b, f x := by
  letI := S k
  intro f a b hab hf h
  obtain ⟨f', hc, he⟩ := continuous_extension_from_Icc hab hf
  let F : ℝ → Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue k :=
    fun y => ∫ x in a..y, f' x
  have hder (x : ℝ) : HasDerivAt F (f' x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hder x).continuousAt
  have hder' (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt F (f x) x := by
    rw [← he ⟨hx.1.le, hx.2.le⟩]
    exact hder x
  have hv : integral k f h = F b - F a := by
    cases k with
    | real => exact real_ftc_second F f a b hab hF.continuousOn hder' h
    | complex => exact complex_ftc_second F f a b hab hF.continuousOn hder' h
  have hval : F b - F a = ∫ x in a..b, f' x := by simp [F]
  exact hv.trans (hval.trans (intervalIntegral.integral_congr (by simpa only [uIcc_of_le hab] using he)))

/-- Leading Laplace asymptotic as a normalized limit for both canonical
scalars, with existence of the proper Darboux integrals. -/
theorem normalized_limit : Specs.SingleVariableAnalysis.Ch17.LaplaceLocal.normalizedLimit := by
  intro k
  letI := S k
  intro φ g a b x₀ hab hφ hg hx hmin hd
  have hf (t : ℝ) : ContinuousOn (fun x => Real.exp (-t * φ x) • g x) (Icc a b) :=
    ((hφ.continuousOn.const_mul (-t)).rexp).smul hg
  let h := fun t : ℝ => LaplaceLocalization.scalar_continuous_integrable k
    (fun x => Real.exp (-t * φ x) • g x) a b hab.le (hf t)
  refine ⟨h, ?_⟩
  apply (rescaled_integral_limit φ g hφ hg hx hmin hd).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [rescaled_integral_eq φ g hab.le ht]
  congr 1
  exact (scalar_darboux_bridge k _ hab.le (hf t) (h t)).symm

end SingleVariableAnalysis.LaplaceLocal
