import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory Filter Set
open scoped SchwartzMap FourierTransform Topology

noncomputable section
namespace ExpandedFA.SingularIntegrals

/-- The ordinary integral with a symmetric interval removed around zero. -/
def symmetricTruncation (ε : ℝ) (φ : LineSchwartz) : ℂ :=
  ∫ x in {x : ℝ | ε < |x|}, φ x / (x : ℂ)

/-- The symmetric principal-value pairing; convergence is proved below. -/
def principalValuePairing (φ : LineSchwartz) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => symmetricTruncation ε φ)

namespace PrincipalValue

/-- Subtracting the test value removes the singularity in a norm estimate. -/
theorem difference_quotient_bound (φ : LineSchwartz) (x : ℝ) :
    ‖(φ x - φ 0) / (x : ℂ)‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ := by
  have hd : ∀ y : ℝ, ‖deriv φ y‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ := by
    intro y
    simpa using SchwartzMap.le_seminorm' ℂ 0 1 φ y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (Set.univ : Set ℝ)) (fun y _ => φ.differentiableAt)
    (fun y _ => hd y) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (x := 0) (y := x) (mem_univ _) (mem_univ _)
  by_cases hx : x = 0
  · simp [hx]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (abs_pos.mpr hx)).mpr
    simpa using h

/-- The near-origin compensated integrand is Lebesgue integrable. -/
theorem near_integrable (φ : LineSchwartz) :
    IntegrableOn (fun x : ℝ => (φ x - φ 0) / (x : ℂ)) (Icc (-1) 1) := by
  apply Integrable.mono' (g := fun _ : ℝ => SchwartzMap.seminorm ℂ 0 1 φ)
    (integrableOn_const (by simp))
  · exact ((φ.continuous.measurable.sub measurable_const).div
      Complex.measurable_ofReal).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (difference_quotient_bound φ)

/-- Multiplication by a measurable uniformly bounded kernel remains integrable
against every Schwartz test. No smoothness of the kernel is assumed. -/
theorem bounded_kernel_integrable (k : ℝ → ℂ) (hk : Measurable k)
    {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) (φ : LineSchwartz) :
    Integrable (fun x => k x * φ x) :=
  φ.integrable.bdd_mul hk.aestronglyMeasurable (Eventually.of_forall hB)

/-- Bounded measurable kernels define actual continuous linear functionals. -/
def boundedKernel (k : ℝ → ℂ) (hk : Measurable k)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖k x‖ ≤ B) : LineTempered := by
  refine SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun φ => ∫ x, k x * φ x) ?_ ?_ ?_
  · intro φ ψ
    simp only [add_apply, mul_add]
    exact integral_add (bounded_kernel_integrable k hk hbound φ)
      (bounded_kernel_integrable k hk hbound ψ)
  · intro c φ
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x, k x * (c * φ x) = c * (k x * φ x) by intro x; ring]
    exact integral_const_mul c _
  · let μ : Measure ℝ := volume
    let n := μ.integrablePower
    let C := 2 ^ n * ∫ x : ℝ, (1 + ‖x‖) ^ (-(n : ℝ))
    refine ⟨{(0, 0), (n, 0)}, B * C * 2, by dsimp [C]; positivity, ?_⟩
    intro φ
    have hnorm : (∫ x : ℝ, ‖k x * φ x‖) ≤ B * ∫ x : ℝ, ‖φ x‖ := by
      rw [← integral_const_mul]
      exact integral_mono (bounded_kernel_integrable k hk hbound φ).norm
        (φ.integrable.norm.const_mul B) (fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))
    have h := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ volume φ 0 0
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, zero_add] at h
    have h₀ : SchwartzMap.seminorm ℂ 0 0 φ ≤
        ({(0, 0), (n, 0)} : Finset (ℕ × ℕ)).sup
          (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
      exact Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) (by simp : (0, 0) ∈
        ({(0, 0), (n, 0)} : Finset (ℕ × ℕ)))) φ
    have hₙ : SchwartzMap.seminorm ℂ n 0 φ ≤
        ({(0, 0), (n, 0)} : Finset (ℕ × ℕ)).sup
          (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
      exact Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) (by simp : (n, 0) ∈
        ({(0, 0), (n, 0)} : Finset (ℕ × ℕ)))) φ
    calc
      ‖∫ x, k x * φ x‖ ≤ ∫ x, ‖k x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ B * ∫ x, ‖φ x‖ := hnorm
      _ ≤ B * (C * (SchwartzMap.seminorm ℂ 0 0 φ + SchwartzMap.seminorm ℂ n 0 φ)) :=
        mul_le_mul_of_nonneg_left h hB
      _ ≤ B * (C * (2 * ({(0, 0), (n, 0)} : Finset (ℕ × ℕ)).sup
          (schwartzSeminormFamily ℂ ℝ ℂ) φ)) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
        linarith
      _ = _ := by ring

/-- The nonsingular tail of 1/x. -/
def tailKernel (x : ℝ) : ℂ := if 1 < |x| then (x : ℂ)⁻¹ else 0

theorem tailKernel_measurable : Measurable tailKernel := by
  exact Complex.measurable_ofReal.inv.ite
    (measurableSet_lt measurable_const continuous_abs.measurable) measurable_const

theorem tailKernel_bound (x : ℝ) : ‖tailKernel x‖ ≤ 1 := by
  unfold tailKernel
  split_ifs with h
  · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact inv_le_one_of_one_le₀ h.le
  · simp

theorem tail_integrable (φ : LineSchwartz) : Integrable (fun x => tailKernel x * φ x) :=
  bounded_kernel_integrable _ tailKernel_measurable tailKernel_bound φ

theorem compensated_integrable :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.compensatedIntegrabilityType := by
  intro φ
  have hn := (near_integrable φ).integrable_indicator measurableSet_Icc
  have ht := tail_integrable φ
  convert hn.add ht using 1
  ext x
  by_cases h : |x| ≤ 1
  · have hx : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp h
    simp [hx, tailKernel, not_lt.mpr h, h, div_eq_mul_inv]
  · have hx : x ∉ Icc (-1 : ℝ) 1 := by simpa [← abs_le] using h
    simp [hx, tailKernel, lt_of_not_ge h, h, div_eq_mul_inv, mul_comm]

/-- The compact near-origin part is continuous for the first-derivative seminorm. -/
def nearFunctional : LineTempered := by
  refine SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun φ => ∫ x in Icc (-1 : ℝ) 1, (φ x - φ 0) / (x : ℂ)) ?_ ?_ ?_
  · intro φ ψ
    have h : (fun x : ℝ => ((φ + ψ) x - (φ + ψ) 0) / (x : ℂ)) =
        (fun x => (φ x - φ 0) / (x : ℂ) + (ψ x - ψ 0) / (x : ℂ)) := by
      ext x; simp only [add_apply]; ring
    rw [h, integral_add (near_integrable φ) (near_integrable ψ)]
  · intro c φ
    have h : (fun x : ℝ => ((c • φ) x - (c • φ) 0) / (x : ℂ)) =
        (fun x => c * ((φ x - φ 0) / (x : ℂ))) := by
      ext x; simp only [smul_apply, smul_eq_mul]; ring
    simpa only [RingHom.id_apply, smul_eq_mul] using congrArg
      (fun f : ℝ → ℂ => ∫ x in Icc (-1 : ℝ) 1, f x) h |>.trans (integral_const_mul c _)
  · refine ⟨{(0, 1)}, 2, by norm_num, ?_⟩
    intro φ
    have h := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Icc (-1 : ℝ) 1)
      (by simp) (fun x _ => difference_quotient_bound φ x)
    simpa [Real.volume_Icc, schwartzSeminormFamily, Finset.sup_singleton, mul_comm, ← two_mul] using h

/-- The compensated principal-value integral as a continuous linear functional. -/
def compensatedFunctional : LineTempered :=
  nearFunctional + boundedKernel tailKernel tailKernel_measurable 1 (by norm_num) tailKernel_bound

theorem compensatedFunctional_apply (φ : LineSchwartz) :
    compensatedFunctional φ = compensatedPairing φ := by
  change (∫ x in Icc (-1 : ℝ) 1, (φ x - φ 0) / (x : ℂ)) +
    (∫ x : ℝ, tailKernel x * φ x) = _
  rw [← integral_indicator measurableSet_Icc,
    ← integral_add ((near_integrable φ).integrable_indicator measurableSet_Icc) (tail_integrable φ)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases h : |x| ≤ 1
  · have hx : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp h
    simp [hx, tailKernel, not_lt.mpr h, h]
  · have hx : x ∉ Icc (-1 : ℝ) 1 := by simpa [← abs_le] using h
    simp [hx, tailKernel, lt_of_not_ge h, h, div_eq_mul_inv, mul_comm]

/-- Odd integrands have zero integral, including Lean's nonintegrable convention. -/
theorem integral_odd (g : ℝ → ℂ) (hg : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have h := integral_neg_eq_self g volume
  simp only [hg, integral_neg] at h
  linear_combination -h / 2

/-- Every positive symmetric truncation is an ordinary absolutely convergent integral. -/
theorem truncation_integrable (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    IntegrableOn (fun x : ℝ => φ x / (x : ℂ)) {x : ℝ | ε < |x|} := by
  apply Integrable.mono' (g := fun x : ℝ => ε⁻¹ * ‖φ x‖)
    ((φ.integrable.norm.const_mul ε⁻¹).restrict)
  · exact (φ.continuous.measurable.div Complex.measurable_ofReal).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const continuous_abs.measurable)] with x hx
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε (le_of_lt hx)) (norm_nonneg _)

/-- Symmetric cancellation of the subtracted constant, before taking any limit. -/
theorem truncation_compensated (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    symmetricTruncation ε φ =
      ∫ x in {x : ℝ | ε < |x|},
        (if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ) := by
  let s := {x : ℝ | ε < |x|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const continuous_abs.measurable
  let f : ℝ → ℂ := fun x => (if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ)
  let g : ℝ → ℂ := fun x => if ε < |x| ∧ |x| ≤ 1 then φ 0 / (x : ℂ) else 0
  have hg : ∫ x, g x = 0 := integral_odd g (by
    intro x
    dsimp [g]
    simp only [abs_neg, Complex.ofReal_neg]
    split_ifs <;> simp [div_neg])
  apply sub_eq_zero.mp
  change (∫ x in s, φ x / (x : ℂ)) - ∫ x in s, f x = 0
  rw [← integral_sub (truncation_integrable ε hε φ) ((compensated_integrable φ).integrableOn),
    ← integral_indicator hs]
  calc
    (∫ x, s.indicator (fun x => φ x / (x : ℂ) - f x) x) = ∫ x, g x := by
      congr 1
      ext x
      dsimp [s, f, g]
      by_cases hx : ε < |x| <;> by_cases hy : |x| ≤ 1 <;>
        simp [hx, hy, sub_div]
    _ = 0 := hg

/-- Dominated convergence applies after the symmetric cancellation. -/
theorem truncation_tendsto_compensated (φ : LineSchwartz) :
    Tendsto (fun ε => symmetricTruncation ε φ) (𝓝[>] (0 : ℝ))
      (𝓝 (compensatedPairing φ)) := by
  let f : ℝ → ℂ := fun x => (if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ)
  have hf : Integrable f := compensated_integrable φ
  have hs (ε : ℝ) : MeasurableSet {x : ℝ | ε < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hc : Tendsto (fun ε : ℝ => ∫ x, {x : ℝ | ε < |x|}.indicator f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    · exact Eventually.of_forall (fun ε => (hf.indicator (hs ε)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun ε => Eventually.of_forall (fun x => by
        by_cases hx : ε < |x| <;> simp [hx]))
    · exact hf.norm
    · have hzero : ∀ᵐ x : ℝ, x ≠ 0 := by
        apply ae_iff.mpr
        simp
      filter_upwards [hzero] with x hx
      have hlt : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < |x| :=
        (eventually_lt_nhds (abs_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [hlt] with ε hε
      simp [hε]
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [integral_indicator (hs ε)]
  exact (truncation_compensated ε hε φ).symm

theorem compensated_formula :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.compensatedFormulaType := by
  intro φ
  exact (truncation_tendsto_compensated φ).limUnder_eq

theorem symmetric_limit :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.symmetricLimitType := by
  intro φ
  rw [compensated_formula φ]
  exact truncation_tendsto_compensated φ

theorem temperedness :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.temperednessType := by
  refine ⟨compensatedFunctional, fun φ => ?_⟩
  rw [compensatedFunctional_apply, compensated_formula φ]

/-- Check the real-line native transform against the source's explicit 2π kernel. -/
theorem fourier_normalization :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.fourierNormalizationType := by
  intro φ ξ
  rw [FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- Real and imaginary kernels in the half-plane boundary-value decomposition. -/
def realBoundaryKernel (ε x : ℝ) : ℝ := x / (x ^ 2 + ε ^ 2)
def poissonKernel (ε x : ℝ) : ℝ := ε / (x ^ 2 + ε ^ 2)
def regularizingFactor (ε x : ℝ) : ℝ := x ^ 2 / (x ^ 2 + ε ^ 2)

theorem regularizingFactor_bounds (ε x : ℝ) :
    0 ≤ regularizingFactor ε x ∧ regularizingFactor ε x ≤ 1 := by
  unfold regularizingFactor
  constructor
  · positivity
  · exact div_le_one_of_le₀ (le_add_of_nonneg_right (sq_nonneg ε)) (by positivity)

theorem realBoundaryKernel_bound (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    |realBoundaryKernel ε x| ≤ ε⁻¹ := by
  have hd : 0 < x ^ 2 + ε ^ 2 := by positivity
  rw [realBoundaryKernel, abs_div, abs_of_pos hd, inv_eq_one_div, div_le_div_iff₀ hd hε]
  nlinarith [sq_nonneg (|x| - ε), sq_abs x]

theorem real_boundary_integrable (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    Integrable (fun x => (realBoundaryKernel ε x : ℂ) * φ x) := by
  apply bounded_kernel_integrable (B := ε⁻¹)
  · unfold realBoundaryKernel; fun_prop
  · intro x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using realBoundaryKernel_bound ε hε x

theorem regularized_integrable (ε : ℝ) (φ : LineSchwartz) :
    Integrable (fun x : ℝ => (regularizingFactor ε x : ℂ) *
      ((if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ))) := by
  apply (compensated_integrable φ).bdd_mul (c := 1)
  · exact (Complex.measurable_ofReal.comp
      ((measurable_id.pow_const 2).div
        ((measurable_id.pow_const 2).add measurable_const))).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (regularizingFactor_bounds ε x).1]
      exact (regularizingFactor_bounds ε x).2)

/-- Oddness again cancels the constant part of the real boundary kernel. -/
theorem real_boundary_compensated (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    (∫ x : ℝ, (realBoundaryKernel ε x : ℂ) * φ x) =
      ∫ x : ℝ, (regularizingFactor ε x : ℂ) *
        ((if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ)) := by
  apply sub_eq_zero.mp
  rw [← integral_sub (real_boundary_integrable ε hε φ) (regularized_integrable ε φ)]
  apply integral_odd
  intro x
  have hd : (x : ℂ) ^ 2 + (ε : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < x ^ 2 + ε ^ 2 by positivity))
  dsimp [realBoundaryKernel, regularizingFactor]
  push_cast
  simp only [abs_neg, neg_sq]
  by_cases hx : x = 0
  · simp [hx]
  · have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    split_ifs <;> field_simp <;> ring

/-- The real part converges to the symmetric principal-value pairing. -/
theorem real_boundary_limit (φ : LineSchwartz) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, (realBoundaryKernel ε x : ℂ) * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (principalValuePairing φ)) := by
  have hformula := compensated_formula φ
  change principalValuePairing φ = compensatedPairing φ at hformula
  rw [hformula]
  let f : ℝ → ℂ := fun x => (if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ)
  have hf : Integrable f := compensated_integrable φ
  have hc : Tendsto (fun ε : ℝ => ∫ x : ℝ, (regularizingFactor ε x : ℂ) * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    · exact Eventually.of_forall (fun ε => (regularized_integrable ε φ).aestronglyMeasurable)
    · exact Eventually.of_forall (fun ε => Eventually.of_forall (fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (regularizingFactor_bounds ε x).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (regularizingFactor_bounds ε x).2))
    · exact hf.norm
    · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
      have hd : x ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
      have hcont : ContinuousAt (fun ε : ℝ => (regularizingFactor ε x : ℂ) * f x) 0 := by
        unfold regularizingFactor
        exact (Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_const.div (continuousAt_const.add (continuousAt_id.pow 2)) hd)).mul continuousAt_const
      simpa [regularizingFactor, hx] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (real_boundary_compensated ε hε φ).symm

/-- Under scaling, the Poisson kernel has the fixed integrable majorant 1/(1+y²). -/
theorem poisson_scaled_limit (φ : LineSchwartz) :
    Tendsto (fun ε : ℝ => ∫ y : ℝ, ((1 + y ^ 2)⁻¹ : ℝ) • φ (ε * y))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ) * φ 0)) := by
  have hi : Integrable (fun y : ℝ => (1 + y ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hlim : Tendsto (fun ε : ℝ => ∫ y : ℝ, ((1 + y ^ 2)⁻¹ : ℝ) • φ (ε * y))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ y : ℝ, ((1 + y ^ 2)⁻¹ : ℝ) • φ 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => (1 + y ^ 2)⁻¹ * SchwartzMap.seminorm ℂ 0 0 φ)
    · exact Eventually.of_forall (fun ε => by fun_prop)
    · exact Eventually.of_forall (fun ε => Eventually.of_forall (fun y => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ _) (by positivity)))
    · exact hi.mul_const _
    · exact Eventually.of_forall (fun y => by
        have h : ContinuousAt (fun ε : ℝ => ((1 + y ^ 2)⁻¹ : ℝ) • φ (ε * y)) 0 := by fun_prop
        simpa using h.tendsto.mono_left nhdsWithin_le_nhds)
  rw [integral_smul_const, integral_univ_inv_one_add_sq] at hlim
  simpa only [Complex.real_smul] using hlim

/-- Exact change of variables for the Cauchy approximate identity. -/
theorem poisson_scaling (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    (∫ x : ℝ, (poissonKernel ε x : ℂ) * φ x) =
      ∫ y : ℝ, ((1 + y ^ 2)⁻¹ : ℝ) • φ (ε * y) := by
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => (poissonKernel ε x : ℂ) * φ x) ε
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have heq : (fun y : ℝ => (poissonKernel ε (ε * y) : ℂ) * φ (ε * y)) =
      fun y => ε⁻¹ • (((1 + y ^ 2)⁻¹ : ℝ) • φ (ε * y)) := by
    ext y
    have hd : ((1 : ℂ) + (y : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0 < 1 + y ^ 2 by positivity))
    simp only [poissonKernel, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_one]
    field_simp [hεc, hd]
    ring_nf
    field_simp [hd]
    ring
  rw [heq, integral_smul, abs_of_pos (inv_pos.mpr hε)] at h
  have hh := congrArg (fun z : ℂ => ε • z) h
  simpa [smul_smul, hε.ne'] using hh.symm

theorem poisson_limit (φ : LineSchwartz) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, (poissonKernel ε x : ℂ) * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ) * φ 0)) := by
  apply (poisson_scaled_limit φ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (poisson_scaling ε hε φ).symm

theorem poissonKernel_bound (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    |poissonKernel ε x| ≤ ε⁻¹ := by
  have hd : 0 < x ^ 2 + ε ^ 2 := by positivity
  rw [poissonKernel, abs_div, abs_of_pos hε, abs_of_pos hd,
    inv_eq_one_div, div_le_div_iff₀ hd hε]
  nlinarith [sq_nonneg x]

theorem poisson_integrable (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    Integrable (fun x => (poissonKernel ε x : ℂ) * φ x) := by
  apply bounded_kernel_integrable (B := ε⁻¹)
  · unfold poissonKernel; fun_prop
  · intro x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using poissonKernel_bound ε hε x

theorem boundary_kernel_bound (s : ℝ) (hs : s = 1 ∨ s = -1)
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    ‖((x : ℂ) + (s * ε : ℝ) * Complex.I)⁻¹‖ ≤ ε⁻¹ := by
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [norm_inv]
  apply inv_anti₀ hε
  have h := Complex.abs_im_le_norm ((x : ℂ) + (s * ε : ℝ) * Complex.I)
  simpa [abs_mul, hsabs, abs_of_pos hε] using h

theorem boundary_integrable (s : ℝ) (hs : s = 1 ∨ s = -1)
    (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    Integrable (fun x : ℝ => φ x / ((x : ℂ) + (s * ε : ℝ) * Complex.I)) := by
  have hk : Measurable (fun x : ℝ => ((x : ℂ) + (s * ε : ℝ) * Complex.I)⁻¹) := by fun_prop
  simpa only [div_eq_mul_inv, mul_comm] using
    bounded_kernel_integrable _ hk (boundary_kernel_bound s hs ε hε) φ

theorem boundary_tempered (s : ℝ) (hs : s = 1 ∨ s = -1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : LineTempered, ∀ φ : LineSchwartz, T φ = boundaryPairing s ε φ := by
  have hk : Measurable (fun x : ℝ => ((x : ℂ) + (s * ε : ℝ) * Complex.I)⁻¹) := by fun_prop
  refine ⟨boundedKernel _ hk ε⁻¹ (by positivity) (boundary_kernel_bound s hs ε hε), ?_⟩
  intro φ
  change (∫ x : ℝ, ((x : ℂ) + (s * ε : ℝ) * Complex.I)⁻¹ * φ x) = _
  simp only [boundaryPairing, div_eq_mul_inv, mul_comm]

theorem boundary_kernel_decomposition (s : ℝ) (hs : s = 1 ∨ s = -1)
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    ((x : ℂ) + (s * ε : ℝ) * Complex.I)⁻¹ =
      (realBoundaryKernel ε x : ℂ) - (s : ℂ) * Complex.I * (poissonKernel ε x : ℂ) := by
  have hd : (x : ℂ) ^ 2 + (ε : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < x ^ 2 + ε ^ 2 by positivity))
  have hz : (x : ℂ) + (s * ε : ℝ) * Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have hse : s * ε ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hε.ne'
    exact hse (by simpa using him)
  dsimp [realBoundaryKernel, poissonKernel]
  push_cast
  push_cast at hz
  rcases hs with rfl | rfl <;>
    simp only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul] at hz ⊢ <;>
    field_simp [hz, hd] <;> ring_nf <;> simp [Complex.I_sq]

theorem boundary_decomposition (s : ℝ) (hs : s = 1 ∨ s = -1)
    (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    boundaryPairing s ε φ = (∫ x : ℝ, (realBoundaryKernel ε x : ℂ) * φ x) -
      (s : ℂ) * Complex.I * (∫ x : ℝ, (poissonKernel ε x : ℂ) * φ x) := by
  unfold boundaryPairing
  rw [← integral_const_mul, ← integral_sub (real_boundary_integrable ε hε φ)
    ((poisson_integrable ε hε φ).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [div_eq_mul_inv, boundary_kernel_decomposition s hs ε hε x]
  ring

theorem boundary_values :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.boundaryValuesType := by
  intro s hs
  refine ⟨fun ε hε => ⟨fun φ => boundary_integrable s hs ε hε φ,
    boundary_tempered s hs ε hε⟩, fun φ => ?_⟩
  have h := (real_boundary_limit φ).sub ((poisson_limit φ).const_mul ((s : ℂ) * Complex.I))
  simp only [← mul_assoc] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (boundary_decomposition s hs ε hε φ).symm

/-- The exponentially damped sign multiplier. Its value at zero is immaterial. -/
def dampedSign (ε t : ℝ) : ℂ :=
  if t ≤ 0 then Complex.I * Real.pi * Complex.exp ((2 * Real.pi * ε : ℝ) * t)
  else -Complex.I * Real.pi * Complex.exp ((-2 * Real.pi * ε : ℝ) * t)

theorem dampedSign_integrable (ε : ℝ) (hε : 0 < ε) : Integrable (dampedSign ε) := by
  have hpos : 0 < 2 * Real.pi * ε := by positivity
  have hl : IntegrableOn (dampedSign ε) (Iic 0) := by
    apply IntegrableOn.congr_fun ((integrableOn_exp_mul_complex_Iic (a := (2 * Real.pi * ε : ℝ))
      (by simpa using hpos) 0).const_mul (Complex.I * Real.pi))
    · intro t ht
      simp [dampedSign, show t ≤ 0 from ht]
    · exact measurableSet_Iic
  have hr : IntegrableOn (dampedSign ε) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((integrableOn_exp_mul_complex_Ioi (a := (-2 * Real.pi * ε : ℝ))
      (by push_cast; simp; nlinarith [Real.pi_pos]) 0).const_mul (-Complex.I * Real.pi))
    · intro t ht
      simp [dampedSign, not_le.mpr (show 0 < t from ht)]
    · exact measurableSet_Ioi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hl, hr⟩

/-- Inverting the damped multiplier gives the conjugate Poisson kernel. -/
theorem inverse_dampedSign (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    𝓕⁻ (dampedSign ε) x = (realBoundaryKernel ε x : ℂ) := by
  let a : ℂ := 2 * Real.pi * ((ε : ℂ) + Complex.I * x)
  let b : ℂ := 2 * Real.pi * (-(ε : ℂ) + Complex.I * x)
  have ha : 0 < a.re := by dsimp [a]; simp; positivity
  have hb : b.re < 0 := by dsimp [b]; simp; nlinarith [Real.pi_pos]
  have hl : IntegrableOn (fun t : ℝ => Complex.I * Real.pi * Complex.exp (a * t)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic ha 0).const_mul _
  have hr : IntegrableOn (fun t : ℝ => -Complex.I * Real.pi * Complex.exp (b * t)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hb 0).const_mul _
  have heq : (fun t : ℝ => Complex.exp
      ((2 * Real.pi * inner ℝ t x : ℝ) * Complex.I) * dampedSign ε t) =
      (fun t : ℝ => if t ≤ 0 then Complex.I * Real.pi * Complex.exp (a * t)
        else -Complex.I * Real.pi * Complex.exp (b * t)) := by
    ext t
    dsimp [dampedSign]
    split_ifs
    all_goals
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      dsimp [a, b]
      simp only [starRingEnd_apply, star_trivial]
      push_cast
      ring
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul]
  rw [heq]
  have hleft : IntegrableOn (fun t : ℝ => if t ≤ 0 then
      Complex.I * Real.pi * Complex.exp (a * t) else
      -Complex.I * Real.pi * Complex.exp (b * t)) (Iic 0) :=
    IntegrableOn.congr_fun hl (fun t ht => by simp [show t ≤ 0 from ht]) measurableSet_Iic
  have hright : IntegrableOn (fun t : ℝ => if t ≤ 0 then
      Complex.I * Real.pi * Complex.exp (a * t) else
      -Complex.I * Real.pi * Complex.exp (b * t)) (Ioi 0) :=
    IntegrableOn.congr_fun hr (fun t ht => by simp [not_le.mpr (show 0 < t from ht)]) measurableSet_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright]
  rw [setIntegral_congr_fun measurableSet_Iic (fun (t : ℝ) ht => ite_eq_left (show t ≤ 0 from ht)),
      setIntegral_congr_fun measurableSet_Ioi (fun (t : ℝ) ht => ite_eq_right (not_le.mpr (show 0 < t from ht)))]
  rw [integral_const_mul, integral_const_mul, integral_exp_mul_complex_Iic ha,
    integral_exp_mul_complex_Ioi hb]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, mul_neg]
  have han : a ≠ 0 := fun h => by simp [h] at ha
  have hbn : b ≠ 0 := fun h => by simp [h] at hb
  have hd : (x : ℂ) ^ 2 + (ε : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < x ^ 2 + ε ^ 2 by positivity))
  dsimp [realBoundaryKernel]
  push_cast
  apply (eq_div_iff hd).mpr
  field_simp [han, hbn, hd]
  dsimp [a, b]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Absolute Fubini is used only for the integrable damped multiplier. -/
theorem damped_fourier_pairing (ε : ℝ) (hε : 0 < ε) (φ : LineSchwartz) :
    (∫ x : ℝ, (realBoundaryKernel ε x : ℂ) * (𝓕 φ) x) =
      ∫ t : ℝ, dampedSign ε t * φ t := by
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by
    ext
    simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := -innerₗ ℝ) Real.continuous_fourierChar continuous_inner.neg
    (dampedSign_integrable ε hε) (g := ⇑(𝓕 φ : LineSchwartz)) (𝓕 φ).integrable
  rw [hflip] at h
  change (∫ x : ℝ, (𝓕⁻ (dampedSign ε) x) • (𝓕 φ) x) =
    ∫ t : ℝ, dampedSign ε t • (𝓕⁻ (⇑(𝓕 φ : LineSchwartz)) t) at h
  simp_rw [inverse_dampedSign ε hε, ← SchwartzMap.fourierInv_coe,
    FourierTransform.fourierInv_fourier_eq, smul_eq_mul] at h
  exact h

theorem dampedSign_bound (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) :
    ‖dampedSign ε t‖ ≤ Real.pi := by
  unfold dampedSign
  split_ifs with ht
  all_goals
    rw [norm_mul]
    simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply mul_le_of_le_one_right Real.pi_pos.le
    apply Real.exp_le_one_iff.mpr
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  · exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos]) (le_of_not_ge ht)

theorem damped_sign_limit (φ : LineSchwartz) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, dampedSign ε t * φ t)
      (𝓝[>] (0 : ℝ)) (𝓝 (signPairing φ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun t => Real.pi * ‖φ t‖)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (dampedSign_integrable ε hε).aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall (fun t => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (dampedSign_bound ε hε.le t) (norm_nonneg _))
  · exact φ.integrable.norm.const_mul _
  · filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    have hc : ContinuousAt (fun ε : ℝ => dampedSign ε t * φ t) 0 := by
      unfold dampedSign
      split_ifs <;> fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    dsimp [dampedSign]
    by_cases h : t ≤ 0
    · simp [h, ht, not_lt.mpr h]
    · simp [h, ht, lt_of_not_ge h]

theorem fourier_principal_value :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.fourierPrincipalValueType := by
  intro φ
  apply tendsto_nhds_unique (real_boundary_limit (𝓕 φ))
  apply (damped_sign_limit φ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (damped_fourier_pairing ε hε φ).symm

/-- An integrable kernel acts continuously on the zeroth Schwartz seminorm. -/
def integrableKernel (k : ℝ → ℂ) (hk : Integrable k) : LineTempered := by
  have hi (φ : LineSchwartz) : Integrable (fun x => k x * φ x) :=
    hk.mul_bdd φ.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => φ.norm_le_seminorm ℂ x))
  refine SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun φ => ∫ x, k x * φ x) ?_ ?_ ?_
  · intro φ ψ
    simp only [add_apply, mul_add]
    exact integral_add (hi φ) (hi ψ)
  · intro c φ
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x, k x * (c * φ x) = c * (k x * φ x) by intro x; ring]
    exact integral_const_mul c _
  · refine ⟨{(0, 0)}, ∫ x, ‖k x‖, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
    intro φ
    simp only [Finset.sup_singleton, schwartzSeminormFamily]
    calc
      ‖∫ x, k x * φ x‖ ≤ ∫ x, ‖k x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖k x‖ * SchwartzMap.seminorm ℂ 0 0 φ := by
        apply integral_mono (hi φ).norm (hk.norm.mul_const _)
        intro x
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ x) (norm_nonneg _)
      _ = _ := integral_mul_const _ _

theorem logarithm_integrableOn (a b : ℝ) (hab : a ≤ b) :
    IntegrableOn (fun x : ℝ => (Real.log |x| : ℂ)) (Icc a b) := by
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (intervalIntegral.intervalIntegrable_log' (a := a) (b := b))
  simp only [Real.log_abs]
  exact h.ofReal

theorem logarithm_locally_integrable :
    LocallyIntegrable (fun x : ℝ => (Real.log |x| : ℂ)) := by
  intro x
  exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
    logarithm_integrableOn _ _ (by linarith)⟩

def logNearKernel (x : ℝ) : ℂ := (Icc (-1 : ℝ) 1).indicator
  (fun y : ℝ => (Real.log |y| : ℂ)) x

theorem logNearKernel_integrable : Integrable logNearKernel :=
  (logarithm_integrableOn (-1) 1 (by norm_num)).integrable_indicator measurableSet_Icc

def logTailKernel (x : ℝ) : ℂ := if 1 < |x| then (Real.log |x| : ℂ) / x else 0

theorem logTailKernel_measurable : Measurable logTailKernel := by
  exact ((Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).div
    Complex.measurable_ofReal).ite
    (measurableSet_lt measurable_const continuous_abs.measurable) measurable_const

theorem logTailKernel_bound (x : ℝ) : ‖logTailKernel x‖ ≤ 1 := by
  unfold logTailKernel
  split_ifs with h
  · rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h.le)]
    exact (div_le_one (by positivity)).mpr (Real.log_le_self (abs_nonneg _))
  · simp

def coordinateTest : LineSchwartz →L[ℂ] LineSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

theorem coordinateTest_apply (φ : LineSchwartz) (x : ℝ) :
    coordinateTest φ x = (x : ℂ) * φ x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) φ x

def logarithmFunctional : LineTempered :=
  integrableKernel logNearKernel logNearKernel_integrable +
    (boundedKernel logTailKernel logTailKernel_measurable 1 (by norm_num)
      logTailKernel_bound).comp coordinateTest

theorem logarithm_kernel_decomposition (φ : LineSchwartz) (x : ℝ) :
    (Real.log |x| : ℂ) * φ x = logNearKernel x * φ x +
      logTailKernel x * coordinateTest φ x := by
  rw [coordinateTest_apply]
  by_cases hx : |x| ≤ 1
  · have hmem : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    simp [logNearKernel, logTailKernel, hmem, not_lt.mpr hx]
  · have hmem : x ∉ Icc (-1 : ℝ) 1 := by simpa [← abs_le] using hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by intro h; simp [h] at hx)
    simp [logNearKernel, logTailKernel, hmem, lt_of_not_ge hx, div_eq_mul_inv, ← mul_assoc, hxc]

theorem logarithm_test_integrable (φ : LineSchwartz) :
    Integrable (fun x : ℝ => (Real.log |x| : ℂ) * φ x) := by
  have hn := logNearKernel_integrable.mul_bdd φ.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => φ.norm_le_seminorm ℂ x))
  have ht := bounded_kernel_integrable _ logTailKernel_measurable logTailKernel_bound
    (coordinateTest φ)
  convert hn.add ht using 1
  ext x
  exact logarithm_kernel_decomposition φ x

theorem logarithmFunctional_apply (φ : LineSchwartz) :
    logarithmFunctional φ = logPairing φ := by
  change (∫ x : ℝ, logNearKernel x * φ x) +
    (∫ x : ℝ, logTailKernel x * coordinateTest φ x) = _
  rw [← integral_add (logNearKernel_integrable.mul_bdd φ.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => φ.norm_le_seminorm ℂ x)))
    (bounded_kernel_integrable _ logTailKernel_measurable logTailKernel_bound (coordinateTest φ))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (logarithm_kernel_decomposition φ x).symm)

/-- Smooth logarithms approximate log|x| while retaining an integrable derivative. -/
def regularizedLog (ε x : ℝ) : ℝ := Real.log (x ^ 2 + ε ^ 2) / 2

theorem regularizedLog_deriv (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (regularizedLog ε y : ℂ))
      (realBoundaryKernel ε x : ℂ) x := by
  have hd : x ^ 2 + ε ^ 2 ≠ 0 := ne_of_gt (by positivity)
  convert (((hasDerivAt_pow 2 x).add_const (ε ^ 2)).log hd).div_const 2 |>.ofReal_comp using 1
  · rfl
  · simp only [realBoundaryKernel, Nat.cast_ofNat]
    push_cast
    ring

theorem regularizedLog_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : ℝ) (hx : x ≠ 0) :
    |regularizedLog ε x| ≤ |Real.log (|x|)| + x ^ 2 + 1 := by
  have hlow : Real.log |x| ≤ regularizedLog ε x := by
    have h := Real.log_le_log (sq_pos_of_ne_zero hx) (le_add_of_nonneg_right (sq_nonneg ε))
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    rw [Real.log_abs]
    dsimp [regularizedLog]
    linarith
  have hupp : regularizedLog ε x ≤ x ^ 2 + 1 := by
    have h := Real.log_le_self (show 0 ≤ x ^ 2 + ε ^ 2 by positivity)
    have he : ε ^ 2 ≤ 1 := by nlinarith
    dsimp [regularizedLog]
    nlinarith [sq_nonneg x]
  apply abs_le.mpr
  constructor
  · have := neg_abs_le (Real.log |x|)
    nlinarith [sq_nonneg x]
  · nlinarith [abs_nonneg (Real.log |x|)]

theorem logarithm_majorant_integrable (φ : LineSchwartz) :
    Integrable (fun x : ℝ => (|Real.log (|x|)| + x ^ 2 + 1) * ‖φ x‖) := by
  have hl := (logarithm_test_integrable φ).norm
  have hp := φ.integrable_pow_mul volume 2
  have h := (hl.add hp).add φ.integrable.norm
  convert h using 1
  ext x
  simp only [Pi.add_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, add_mul, one_mul]

theorem regularizedLog_test_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (φ : LineSchwartz) : Integrable (fun x : ℝ => (regularizedLog ε x : ℂ) * φ x) := by
  apply Integrable.mono' (logarithm_majorant_integrable φ)
  · have hc : Continuous (fun x : ℝ => (regularizedLog ε x : ℂ)) :=
      continuous_iff_continuousAt.mpr (fun x => (regularizedLog_deriv ε hε x).continuousAt)
    exact hc.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (regularizedLog_bound ε hε hε1 x hx) (norm_nonneg _)

theorem regularizedLog_limit (φ : LineSchwartz) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, (regularizedLog ε x : ℂ) * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (logPairing φ)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => (|Real.log (|x|)| + x ^ 2 + 1) * ‖φ x‖)
  · filter_upwards [self_mem_nhdsWithin, he] with ε hε hε1
    exact (regularizedLog_test_integrable ε hε hε1.le φ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, he] with ε hε hε1
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (regularizedLog_bound ε hε hε1.le x hx) (norm_nonneg _)
  · exact logarithm_majorant_integrable φ
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    have hc : ContinuousAt (fun ε : ℝ => (regularizedLog ε x : ℂ) * φ x) 0 := by
      unfold regularizedLog
      fun_prop (disch := positivity)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [regularizedLog, Real.log_pow, Real.log_abs]

theorem regularizedLog_integration_by_parts (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (φ : LineSchwartz) :
    -(∫ x : ℝ, (regularizedLog ε x : ℂ) * (SchwartzMap.derivCLM ℂ ℂ φ) x) =
      ∫ x : ℝ, (realBoundaryKernel ε x : ℂ) * φ x := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => (regularizedLog ε x : ℂ))
    (u' := fun x : ℝ => (realBoundaryKernel ε x : ℂ))
    (v := ⇑φ) (v' := ⇑(SchwartzMap.derivCLM ℂ ℂ φ))
    (fun x _ => regularizedLog_deriv ε hε x)
    (fun x _ => by simpa only [SchwartzMap.derivCLM_apply] using φ.differentiableAt.hasDerivAt)
    (regularizedLog_test_integrable ε hε hε1 (SchwartzMap.derivCLM ℂ ℂ φ))
    (real_boundary_integrable ε hε φ) (regularizedLog_test_integrable ε hε hε1 φ)
  exact neg_eq_iff_eq_neg.mpr h

theorem logarithm_derivative (φ : LineSchwartz) :
    -logPairing (SchwartzMap.derivCLM ℂ ℂ φ) = principalValuePairing φ := by
  have h := (regularizedLog_limit (SchwartzMap.derivCLM ℂ ℂ φ)).neg
  apply tendsto_nhds_unique h
  apply (real_boundary_limit φ).congr'
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he] with ε hε hε1
  exact (regularizedLog_integration_by_parts ε hε hε1.le φ).symm

theorem logarithm :
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.logarithmType := by
  refine ⟨logarithm_locally_integrable, logarithm_test_integrable,
    logarithmFunctional, logarithmFunctional_apply, ?_⟩
  intro φ
  rw [logarithmFunctional_apply]
  exact logarithm_derivative φ

end PrincipalValue
end ExpandedFA.SingularIntegrals
