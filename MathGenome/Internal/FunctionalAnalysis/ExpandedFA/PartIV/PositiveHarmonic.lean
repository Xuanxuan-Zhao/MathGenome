import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveHarmonic
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace ExpandedFA.PartIV.PositiveHarmonic

open Set MeasureTheory InnerProductSpace Metric Complex Filter
open scoped Topology BoundedContinuousFunction

lemma circle_sub_ne_zero {z : ℂ} (hz : z ∈ unitDisk) (ζ : Circle) :
    (ζ : ℂ) - z ≠ 0 := by
  intro h
  have : z = (ζ : ℂ) := (sub_eq_zero.mp h).symm
  simp [unitDisk, this] at hz

lemma continuous_circlePoissonKernel {z : ℂ} (hz : z ∈ unitDisk) :
    Continuous (circlePoissonKernel z) := by
  unfold circlePoissonKernel
  exact continuous_const.div (by fun_prop) (fun ζ => pow_ne_zero _
    (norm_ne_zero_iff.mpr (circle_sub_ne_zero hz ζ)))

lemma circlePoissonKernel_pos {z : ℂ} (hz : z ∈ unitDisk) (ζ : Circle) :
    0 < circlePoissonKernel z ζ := by
  have h : ‖z‖ < 1 := hz
  have hn := norm_nonneg z
  unfold circlePoissonKernel
  exact div_pos (by nlinarith) (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (circle_sub_ne_zero hz ζ)))

@[simp] lemma circlePoissonKernel_zero (ζ : Circle) : circlePoissonKernel 0 ζ = 1 := by
  simp [circlePoissonKernel]

lemma integrable_circlePoissonKernel (μ : Measure Circle) [IsFiniteMeasure μ]
    {z : ℂ} (hz : z ∈ unitDisk) : Integrable (circlePoissonKernel z) μ :=
  (continuous_circlePoissonKernel hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma poissonExtension_nonneg (μ : Measure Circle) {z : ℂ} (hz : z ∈ unitDisk) :
    0 ≤ poissonExtension μ z := by
  exact integral_nonneg (fun ζ => (circlePoissonKernel_pos hz ζ).le)

@[simp] lemma poissonExtension_zero (μ : Measure Circle) :
    poissonExtension μ 0 = μ.real univ := by
  simp [poissonExtension]

lemma zero_extension : Spec.ZeroExtension := by
  funext z
  simp [poissonExtension]

lemma circleHaar_probability : IsProbabilityMeasure circleHaar := by
  constructor
  exact Measure.haarMeasure_self

lemma circleHaar_regular : circleHaar.Regular := inferInstanceAs (Measure.haarMeasure ⊤).Regular

lemma isOpen_unitDisk : IsOpen unitDisk :=
  isOpen_lt continuous_norm continuous_const

/-- The complex kernel whose real part is the Poisson kernel. -/
def circleHerglotzKernel (z : ℂ) (ζ : Circle) : ℂ :=
  herglotzRieszKernel 0 z (ζ : ℂ)

lemma circleHerglotzKernel_re (z : ℂ) (ζ : Circle) :
    (circleHerglotzKernel z ζ).re = circlePoissonKernel z ζ := by
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z))
    (ζ : ℂ)
  simpa [poissonKernel, circlePoissonKernel, circleHerglotzKernel] using h.symm

lemma continuous_circleHerglotzKernel {z : ℂ} (hz : z ∈ unitDisk) :
    Continuous (circleHerglotzKernel z) := by
  unfold circleHerglotzKernel herglotzRieszKernel
  simp only [sub_zero]
  exact (by fun_prop : Continuous (fun ζ : Circle => (ζ : ℂ) + z)).div
    (by fun_prop) (circle_sub_ne_zero hz)

lemma integrable_circleHerglotzKernel (μ : Measure Circle) [IsFiniteMeasure μ]
    {z : ℂ} (hz : z ∈ unitDisk) : Integrable (circleHerglotzKernel z) μ :=
  (continuous_circleHerglotzKernel hz).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma hasDerivAt_circleHerglotzKernel {z : ℂ} (hz : z ∈ unitDisk) (ζ : Circle) :
    HasDerivAt (fun w => circleHerglotzKernel w ζ)
      (2 * (ζ : ℂ) / ((ζ : ℂ) - z) ^ 2) z := by
  have h := ((hasDerivAt_id' z).const_add (ζ : ℂ)).div
    ((hasDerivAt_id' z).const_sub (ζ : ℂ)) (circle_sub_ne_zero hz ζ)
  convert h using 1 <;> simp [circleHerglotzKernel, herglotzRieszKernel,
    sub_zero, sub_sub, ← two_mul, Pi.div_def]

lemma differentiableOn_herglotzIntegral (μ : Measure Circle) [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (fun z => ∫ ζ, circleHerglotzKernel z ζ ∂μ) unitDisk := by
  intro w hw
  let r : ℝ := (1 + ‖w‖) / 2
  have hw' : ‖w‖ < 1 := hw
  have hwr : ‖w‖ < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hmem : ball (0 : ℂ) r ∈ 𝓝 w := isOpen_ball.mem_nhds (by simpa using hwr)
  have hsub : ball (0 : ℂ) r ⊆ unitDisk := by
    intro x hx
    exact lt_trans (by simpa using hx) hr
  have hdist (x : ℂ) (hx : x ∈ ball (0 : ℂ) r) (ζ : Circle) :
      1 - r ≤ ‖(ζ : ℂ) - x‖ := by
    have hx' : ‖x‖ < r := by simpa using hx
    have h := norm_sub_norm_le (ζ : ℂ) x
    rw [Circle.norm_coe] at h
    linarith
  have hd : 0 < 1 - r := sub_pos.mpr hr
  have hmeas : ∀ᶠ x in 𝓝 w,
      AEStronglyMeasurable (circleHerglotzKernel x) μ := by
    filter_upwards [hmem] with x hx
    exact (continuous_circleHerglotzKernel (hsub hx)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun ζ : Circle => 2 * (ζ : ℂ) / ((ζ : ℂ) - w) ^ 2) μ := by
    apply Continuous.aestronglyMeasurable
    exact (by fun_prop : Continuous (fun ζ : Circle => 2 * (ζ : ℂ))).div
      (by fun_prop) (fun ζ => pow_ne_zero _ (circle_sub_ne_zero hw ζ))
  have hbound : ∀ᵐ ζ : Circle ∂μ, ∀ x ∈ ball (0 : ℂ) r,
      ‖2 * (ζ : ℂ) / ((ζ : ℂ) - x) ^ 2‖ ≤ 2 / (1 - r) ^ 2 := by
    filter_upwards with ζ x hx
    simp only [norm_div, norm_mul, norm_pow, Circle.norm_coe, norm_ofNat, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num)
      (sq_pos_of_pos hd) (by nlinarith [hdist x hx ζ, norm_nonneg ((ζ : ℂ) - x)])
  have hdiff : ∀ᵐ ζ : Circle ∂μ, ∀ x ∈ ball (0 : ℂ) r,
      HasDerivAt (fun z => circleHerglotzKernel z ζ)
        (2 * (ζ : ℂ) / ((ζ : ℂ) - x) ^ 2) x := by
    filter_upwards with ζ x hx
    exact hasDerivAt_circleHerglotzKernel (hsub hx) ζ
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := circleHerglotzKernel) (F' := fun x ζ =>
      2 * (ζ : ℂ) / ((ζ : ℂ) - x) ^ 2)
    (bound := fun _ => 2 / (1 - r) ^ 2) hmem hmeas
    (integrable_circleHerglotzKernel μ hw) hmeas' hbound
    (integrable_const _) hdiff).2.differentiableAt.differentiableWithinAt

lemma poissonExtension_eq_re_integral (μ : Measure Circle) [IsFiniteMeasure μ]
    {z : ℂ} (hz : z ∈ unitDisk) :
    poissonExtension μ z = (∫ ζ, circleHerglotzKernel z ζ ∂μ).re := by
  change poissonExtension μ z = Complex.reCLM (∫ ζ, circleHerglotzKernel z ζ ∂μ)
  rw [← Complex.reCLM.integral_comp_comm (integrable_circleHerglotzKernel μ hz)]
  simp only [poissonExtension, Complex.reCLM_apply, circleHerglotzKernel_re]

lemma poissonExtension_harmonic (μ : Measure Circle) [IsFiniteMeasure μ] :
    HarmonicOnNhd (poissonExtension μ) unitDisk := by
  intro z hz
  have han := (differentiableOn_herglotzIntegral μ).analyticOnNhd isOpen_unitDisk
  apply (harmonicAt_congr_nhds (f₂ := fun w =>
    (∫ ζ, circleHerglotzKernel w ζ ∂μ).re) ?_).mpr ((han z hz).harmonicAt_re)
  filter_upwards [isOpen_unitDisk.mem_nhds hz] with w hw
  exact poissonExtension_eq_re_integral μ hw

theorem converse : Spec.Converse := by
  intro μ hμ _
  have := hμ
  exact ⟨⟨poissonExtension_harmonic μ, fun z hz => poissonExtension_nonneg μ hz⟩,
    poissonExtension_zero μ⟩

lemma circlePoissonKernel_rotate (η ζ : Circle) (z : ℂ) :
    circlePoissonKernel ((η : ℂ) * z) (η * ζ) = circlePoissonKernel z ζ := by
  simp only [circlePoissonKernel, Circle.coe_mul, ← mul_sub, norm_mul,
    Circle.norm_coe, one_mul]

lemma poissonExtension_haar_rotate (η : Circle) (z : ℂ) :
    poissonExtension circleHaar ((η : ℂ) * z) = poissonExtension circleHaar z := by
  have : Measure.IsMulLeftInvariant circleHaar :=
    inferInstanceAs (Measure.IsMulLeftInvariant (Measure.haarMeasure ⊤))
  unfold poissonExtension
  rw [← integral_mul_left_eq_self (circlePoissonKernel ((η : ℂ) * z)) η]
  simp_rw [circlePoissonKernel_rotate]

lemma poissonExtension_haar_eq_of_norm_eq {z w : ℂ} (h : ‖z‖ = ‖w‖) :
    poissonExtension circleHaar z = poissonExtension circleHaar w := by
  by_cases hw : w = 0
  · have hz : z = 0 := norm_eq_zero.mp (by simpa [hw] using h)
    simp [hw, hz]
  · let η : Circle := ⟨z / w, by
      apply mem_sphere_zero_iff_norm.mpr
      simp [h, (norm_ne_zero_iff.mpr hw)]⟩
    have heq : (η : ℂ) * w = z := div_mul_cancel₀ z hw
    rw [← heq]
    exact poissonExtension_haar_rotate η w

theorem haar_normalization : Spec.HaarNormalization := by
  have : IsProbabilityMeasure circleHaar := circleHaar_probability
  refine ⟨circleHaar_probability, circleHaar_regular, ?_⟩
  intro z hz
  have hsub : closedBall (0 : ℂ) |‖z‖| ⊆ unitDisk := by
    intro w hw
    have hw' : ‖w‖ ≤ ‖z‖ := by simpa using hw
    exact hw'.trans_lt hz
  have hmean := ((poissonExtension_harmonic circleHaar).mono hsub).circleAverage_eq
  have heq : Real.circleAverage (poissonExtension circleHaar) 0 ‖z‖ =
      poissonExtension circleHaar z := by
    calc
      Real.circleAverage (poissonExtension circleHaar) 0 ‖z‖ =
          Real.circleAverage (fun _ : ℂ => poissonExtension circleHaar z) 0 ‖z‖ := by
        apply Real.circleAverage_congr_sphere
        intro w hw
        apply poissonExtension_haar_eq_of_norm_eq
        simpa [mem_sphere_iff_norm] using hw
      _ = _ := Real.circleAverage_const _ _ _
  rw [heq, poissonExtension_zero] at hmean
  simpa using hmean

local instance two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Identifies the abstract normalized Haar measure with angle integration. -/
lemma circleHaar_eq_map :
    circleHaar = Measure.map (AddCircle.toCircle (T := 2 * Real.pi))
      AddCircle.haarAddCircle := by
  let m := (AddCircle.haarAddCircle : Measure (AddCircle (2 * Real.pi)))
  let e := AddCircle.toCircle (T := 2 * Real.pi)
  have he : Measurable e := AddCircle.continuous_toCircle.measurable
  have hs : Function.Surjective e := by
    intro ζ
    obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (by positivity : 2 * Real.pi ≠ 0)).surjective ζ
    exact ⟨x, by simpa only [AddCircle.homeomorphCircle_apply] using hx⟩
  have : (Measure.map e m).IsMulLeftInvariant := by
    constructor
    intro g
    obtain ⟨a, rfl⟩ := hs g
    rw [Measure.map_map (measurable_const_mul _) he]
    have heq : (fun x => e a * x) ∘ e = e ∘ (fun x => a + x) := by
      funext x
      exact (AddCircle.toCircle_add a x).symm
    rw [heq, ← Measure.map_map he (measurable_const_add a), map_add_left_eq_self m a]
  have : IsProbabilityMeasure (Measure.map e m) := by
    constructor
    rw [Measure.map_apply he MeasurableSet.univ]
    simp [m]
  exact (Measure.haarMeasure_eq_iff ⊤ (Measure.map e m)).mpr (by simp)

lemma integral_circleHaar {f : Circle → ℝ} (hf : Continuous f) :
    ∫ ζ, f ζ ∂circleHaar =
      (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, f (Circle.exp θ) := by
  rw [circleHaar_eq_map, integral_map AddCircle.continuous_toCircle.measurable.aemeasurable
    hf.aestronglyMeasurable, AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp [AddCircle.toCircle_apply_mk, smul_eq_mul]

/-- The Haar integral of a continuous function on a radius-`r` circle is its
usual normalized circle average. Only continuity on that circle is needed. -/
lemma integral_circleHaar_scale {f : ℂ → ℝ} {r : ℝ}
    (hf : Continuous (fun ζ : Circle => f ((r : ℂ) * ζ))) :
    ∫ ζ, f ((r : ℂ) * ζ) ∂circleHaar = Real.circleAverage f 0 r := by
  rw [integral_circleHaar hf, Real.circleAverage_def]
  simp [circleMap, Circle.coe_exp, smul_eq_mul]

lemma continuous_radialBoundary {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u unitDisk) {r : ℝ} (hr : |r| < 1) :
    Continuous (fun ζ : Circle => u ((r : ℂ) * ζ)) := by
  apply hu.continuousOn.comp_continuous (by fun_prop)
  intro ζ
  simpa [unitDisk, norm_mul] using hr

lemma harmonic_radial_mean {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u unitDisk) {r : ℝ} (hr : |r| < 1) :
    ∫ ζ : Circle, u ((r : ℂ) * ζ) ∂circleHaar = u 0 := by
  rw [integral_circleHaar_scale (continuous_radialBoundary hu hr)]
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  apply hu.mono
  intro z hz
  exact lt_of_le_of_lt (by simpa using hz) hr

/-- Positive boundary densities at radii strictly below one. -/
def radialBoundaryMeasure (u : ℂ → ℝ) (r : ℝ) : Measure Circle :=
  circleHaar.withDensity (fun ζ => ENNReal.ofReal (u ((r : ℂ) * ζ)))

lemma radialBoundaryMeasure_finite {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u unitDisk) {r : ℝ} (hr : |r| < 1) :
    IsFiniteMeasure (radialBoundaryMeasure u r) := by
  have : IsProbabilityMeasure circleHaar := circleHaar_probability
  apply isFiniteMeasure_withDensity_ofReal
  exact ((continuous_radialBoundary hu hr).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

lemma integral_radialBoundaryMeasure {u : ℂ → ℝ}
    (hu : NonnegativeHarmonic u) {r : ℝ} (hr : |r| < 1) (f : Circle → ℝ) :
    ∫ ζ, f ζ ∂radialBoundaryMeasure u r =
      ∫ ζ, u ((r : ℂ) * ζ) * f ζ ∂circleHaar := by
  unfold radialBoundaryMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((continuous_radialBoundary hu.1 hr).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  funext ζ
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hu.2 ((r : ℂ) * ζ) (by
    simpa [unitDisk, norm_mul] using hr))]

lemma radialBoundaryMeasure_mass {u : ℂ → ℝ}
    (hu : NonnegativeHarmonic u) {r : ℝ} (hr : |r| < 1) :
    (radialBoundaryMeasure u r).real univ = u 0 := by
  calc
    (radialBoundaryMeasure u r).real univ = ∫ _ : Circle, (1 : ℝ) ∂radialBoundaryMeasure u r := by simp
    _ = u 0 := by
      rw [integral_radialBoundaryMeasure hu hr]
      simpa using harmonic_radial_mean hu.1 hr

lemma poissonKernel_scale (z : ℂ) (ζ : Circle) {r : ℝ} (hr : r ≠ 0) :
    poissonKernel 0 ((r : ℂ) * z) ((r : ℂ) * ζ) = circlePoissonKernel z ζ := by
  simp only [poissonKernel, circlePoissonKernel, sub_zero, norm_mul,
    Circle.norm_coe, mul_one, ← mul_sub, mul_pow]
  have hn : ‖(r : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ofReal_ne_zero.mpr hr)
  rw [show ‖(r : ℂ)‖ ^ 2 - ‖(r : ℂ)‖ ^ 2 * ‖z‖ ^ 2 =
    ‖(r : ℂ)‖ ^ 2 * (1 - ‖z‖ ^ 2) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hn)

lemma radialBoundary_poisson {u : ℂ → ℝ} (hu : NonnegativeHarmonic u)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : z ∈ unitDisk) :
    poissonExtension (radialBoundaryMeasure u r) z = u ((r : ℂ) * z) := by
  have hr : |r| < 1 := by simpa [abs_of_pos hr0] using hr1
  rw [poissonExtension, integral_radialBoundaryMeasure hu hr]
  have hf : Continuous (fun ζ : Circle =>
      poissonKernel 0 ((r : ℂ) * z) ((r : ℂ) * ζ) * u ((r : ℂ) * ζ)) := by
    simp_rw [poissonKernel_scale z _ hr0.ne']
    exact (continuous_circlePoissonKernel hz).mul (continuous_radialBoundary hu.1 hr)
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisk := by
    intro w hw
    exact lt_of_le_of_lt (by simpa using hw) hr1
  have hform := (hu.1.mono hsub).circleAverage_poissonKernel_smul (w := (r : ℂ) * z)
    (by simpa [mem_ball, dist_eq_norm, norm_mul, abs_of_pos hr0] using
      (mul_lt_mul_of_pos_left hz hr0))
  rw [← integral_circleHaar_scale hf] at hform
  change (∫ ζ : Circle, poissonKernel 0 ((r : ℂ) * z) ((r : ℂ) * ζ) *
    u ((r : ℂ) * ζ) ∂circleHaar) = u ((r : ℂ) * z) at hform
  simp_rw [poissonKernel_scale z _ hr0.ne'] at hform
  simpa only [mul_comm] using hform

/-- Existence follows from weak compactness of finite measures of bounded mass.
The fixed-kernel formula `u(r*z) = ∫ P_z dμ_r` avoids a varying-kernel limit. -/
theorem exists_representing_measure {u : ℂ → ℝ} (hu : NonnegativeHarmonic u) :
    ∃ μ : Measure Circle, Represents u μ := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr0 (n : ℕ) : 0 < r n := by
    dsimp [r]
    have h : (1 : ℝ) < (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have := (div_lt_one (by positivity : 0 < (n : ℝ) + 2)).mpr h
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hr (n : ℕ) : |r n| < 1 := by rw [abs_of_pos (hr0 n)]; exact hr1 n
  have hrlim : Filter.Tendsto r Filter.atTop (𝓝 1) := by
    have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa [r] using tendsto_const_nhds.sub hinv
  let ν : ℕ → FiniteMeasure Circle := fun n =>
    ⟨radialBoundaryMeasure u (r n), radialBoundaryMeasure_finite hu.1 (hr n)⟩
  have hu0 : 0 ≤ u 0 := hu.2 0 (by simp [unitDisk])
  have hmass (n : ℕ) : (ν n).mass ≤ (u 0).toNNReal := by
    apply (NNReal.coe_le_coe).mp
    change ((radialBoundaryMeasure u (r n) univ).toNNReal : ℝ) ≤ _
    rw [Real.toNNReal_of_nonneg hu0]
    change (radialBoundaryMeasure u (r n)).real univ ≤ u 0
    exact (radialBoundaryMeasure_mass hu (hr n)).le
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  obtain ⟨μ, hμmass, hμlim⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace Circle (u 0).toNNReal).ultrafilter_le_nhds'
      (Ultrafilter.map ν U) (by
        rw [Ultrafilter.mem_map]
        exact Filter.Eventually.of_forall hmass)
  have hνlim : Filter.Tendsto ν (U : Filter ℕ) (𝓝 μ) := by
    change Filter.map ν (U : Filter ℕ) ≤ 𝓝 μ
    simpa only [Ultrafilter.coe_map] using hμlim
  refine ⟨(μ : Measure Circle), inferInstance, inferInstance, ?_, ?_⟩
  · intro z hz
    let f : Circle →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨circlePoissonKernel z, continuous_circlePoissonKernel hz⟩
    have hlim := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hνlim) f
    have heq (n : ℕ) : ∫ ζ : Circle, f ζ ∂(ν n : Measure Circle) = u ((r n : ℂ) * z) :=
      radialBoundary_poisson hu (hr0 n) (hr1 n) hz
    simp_rw [heq] at hlim
    have hcont : ContinuousAt u z := (hu.1 z hz).1.continuousAt
    have hpoint : Filter.Tendsto (fun n => u ((r n : ℂ) * z)) Filter.atTop (𝓝 (u z)) := by
      apply hcont.tendsto.comp
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hrlim).mul_const z
    exact (tendsto_nhds_unique (hpoint.mono_left hU) hlim)
  · have heq0 := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hνlim)
      (1 : Circle →ᵇ ℝ)
    have heq (n : ℕ) : ∫ ζ : Circle, (1 : Circle →ᵇ ℝ) ζ ∂(ν n : Measure Circle) = u 0 := by
      change (∫ _ : Circle, (1 : ℝ) ∂radialBoundaryMeasure u (r n)) = u 0
      simpa only [integral_const, smul_eq_mul, mul_one] using radialBoundaryMeasure_mass hu (hr n)
    simp_rw [heq] at heq0
    have h := (tendsto_nhds_unique tendsto_const_nhds heq0).symm
    change (∫ _ : Circle, (1 : ℝ) ∂(μ : Measure Circle)) = u 0 at h
    simpa only [integral_const, smul_eq_mul, mul_one] using h

/-- Off every neighborhood of its boundary point, the radial Poisson kernel
converges uniformly to zero. -/
lemma poissonKernel_tendstoUniformly_off {r : ℕ → ℝ}
    (hr : ∀ n, |r n| < 1) (hrlim : Tendsto r atTop (𝓝 1)) (η : Circle)
    {s : Set Circle} (hs : IsOpen s) (hη : η ∈ s) :
    TendstoUniformlyOn (fun n ζ => circlePoissonKernel ((r n : ℂ) * η) ζ)
      0 atTop sᶜ := by
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hη)
  have hsmall : ∀ᶠ n in atTop, |1 - r n| < δ / 2 := by
    have ht : Tendsto (fun n => |1 - r n|) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hrlim).abs
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hboundlim : Tendsto (fun n => (1 - (r n) ^ 2) / (δ / 2) ^ 2) atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hrlim.pow 2)).div_const ((δ / 2) ^ 2)
    simpa using ht
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hsmall, hboundlim.eventually (gt_mem_nhds hε)] with n hn hnε ζ hζ
  have hz : ((r n : ℂ) * η) ∈ unitDisk := by simpa [unitDisk, norm_mul] using hr n
  have hsep : δ ≤ ‖(ζ : ℂ) - η‖ := by
    by_contra! h
    apply hζ
    apply hδs
    change dist (ζ : ℂ) (η : ℂ) < δ
    simpa only [dist_eq_norm] using h
  have hdiff : ‖(r n : ℂ) * (η : ℂ) - η‖ = |1 - r n| := by
    have heq : (r n : ℂ) * (η : ℂ) - η = ((r n : ℂ) - 1) * η := by ring
    rw [heq, norm_mul, Circle.norm_coe, mul_one]
    simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
  have hdist := norm_sub_le_norm_sub_add_norm_sub (ζ : ℂ) ((r n : ℂ) * η) (η : ℂ)
  rw [hdiff] at hdist
  have hden : δ / 2 ≤ ‖(ζ : ℂ) - (r n : ℂ) * η‖ := by linarith
  have hnum : 0 ≤ 1 - (r n) ^ 2 := by
    have := abs_lt.mp (hr n)
    nlinarith
  have hbound : circlePoissonKernel ((r n : ℂ) * η) ζ ≤
      (1 - (r n) ^ 2) / (δ / 2) ^ 2 := by
    simp only [circlePoissonKernel, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact div_le_div_of_nonneg_left hnum (by positivity)
      (by nlinarith [norm_nonneg ((ζ : ℂ) - (r n : ℂ) * η)])
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_pos (circlePoissonKernel_pos hz ζ)] using hbound.trans_lt hnε

lemma poissonTest_tendsto {r : ℕ → ℝ} (hr : ∀ n, |r n| < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (f : C(Circle, ℝ)) (η : Circle) :
    Tendsto (fun n => ∫ ζ, circlePoissonKernel ((r n : ℂ) * η) ζ * f ζ ∂circleHaar)
      atTop (𝓝 (f η)) := by
  have : IsProbabilityMeasure circleHaar := circleHaar_probability
  simp_rw [← smul_eq_mul]
  refine tendsto_integral_peak_smul_of_integrable_of_tendsto
    (μ := circleHaar) (t := univ)
    (φ := fun n ζ => circlePoissonKernel ((r n : ℂ) * η) ζ)
    MeasurableSet.univ Filter.univ_mem (measure_ne_top _ _)
    (Eventually.of_forall (fun n ζ => (circlePoissonKernel_pos
      (by simpa [unitDisk, norm_mul] using hr n) ζ).le))
    (fun _ hs hη => poissonKernel_tendstoUniformly_off hr hrlim η hs hη)
    ?_ ?_ ?_ f.continuous.continuousAt.tendsto
  · simp only [Measure.restrict_univ]
    have heq (n : ℕ) : (∫ ζ, circlePoissonKernel ((r n : ℂ) * η) ζ ∂circleHaar) = 1 :=
      haar_normalization.2.2 _ (by simpa [unitDisk, norm_mul] using hr n)
    simp_rw [heq]
    exact tendsto_const_nhds
  · exact Eventually.of_forall (fun n => (continuous_circlePoissonKernel
      (by simpa [unitDisk, norm_mul] using hr n)).aestronglyMeasurable)
  · exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma continuous_radialPoissonKernel {r : ℝ} (hr : |r| < 1) :
    Continuous (fun p : Circle × Circle => circlePoissonKernel ((r : ℂ) * p.1) p.2) := by
  unfold circlePoissonKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (circle_sub_ne_zero
    (by simpa [unitDisk, norm_mul] using hr) p.2))

lemma circlePoissonKernel_symm (r : ℝ) (η ζ : Circle) :
    circlePoissonKernel ((r : ℂ) * η) ζ = circlePoissonKernel ((r : ℂ) * ζ) η := by
  unfold circlePoissonKernel
  congr 1
  · simp
  · rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [Complex.normSq_sub, Circle.normSq_coe,
      mul_one, map_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

lemma norm_poissonTest_le {r : ℝ} (hr : |r| < 1) (f : C(Circle, ℝ)) (η : Circle) :
    ‖∫ ζ, circlePoissonKernel ((r : ℂ) * η) ζ * f ζ ∂circleHaar‖ ≤ ‖f‖ := by
  have : IsProbabilityMeasure circleHaar := circleHaar_probability
  have hz : ((r : ℂ) * η) ∈ unitDisk := by simpa [unitDisk, norm_mul] using hr
  have hi := integrable_circlePoissonKernel circleHaar hz
  have hif := ((continuous_circlePoissonKernel hz).mul f.continuous).integrable_of_hasCompactSupport
    (μ := circleHaar) (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ ζ, ‖circlePoissonKernel ((r : ℂ) * η) ζ * f ζ‖ ∂circleHaar := norm_integral_le_integral_norm _
    _ ≤ ∫ ζ, circlePoissonKernel ((r : ℂ) * η) ζ * ‖f‖ ∂circleHaar := by
      apply integral_mono hif.norm (hi.mul_const _)
      intro ζ
      change ‖circlePoissonKernel ((r : ℂ) * η) ζ * f ζ‖ ≤
        circlePoissonKernel ((r : ℂ) * η) ζ * ‖f‖
      rw [norm_mul, Real.norm_of_nonneg (circlePoissonKernel_pos hz ζ).le]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm ζ) (circlePoissonKernel_pos hz ζ).le
    _ = ‖f‖ := by
      rw [integral_mul_const]
      change poissonExtension circleHaar ((r : ℂ) * η) * ‖f‖ = ‖f‖
      rw [haar_normalization.2.2 _ hz, one_mul]

lemma poissonTest_swap (μ : Measure Circle) [IsFiniteMeasure μ]
    {r : ℝ} (hr : |r| < 1) (f : C(Circle, ℝ)) :
    (∫ η, f η * poissonExtension μ ((r : ℂ) * η) ∂circleHaar) =
      ∫ ζ, (∫ η, circlePoissonKernel ((r : ℂ) * ζ) η * f η ∂circleHaar) ∂μ := by
  have : IsProbabilityMeasure circleHaar := circleHaar_probability
  have hcont : Continuous (fun p : Circle × Circle =>
      f p.1 * circlePoissonKernel ((r : ℂ) * p.1) p.2) :=
    (f.continuous.comp continuous_fst).mul (continuous_radialPoissonKernel hr)
  have hi := hcont.integrable_of_hasCompactSupport (μ := circleHaar.prod μ)
    (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ η, (∫ ζ, f η * circlePoissonKernel ((r : ℂ) * η) ζ ∂μ) ∂circleHaar := by
      simp_rw [integral_const_mul]
      rfl
    _ = ∫ ζ, (∫ η, f η * circlePoissonKernel ((r : ℂ) * η) ζ ∂circleHaar) ∂μ :=
      integral_integral_swap hi
    _ = _ := by simp_rw [circlePoissonKernel_symm r, mul_comm]

lemma poissonTest_integral_tendsto (μ : Measure Circle) [IsFiniteMeasure μ]
    {r : ℕ → ℝ} (hr : ∀ n, |r n| < 1) (hrlim : Tendsto r atTop (𝓝 1))
    (f : C(Circle, ℝ)) :
    Tendsto (fun n => ∫ η, f η * poissonExtension μ ((r n : ℂ) * η) ∂circleHaar)
      atTop (𝓝 (∫ η, f η ∂μ)) := by
  have : IsProbabilityMeasure circleHaar := circleHaar_probability
  simp_rw [poissonTest_swap μ (hr _) f]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    have hcont : Continuous (fun p : Circle × Circle =>
        circlePoissonKernel ((r n : ℂ) * p.1) p.2 * f p.2) :=
      (continuous_radialPoissonKernel (hr n)).mul (f.continuous.comp continuous_snd)
    have hc := continuous_parametric_integral_of_continuous (μ := circleHaar)
      (f := fun η ζ : Circle => circlePoissonKernel ((r n : ℂ) * η) ζ * f ζ)
      hcont isCompact_univ
    simpa using hc.aestronglyMeasurable (μ := μ)
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (norm_poissonTest_le (hr n) f)
  · exact Eventually.of_forall (poissonTest_tendsto hr hrlim f)

/-- Finite positive measures are determined by their Poisson extensions on the
disk. Continuous boundary tests are recovered by radial approximation. -/
theorem poissonExtension_injective (μ ν : Measure Circle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z ∈ unitDisk, poissonExtension μ z = poissonExtension ν z) : μ = ν := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : |r n| < 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    rw [abs_lt]
    dsimp [r]
    constructor <;> linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    simpa [r] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : C(Circle, ℝ) := ⟨f, f.continuous⟩
  have hμ := poissonTest_integral_tendsto μ hr hrlim g
  have hν := poissonTest_integral_tendsto ν hr hrlim g
  have heq (n : ℕ) :
      (∫ η, g η * poissonExtension μ ((r n : ℂ) * η) ∂circleHaar) =
      ∫ η, g η * poissonExtension ν ((r n : ℂ) * η) ∂circleHaar := by
    congr 1
    funext η
    rw [h _ (by simpa [unitDisk, norm_mul] using hr n)]
  simp_rw [heq] at hμ
  exact tendsto_nhds_unique hμ hν

/-- Positive harmonic representation, with uniqueness among all finite positive
Radon measures and the exact mass formula. No strict positivity is assumed. -/
theorem representation : Spec.Representation := by
  intro u hu
  obtain ⟨μ, hμ⟩ := exists_representing_measure hu
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  have : IsFiniteMeasure μ := hμ.1
  have : IsFiniteMeasure ν := hν.1
  exact poissonExtension_injective ν μ (fun z hz => (hν.2.2.1 z hz).symm.trans (hμ.2.2.1 z hz))

end ExpandedFA.PartIV.PositiveHarmonic
