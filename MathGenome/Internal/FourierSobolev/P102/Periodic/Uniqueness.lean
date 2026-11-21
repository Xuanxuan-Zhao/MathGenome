import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.FejerRecovery
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Uniqueness
import Mathlib.MeasureTheory.Integral.DominatedConvergence

import MathGenome.Internal.FourierSobolev.P102.Periodic.FejerRecovery
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate
namespace P102.Periodic

private theorem zero_from_fejer
    (h : Expected.FejerRecovery.lpComplexStatement) :
    Expected.Uniqueness.zeroStatement := by
  intro T hT f hf hc
  have hm : ∀ N x, Expected.fejerMean T N f x = 0 := by
    intro N x
    simp [Expected.fejerMean, Expected.partialSum, show ∀ k, Expected.coefficient T f k = 0 from hc]
  have hl := h T 1 le_rfl (by simp) f (memLp_one_iff_integrable.mpr hf)
  simp only [hm, zero_sub] at hl
  change Tendsto (fun _ : ℕ => eLpNorm (-f) 1 (haar T)) atTop (𝓝 0) at hl
  rw [eLpNorm_neg] at hl
  have hz : eLpNorm f 1 (haar T) = 0 := tendsto_nhds_unique tendsto_const_nhds hl
  exact (eLpNorm_eq_zero_iff (by simp : (1 : ℝ≥0∞) ≠ 0)).mp hz

private theorem ae_equal_from_fejer
    (h : Expected.FejerRecovery.lpComplexStatement) :
    Expected.Uniqueness.aeEqualityStatement := by
  intro T hT f g hf hg hc
  have hz := zero_from_fejer h T (fun x => f x - g x) (hf.sub hg)
  have hh : (fun x => f x - g x) =ᵐ[haar T] 0 := hz (by
    intro k
    change coefficient T (fun x => f x - g x) k = 0
    rw [coefficient, show (fun x => (f x - g x) * conj (mode T k x)) =
      (fun x => f x * conj (mode T k x)) - (fun x => g x * conj (mode T k x)) by
        ext x; simp [sub_mul]]
    change (∫ x, f x * conj (mode T k x) - g x * conj (mode T k x) ∂haar T) = 0
    rw [integral_sub]
    · exact sub_eq_zero.mpr (hc k)
    · simpa only [mode, fourier_neg, smul_eq_mul, mul_comm] using hf.fourier_smul (-k)
    · simpa only [mode, fourier_neg, smul_eq_mul, mul_comm] using hg.fourier_smul (-k))
  exact hh.mono fun x hx => sub_eq_zero.mp hx

private theorem at_continuity_point : Expected.Uniqueness.continuityPointStatement := by
  intro T hT f g heq x hf
  let s : Set (Circle T) := {y | f y = g y}
  have hd : Dense s := (haar T).dense_of_ae heq
  have : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd x)
  have he : f =ᶠ[𝓝[s] x] g := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hy
  exact (tendsto_nhds_unique (hf.mono_left nhdsWithin_le_nhds)
    ((g.continuous.continuousAt.mono_left nhdsWithin_le_nhds).congr' he.symm)).symm

private theorem mode_mul_norm (T : ℝ) [Fact (0 < T)] (a : ℂ) (k : ℤ) (x : Circle T) :
    ‖a * mode T k x‖ = ‖a‖ := by
  simp only [norm_mul, mode, fourier_apply, Circle.norm_coe, mul_one]

/-- The Weierstrass test and termwise integration for arbitrary summable coefficients. -/
theorem summable_fourier_synthesis (T : ℝ) [Fact (0 < T)] (a : ℤ → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    ∃ g : C(Circle T, ℂ),
      (∀ x, Summable (fun k => ‖a k * mode T k x‖)) ∧
      (∀ x, HasSum (fun k => a k * mode T k x) (g x)) ∧
      TendstoUniformly (fun s : Finset ℤ => fun x => ∑ k ∈ s, a k * mode T k x) g atTop ∧
      (∀ k, coefficient T g k = a k) := by
  classical
  have hb : ∀ k x, ‖a k * mode T k x‖ ≤ ‖a k‖ := fun k x => (mode_mul_norm T _ k x).le
  let g : C(Circle T, ℂ) := ⟨fun x => ∑' k, a k * mode T k x,
    continuous_tsum (fun k => continuous_const.mul (mode T k).continuous) ha hb⟩
  have habs : ∀ x, Summable (fun k => ‖a k * mode T k x‖) := by
    intro x
    simpa only [mode_mul_norm] using ha
  have hsum : ∀ x, HasSum (fun k => a k * mode T k x) (g x) :=
    fun x => (summable_norm_iff.mp (habs x)).hasSum
  refine ⟨g, habs, hsum, tendstoUniformly_tsum ha hb, ?_⟩
  intro j
  let F : ℤ → Circle T → ℂ := fun k x => (a k * mode T k x) * conj (mode T j x)
  have hFnorm : ∀ k x, ‖F k x‖ = ‖a k‖ := by
    intro k x
    simp only [F, norm_mul, Complex.norm_conj, mode, fourier_apply, Circle.norm_coe, mul_one]
  have hi : HasSum (fun k => ∫ x, F k x ∂haar T) (coefficient T g j) := by
    apply hasSum_integral_of_dominated_convergence (fun k _ => ‖a k‖)
    · intro k
      exact ((continuous_const.mul (mode T k).continuous).mul
        (Complex.continuous_conj.comp (mode T j).continuous)).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun x => (hFnorm k x).le
    · exact ae_of_all _ fun _ => ha
    · exact integrable_const _
    · exact ae_of_all _ fun x => (hsum x).mul_right _
  have hterm : (fun k => ∫ x, F k x ∂haar T) =
      (fun k => if k = j then a j else 0) := by
    ext k
    change coefficient T (fun x => a k * mode T k x) j = _
    rw [coefficient_eq_fourierCoeff, fourierCoeff.const_mul]
    simp only [mode, fourierCoeff_fourier]
    by_cases hk : k = j
    · subst k; simp
    · simp [hk, Ne.symm hk]
  rw [hterm] at hi
  simpa using hi.tsum_eq.symm

/-- Conditional draft: all Fejér premises are retained explicitly in the contract order. -/
theorem fourier_coefficients_zero_ae_conditional
    (_h01 : P102.Periodic.Expected.FejerRecovery.kernelAngularExpansionStatement)
    (_h02 : P102.Periodic.Expected.FejerRecovery.kernelSquareStatement)
    (_h03 : P102.Periodic.Expected.FejerRecovery.concentrationStatement)
    (_h04 : P102.Periodic.Expected.FejerRecovery.kernelDegreeStatement)
    (_h05 : P102.Periodic.Expected.FejerRecovery.kernelAverageStatement)
    (_h06 : P102.Periodic.Expected.FejerRecovery.kernelExpansionStatement)
    (_h07 : P102.Periodic.Expected.FejerRecovery.kernelMassStatement)
    (_h08 : P102.Periodic.Expected.FejerRecovery.outsideBoundStatement)
    (_h09 : P102.Periodic.Expected.FejerRecovery.kernelPositiveStatement)
    (_h10 : P102.Periodic.Expected.FejerRecovery.cesaroStatement)
    (_h11 : P102.Periodic.Expected.FejerRecovery.contractionComplexStatement)
    (_h12 : P102.Periodic.Expected.FejerRecovery.contractionRealStatement)
    (_h13 : P102.Periodic.Expected.FejerRecovery.meanDegreeStatement)
    (_h14 : P102.Periodic.Expected.FejerRecovery.convolutionStatement)
    (_h15 : P102.Periodic.Expected.FejerRecovery.lpComplexStatement)
    (_h16 : P102.Periodic.Expected.FejerRecovery.lpRealStatement)
    (_h17 : P102.Periodic.Expected.FejerRecovery.uniformComplexStatement)
    (_h18 : P102.Periodic.Expected.FejerRecovery.uniformRealStatement)
    (_h19 : P102.Periodic.Expected.FejerRecovery.sineCosineRepresentationStatement)
    (_h20 : P102.Periodic.Expected.FejerRecovery.sineCosineDensityStatement)
    (_h21 : P102.Periodic.Expected.FejerRecovery.lpDensityComplexStatement)
    (_h22 : P102.Periodic.Expected.FejerRecovery.lpDensityRealStatement)
    (_h23 : P102.Periodic.Expected.FejerRecovery.uniformDensityComplexStatement)
    (_h24 : P102.Periodic.Expected.FejerRecovery.uniformDensityRealStatement) :
    Expected.Uniqueness.zeroStatement := by
  exact zero_from_fejer _h15

/-- Conditional draft: all Fejér premises are retained explicitly in the contract order. -/
theorem fourier_coefficients_eq_ae_conditional
    (_h01 : P102.Periodic.Expected.FejerRecovery.kernelAngularExpansionStatement)
    (_h02 : P102.Periodic.Expected.FejerRecovery.kernelSquareStatement)
    (_h03 : P102.Periodic.Expected.FejerRecovery.concentrationStatement)
    (_h04 : P102.Periodic.Expected.FejerRecovery.kernelDegreeStatement)
    (_h05 : P102.Periodic.Expected.FejerRecovery.kernelAverageStatement)
    (_h06 : P102.Periodic.Expected.FejerRecovery.kernelExpansionStatement)
    (_h07 : P102.Periodic.Expected.FejerRecovery.kernelMassStatement)
    (_h08 : P102.Periodic.Expected.FejerRecovery.outsideBoundStatement)
    (_h09 : P102.Periodic.Expected.FejerRecovery.kernelPositiveStatement)
    (_h10 : P102.Periodic.Expected.FejerRecovery.cesaroStatement)
    (_h11 : P102.Periodic.Expected.FejerRecovery.contractionComplexStatement)
    (_h12 : P102.Periodic.Expected.FejerRecovery.contractionRealStatement)
    (_h13 : P102.Periodic.Expected.FejerRecovery.meanDegreeStatement)
    (_h14 : P102.Periodic.Expected.FejerRecovery.convolutionStatement)
    (_h15 : P102.Periodic.Expected.FejerRecovery.lpComplexStatement)
    (_h16 : P102.Periodic.Expected.FejerRecovery.lpRealStatement)
    (_h17 : P102.Periodic.Expected.FejerRecovery.uniformComplexStatement)
    (_h18 : P102.Periodic.Expected.FejerRecovery.uniformRealStatement)
    (_h19 : P102.Periodic.Expected.FejerRecovery.sineCosineRepresentationStatement)
    (_h20 : P102.Periodic.Expected.FejerRecovery.sineCosineDensityStatement)
    (_h21 : P102.Periodic.Expected.FejerRecovery.lpDensityComplexStatement)
    (_h22 : P102.Periodic.Expected.FejerRecovery.lpDensityRealStatement)
    (_h23 : P102.Periodic.Expected.FejerRecovery.uniformDensityComplexStatement)
    (_h24 : P102.Periodic.Expected.FejerRecovery.uniformDensityRealStatement) :
    Expected.Uniqueness.aeEqualityStatement := by
  exact ae_equal_from_fejer _h15

/-- Conditional draft: all Fejér premises are retained explicitly in the contract order. -/
theorem fourier_coefficients_eq_iff_conditional
    (_h01 : P102.Periodic.Expected.FejerRecovery.kernelAngularExpansionStatement)
    (_h02 : P102.Periodic.Expected.FejerRecovery.kernelSquareStatement)
    (_h03 : P102.Periodic.Expected.FejerRecovery.concentrationStatement)
    (_h04 : P102.Periodic.Expected.FejerRecovery.kernelDegreeStatement)
    (_h05 : P102.Periodic.Expected.FejerRecovery.kernelAverageStatement)
    (_h06 : P102.Periodic.Expected.FejerRecovery.kernelExpansionStatement)
    (_h07 : P102.Periodic.Expected.FejerRecovery.kernelMassStatement)
    (_h08 : P102.Periodic.Expected.FejerRecovery.outsideBoundStatement)
    (_h09 : P102.Periodic.Expected.FejerRecovery.kernelPositiveStatement)
    (_h10 : P102.Periodic.Expected.FejerRecovery.cesaroStatement)
    (_h11 : P102.Periodic.Expected.FejerRecovery.contractionComplexStatement)
    (_h12 : P102.Periodic.Expected.FejerRecovery.contractionRealStatement)
    (_h13 : P102.Periodic.Expected.FejerRecovery.meanDegreeStatement)
    (_h14 : P102.Periodic.Expected.FejerRecovery.convolutionStatement)
    (_h15 : P102.Periodic.Expected.FejerRecovery.lpComplexStatement)
    (_h16 : P102.Periodic.Expected.FejerRecovery.lpRealStatement)
    (_h17 : P102.Periodic.Expected.FejerRecovery.uniformComplexStatement)
    (_h18 : P102.Periodic.Expected.FejerRecovery.uniformRealStatement)
    (_h19 : P102.Periodic.Expected.FejerRecovery.sineCosineRepresentationStatement)
    (_h20 : P102.Periodic.Expected.FejerRecovery.sineCosineDensityStatement)
    (_h21 : P102.Periodic.Expected.FejerRecovery.lpDensityComplexStatement)
    (_h22 : P102.Periodic.Expected.FejerRecovery.lpDensityRealStatement)
    (_h23 : P102.Periodic.Expected.FejerRecovery.uniformDensityComplexStatement)
    (_h24 : P102.Periodic.Expected.FejerRecovery.uniformDensityRealStatement) :
    Expected.Uniqueness.classEqualityStatement := by
  intro T hT f g
  constructor
  · intro hc
    apply Lp.ext
    exact ae_equal_from_fejer _h15 T f g (L1.integrable_coeFn f) (L1.integrable_coeFn g) hc
  · intro h
    subst g
    intro k
    rfl

/-- Conditional draft: all Fejér premises are retained explicitly in the contract order. -/
theorem fourier_absolute_inversion_conditional
    (_h01 : P102.Periodic.Expected.FejerRecovery.kernelAngularExpansionStatement)
    (_h02 : P102.Periodic.Expected.FejerRecovery.kernelSquareStatement)
    (_h03 : P102.Periodic.Expected.FejerRecovery.concentrationStatement)
    (_h04 : P102.Periodic.Expected.FejerRecovery.kernelDegreeStatement)
    (_h05 : P102.Periodic.Expected.FejerRecovery.kernelAverageStatement)
    (_h06 : P102.Periodic.Expected.FejerRecovery.kernelExpansionStatement)
    (_h07 : P102.Periodic.Expected.FejerRecovery.kernelMassStatement)
    (_h08 : P102.Periodic.Expected.FejerRecovery.outsideBoundStatement)
    (_h09 : P102.Periodic.Expected.FejerRecovery.kernelPositiveStatement)
    (_h10 : P102.Periodic.Expected.FejerRecovery.cesaroStatement)
    (_h11 : P102.Periodic.Expected.FejerRecovery.contractionComplexStatement)
    (_h12 : P102.Periodic.Expected.FejerRecovery.contractionRealStatement)
    (_h13 : P102.Periodic.Expected.FejerRecovery.meanDegreeStatement)
    (_h14 : P102.Periodic.Expected.FejerRecovery.convolutionStatement)
    (_h15 : P102.Periodic.Expected.FejerRecovery.lpComplexStatement)
    (_h16 : P102.Periodic.Expected.FejerRecovery.lpRealStatement)
    (_h17 : P102.Periodic.Expected.FejerRecovery.uniformComplexStatement)
    (_h18 : P102.Periodic.Expected.FejerRecovery.uniformRealStatement)
    (_h19 : P102.Periodic.Expected.FejerRecovery.sineCosineRepresentationStatement)
    (_h20 : P102.Periodic.Expected.FejerRecovery.sineCosineDensityStatement)
    (_h21 : P102.Periodic.Expected.FejerRecovery.lpDensityComplexStatement)
    (_h22 : P102.Periodic.Expected.FejerRecovery.lpDensityRealStatement)
    (_h23 : P102.Periodic.Expected.FejerRecovery.uniformDensityComplexStatement)
    (_h24 : P102.Periodic.Expected.FejerRecovery.uniformDensityRealStatement) :
    Expected.Uniqueness.inversionStatement := by
  intro T hT f hf ha
  obtain ⟨g, habs, hsum, hu, hc⟩ := summable_fourier_synthesis T (coefficient T f) ha
  have hg : Integrable (g : Circle T → ℂ) (haar T) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq : f =ᵐ[haar T] g := ae_equal_from_fejer _h15 T f g hf hg (fun k => (hc k).symm)
  exact ⟨g, habs, hsum, hu, hc, heq, at_continuity_point T f g heq⟩

/-- Conditional draft: all Fejér premises are retained explicitly in the contract order. -/
theorem fourier_continuity_point_conditional
    (_h01 : P102.Periodic.Expected.FejerRecovery.kernelAngularExpansionStatement)
    (_h02 : P102.Periodic.Expected.FejerRecovery.kernelSquareStatement)
    (_h03 : P102.Periodic.Expected.FejerRecovery.concentrationStatement)
    (_h04 : P102.Periodic.Expected.FejerRecovery.kernelDegreeStatement)
    (_h05 : P102.Periodic.Expected.FejerRecovery.kernelAverageStatement)
    (_h06 : P102.Periodic.Expected.FejerRecovery.kernelExpansionStatement)
    (_h07 : P102.Periodic.Expected.FejerRecovery.kernelMassStatement)
    (_h08 : P102.Periodic.Expected.FejerRecovery.outsideBoundStatement)
    (_h09 : P102.Periodic.Expected.FejerRecovery.kernelPositiveStatement)
    (_h10 : P102.Periodic.Expected.FejerRecovery.cesaroStatement)
    (_h11 : P102.Periodic.Expected.FejerRecovery.contractionComplexStatement)
    (_h12 : P102.Periodic.Expected.FejerRecovery.contractionRealStatement)
    (_h13 : P102.Periodic.Expected.FejerRecovery.meanDegreeStatement)
    (_h14 : P102.Periodic.Expected.FejerRecovery.convolutionStatement)
    (_h15 : P102.Periodic.Expected.FejerRecovery.lpComplexStatement)
    (_h16 : P102.Periodic.Expected.FejerRecovery.lpRealStatement)
    (_h17 : P102.Periodic.Expected.FejerRecovery.uniformComplexStatement)
    (_h18 : P102.Periodic.Expected.FejerRecovery.uniformRealStatement)
    (_h19 : P102.Periodic.Expected.FejerRecovery.sineCosineRepresentationStatement)
    (_h20 : P102.Periodic.Expected.FejerRecovery.sineCosineDensityStatement)
    (_h21 : P102.Periodic.Expected.FejerRecovery.lpDensityComplexStatement)
    (_h22 : P102.Periodic.Expected.FejerRecovery.lpDensityRealStatement)
    (_h23 : P102.Periodic.Expected.FejerRecovery.uniformDensityComplexStatement)
    (_h24 : P102.Periodic.Expected.FejerRecovery.uniformDensityRealStatement) :
    Expected.Uniqueness.continuityPointStatement := by
  exact at_continuity_point

end P102.Periodic

theorem _root_.«P102».«Periodic».«fourier_absolute_inversion» : _root_.«P102».«Periodic».«Expected».«Uniqueness».«inversionStatement» :=
  @_root_.«P102».«Periodic».«fourier_absolute_inversion_conditional» (@_root_.«P102».«Periodic».«fejerKernel_angular_expansion») (@_root_.«P102».«Periodic».«fejerKernel_angular_square») (@_root_.«P102».«Periodic».«fejerKernel_concentration») (@_root_.«P102».«Periodic».«fejerKernel_degree») (@_root_.«P102».«Periodic».«fejerKernel_eq_average») (@_root_.«P102».«Periodic».«fejerKernel_expansion») (@_root_.«P102».«Periodic».«fejerKernel_mass») (@_root_.«P102».«Periodic».«fejerKernel_outside_bound») (@_root_.«P102».«Periodic».«fejerKernel_positive») (@_root_.«P102».«Periodic».«fejerMean_cesaro») (@_root_.«P102».«Periodic».«fejerMean_contraction_complex») (@_root_.«P102».«Periodic».«fejerMean_contraction_real») (@_root_.«P102».«Periodic».«fejerMean_degree») (@_root_.«P102».«Periodic».«fejerMean_eq_convolution») (@_root_.«P102».«Periodic».«fejerMean_lp_complex») (@_root_.«P102».«Periodic».«fejerMean_lp_real») (@_root_.«P102».«Periodic».«fejerMean_uniform_complex») (@_root_.«P102».«Periodic».«fejerMean_uniform_real») (@_root_.«P102».«Periodic».«real_trig_sine_cosine») (@_root_.«P102».«Periodic».«sine_cosine_uniform_density») (@_root_.«P102».«Periodic».«trig_lp_density_complex») (@_root_.«P102».«Periodic».«trig_lp_density_real») (@_root_.«P102».«Periodic».«trig_uniform_density_complex») (@_root_.«P102».«Periodic».«trig_uniform_density_real»)
theorem _root_.«P102».«Periodic».«fourier_coefficients_eq_ae» : _root_.«P102».«Periodic».«Expected».«Uniqueness».«aeEqualityStatement» :=
  @_root_.«P102».«Periodic».«fourier_coefficients_eq_ae_conditional» (@_root_.«P102».«Periodic».«fejerKernel_angular_expansion») (@_root_.«P102».«Periodic».«fejerKernel_angular_square») (@_root_.«P102».«Periodic».«fejerKernel_concentration») (@_root_.«P102».«Periodic».«fejerKernel_degree») (@_root_.«P102».«Periodic».«fejerKernel_eq_average») (@_root_.«P102».«Periodic».«fejerKernel_expansion») (@_root_.«P102».«Periodic».«fejerKernel_mass») (@_root_.«P102».«Periodic».«fejerKernel_outside_bound») (@_root_.«P102».«Periodic».«fejerKernel_positive») (@_root_.«P102».«Periodic».«fejerMean_cesaro») (@_root_.«P102».«Periodic».«fejerMean_contraction_complex») (@_root_.«P102».«Periodic».«fejerMean_contraction_real») (@_root_.«P102».«Periodic».«fejerMean_degree») (@_root_.«P102».«Periodic».«fejerMean_eq_convolution») (@_root_.«P102».«Periodic».«fejerMean_lp_complex») (@_root_.«P102».«Periodic».«fejerMean_lp_real») (@_root_.«P102».«Periodic».«fejerMean_uniform_complex») (@_root_.«P102».«Periodic».«fejerMean_uniform_real») (@_root_.«P102».«Periodic».«real_trig_sine_cosine») (@_root_.«P102».«Periodic».«sine_cosine_uniform_density») (@_root_.«P102».«Periodic».«trig_lp_density_complex») (@_root_.«P102».«Periodic».«trig_lp_density_real») (@_root_.«P102».«Periodic».«trig_uniform_density_complex») (@_root_.«P102».«Periodic».«trig_uniform_density_real»)
theorem _root_.«P102».«Periodic».«fourier_coefficients_eq_iff» : _root_.«P102».«Periodic».«Expected».«Uniqueness».«classEqualityStatement» :=
  @_root_.«P102».«Periodic».«fourier_coefficients_eq_iff_conditional» (@_root_.«P102».«Periodic».«fejerKernel_angular_expansion») (@_root_.«P102».«Periodic».«fejerKernel_angular_square») (@_root_.«P102».«Periodic».«fejerKernel_concentration») (@_root_.«P102».«Periodic».«fejerKernel_degree») (@_root_.«P102».«Periodic».«fejerKernel_eq_average») (@_root_.«P102».«Periodic».«fejerKernel_expansion») (@_root_.«P102».«Periodic».«fejerKernel_mass») (@_root_.«P102».«Periodic».«fejerKernel_outside_bound») (@_root_.«P102».«Periodic».«fejerKernel_positive») (@_root_.«P102».«Periodic».«fejerMean_cesaro») (@_root_.«P102».«Periodic».«fejerMean_contraction_complex») (@_root_.«P102».«Periodic».«fejerMean_contraction_real») (@_root_.«P102».«Periodic».«fejerMean_degree») (@_root_.«P102».«Periodic».«fejerMean_eq_convolution») (@_root_.«P102».«Periodic».«fejerMean_lp_complex») (@_root_.«P102».«Periodic».«fejerMean_lp_real») (@_root_.«P102».«Periodic».«fejerMean_uniform_complex») (@_root_.«P102».«Periodic».«fejerMean_uniform_real») (@_root_.«P102».«Periodic».«real_trig_sine_cosine») (@_root_.«P102».«Periodic».«sine_cosine_uniform_density») (@_root_.«P102».«Periodic».«trig_lp_density_complex») (@_root_.«P102».«Periodic».«trig_lp_density_real») (@_root_.«P102».«Periodic».«trig_uniform_density_complex») (@_root_.«P102».«Periodic».«trig_uniform_density_real»)
theorem _root_.«P102».«Periodic».«fourier_coefficients_zero_ae» : _root_.«P102».«Periodic».«Expected».«Uniqueness».«zeroStatement» :=
  @_root_.«P102».«Periodic».«fourier_coefficients_zero_ae_conditional» (@_root_.«P102».«Periodic».«fejerKernel_angular_expansion») (@_root_.«P102».«Periodic».«fejerKernel_angular_square») (@_root_.«P102».«Periodic».«fejerKernel_concentration») (@_root_.«P102».«Periodic».«fejerKernel_degree») (@_root_.«P102».«Periodic».«fejerKernel_eq_average») (@_root_.«P102».«Periodic».«fejerKernel_expansion») (@_root_.«P102».«Periodic».«fejerKernel_mass») (@_root_.«P102».«Periodic».«fejerKernel_outside_bound») (@_root_.«P102».«Periodic».«fejerKernel_positive») (@_root_.«P102».«Periodic».«fejerMean_cesaro») (@_root_.«P102».«Periodic».«fejerMean_contraction_complex») (@_root_.«P102».«Periodic».«fejerMean_contraction_real») (@_root_.«P102».«Periodic».«fejerMean_degree») (@_root_.«P102».«Periodic».«fejerMean_eq_convolution») (@_root_.«P102».«Periodic».«fejerMean_lp_complex») (@_root_.«P102».«Periodic».«fejerMean_lp_real») (@_root_.«P102».«Periodic».«fejerMean_uniform_complex») (@_root_.«P102».«Periodic».«fejerMean_uniform_real») (@_root_.«P102».«Periodic».«real_trig_sine_cosine») (@_root_.«P102».«Periodic».«sine_cosine_uniform_density») (@_root_.«P102».«Periodic».«trig_lp_density_complex») (@_root_.«P102».«Periodic».«trig_lp_density_real») (@_root_.«P102».«Periodic».«trig_uniform_density_complex») (@_root_.«P102».«Periodic».«trig_uniform_density_real»)
theorem _root_.«P102».«Periodic».«fourier_continuity_point» : _root_.«P102».«Periodic».«Expected».«Uniqueness».«continuityPointStatement» :=
  @_root_.«P102».«Periodic».«fourier_continuity_point_conditional» (@_root_.«P102».«Periodic».«fejerKernel_angular_expansion») (@_root_.«P102».«Periodic».«fejerKernel_angular_square») (@_root_.«P102».«Periodic».«fejerKernel_concentration») (@_root_.«P102».«Periodic».«fejerKernel_degree») (@_root_.«P102».«Periodic».«fejerKernel_eq_average») (@_root_.«P102».«Periodic».«fejerKernel_expansion») (@_root_.«P102».«Periodic».«fejerKernel_mass») (@_root_.«P102».«Periodic».«fejerKernel_outside_bound») (@_root_.«P102».«Periodic».«fejerKernel_positive») (@_root_.«P102».«Periodic».«fejerMean_cesaro») (@_root_.«P102».«Periodic».«fejerMean_contraction_complex») (@_root_.«P102».«Periodic».«fejerMean_contraction_real») (@_root_.«P102».«Periodic».«fejerMean_degree») (@_root_.«P102».«Periodic».«fejerMean_eq_convolution») (@_root_.«P102».«Periodic».«fejerMean_lp_complex») (@_root_.«P102».«Periodic».«fejerMean_lp_real») (@_root_.«P102».«Periodic».«fejerMean_uniform_complex») (@_root_.«P102».«Periodic».«fejerMean_uniform_real») (@_root_.«P102».«Periodic».«real_trig_sine_cosine») (@_root_.«P102».«Periodic».«sine_cosine_uniform_density») (@_root_.«P102».«Periodic».«trig_lp_density_complex») (@_root_.«P102».«Periodic».«trig_lp_density_real») (@_root_.«P102».«Periodic».«trig_uniform_density_complex») (@_root_.«P102».«Periodic».«trig_uniform_density_real»)
