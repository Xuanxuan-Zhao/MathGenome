import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SmoothPaleyWiener
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros

open MeasureTheory Set
open scoped ContDiff

noncomputable section
namespace ExpandedFA.Fourier.PaleyWiener

lemma complexPairing_realFrequency {d : ℕ} (x ξ : Euclidean d) :
    complexPairing x (realFrequency ξ) = (inner ℝ x ξ : ℝ) := by
  simp [complexPairing, realFrequency, PiLp.inner_apply, RCLike.inner_apply,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, mul_comm]

lemma complexPairing_im {d : ℕ} (x : Euclidean d) (z : ComplexEuclidean d) :
    (complexPairing x z).im = inner ℝ x (imaginaryPart z) := by
  simp [complexPairing, imaginaryPart, Complex.mul_im, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

theorem real_restriction :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.realRestrictionType := by
  intro d f ξ
  simp only [fourierLaplace, integralFourier, complexPairing_realFrequency]

theorem kernel_norm :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.kernelNormType := by
  intro d x z
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, complexPairing_im]

lemma supportFunction_bddAbove {d : ℕ} {K : Set (Euclidean d)} (hK : IsCompact K)
    (η : Euclidean d) : BddAbove ((fun x => inner ℝ x η) '' K) :=
  (hK.image (by fun_prop)).bddAbove

lemma inner_le_supportFunction {d : ℕ} {K : Set (Euclidean d)} (hK : IsCompact K)
    {x : Euclidean d} (hx : x ∈ K) (η : Euclidean d) :
    inner ℝ x η ≤ supportFunction K η :=
  le_csSup (supportFunction_bddAbove hK η) (mem_image_of_mem _ hx)

lemma supportFunction_zero {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty) :
    supportFunction K 0 = 0 := by
  simp only [supportFunction, inner_zero_right]
  rw [hne.image_const, csSup_singleton]

lemma supportFunction_smul_nonneg {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) (η : Euclidean d) {t : ℝ} (ht : 0 ≤ t) :
    supportFunction K (t • η) = t * supportFunction K η := by
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne (show ContinuousOn (fun x => inner ℝ x η) K by fun_prop)
  have hsup : supportFunction K η = inner ℝ y η := by
    apply le_antisymm
    · exact csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hmax hx)
    · exact inner_le_supportFunction hK hy η
  rw [hsup]
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hmax hx) ht
  · simpa only [inner_smul_right] using inner_le_supportFunction hK hy (t • η)

theorem separation :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.separationType := by
  intro d K hne hK hconv x hx
  obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hx
  let η := (InnerProductSpace.toDual ℝ (Euclidean d)).symm l
  have hη (y : Euclidean d) : inner ℝ y η = l y := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨η, ?_⟩
  rw [hη]
  exact lt_of_le_of_lt (csSup_le (hne.image _) (by
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [hη]
    exact (hlu y hy).le)) hux

lemma SmoothSupportedIn.hasCompactSupport {d : ℕ} {K : Set (Euclidean d)}
    {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f) (hK : IsCompact K) :
    HasCompactSupport f :=
  hK.of_isClosed_subset isClosed_closure hf.2

lemma fourierLaplace_integrable {d : ℕ} {K : Set (Euclidean d)}
    {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f) (hK : IsCompact K)
    (z : ComplexEuclidean d) : Integrable (fun x =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z) * f x) := by
  have hc : Continuous (fun x =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z) * f x) := by
    have hfc : Continuous f := hf.1.continuous
    unfold complexPairing
    fun_prop
  exact hc.integrable_of_hasCompactSupport (hf.hasCompactSupport hK).mul_left

theorem zeroth_bound :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.zerothBoundType := by
  intro d K _hne hK f hf z
  have hfi : Integrable f (volume : Measure (Euclidean d)) :=
    hf.1.continuous.integrable_of_hasCompactSupport (hf.hasCompactSupport hK)
  have hzi := fourierLaplace_integrable hf hK z
  calc
    ‖fourierLaplace f z‖ ≤ ∫ x, ‖Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z) * f x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ * Real.exp
        (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
      apply integral_mono hzi.norm (hfi.norm.mul_const _)
      intro x
      dsimp only
      rw [norm_mul, kernel_norm]
      by_cases hx : f x = 0
      · simp [hx]
      · have hxK : x ∈ K := hf.2 (subset_tsupport f hx)
        rw [mul_comm ‖(f x)‖]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (inner_le_supportFunction hK hxK _)
          (by positivity)
    _ = _ := integral_mul_const _ _

theorem smooth_inversion :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.smoothInversionType := by
  intro d K hK f hf
  let g : Schwartz ℂ d := (hf.hasCompactSupport hK).toSchwartzMap hf.1
  ext x
  change (∫ ξ : Euclidean d, Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
      fourierLaplace f (realFrequency ξ)) = f x
  calc
    _ = ∫ ξ : Euclidean d, Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) * schwartzFourier g ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      congr 1
      exact (real_restriction d f ξ).trans (schwartz_integral d g ξ).symm
    _ = f x := (Inversion.inversion d g x).symm

theorem injectivity :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.injectivityType := by
  intro d K L hK hL f g hf hg hfg
  rw [← smooth_inversion d K hK f hf, hfg]
  exact smooth_inversion d L hL g hg

@[simp] lemma imaginaryPart_realFrequency {d : ℕ} (ξ : Euclidean d) :
    imaginaryPart (realFrequency ξ) = 0 := by
  ext j
  simp [imaginaryPart, realFrequency]

@[simp] lemma norm_realFrequency {d : ℕ} (ξ : Euclidean d) :
    ‖realFrequency ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, realFrequency]

@[fun_prop] lemma continuous_realFrequency (d : ℕ) : Continuous (@realFrequency d) := by
  unfold realFrequency
  fun_prop

lemma real_axis_bound {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hF : RapidExponentialType K F) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euclidean d,
      ‖F (realFrequency ξ)‖ ≤ C * (1 + ‖ξ‖) ^ (-(N : ℤ)) := by
  obtain ⟨C, hC, h⟩ := hF N
  refine ⟨C, hC, fun ξ => ?_⟩
  simpa [supportFunction_zero hne] using h (realFrequency ξ)

lemma real_axis_integrable {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hcont : Continuous F) (hF : RapidExponentialType K F) :
    Integrable (fun ξ : Euclidean d => F (realFrequency ξ)) := by
  let N := Module.finrank ℝ (Euclidean d) + 1
  obtain ⟨C, _hC, h⟩ := real_axis_bound hne hF N
  have hi : Integrable (fun ξ : Euclidean d => (1 + ‖ξ‖) ^ (-(N : ℤ))) := by
    simp_rw [← Real.rpow_neg_natCast]
    apply integrable_one_add_norm
    dsimp [N]
    norm_num
  exact (hi.const_mul C).mono' ((hcont.comp (continuous_realFrequency d)).aestronglyMeasurable)
    (Filter.Eventually.of_forall h)

lemma inverse_integrable {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hcont : Continuous F) (hF : RapidExponentialType K F)
    (x : Euclidean d) : Integrable (fun ξ : Euclidean d =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
        F (realFrequency ξ)) := by
  have hfi := real_axis_integrable hne hcont hF
  apply hfi.norm.mono' _
    (Filter.Eventually.of_forall (fun ξ => ?_))
  · apply Continuous.aestronglyMeasurable
    have hfc := hcont.comp (continuous_realFrequency d)
    fun_prop
  · simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

lemma continuous_inverse {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hcont : Continuous F) (hF : RapidExponentialType K F) :
    Continuous (inverseRealIntegral F) := by
  unfold inverseRealIntegral
  apply continuous_of_dominated (bound := fun ξ : Euclidean d => ‖F (realFrequency ξ)‖)
  · intro x
    exact (inverse_integrable hne hcont hF x).aestronglyMeasurable
  · intro x
    filter_upwards [] with ξ
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  · exact (real_axis_integrable hne hcont hF).norm
  · filter_upwards [] with ξ
    fun_prop

theorem inverse_convergence :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.inverseConvergenceType := by
  intro d K hne F hdiff hF
  exact ⟨inverse_integrable hne hdiff.continuous hF,
    continuous_inverse hne hdiff.continuous hF⟩

/-- This is the final limiting step of the contour argument. The shifted
 estimate is a hypothesis of this helper; `contour_shift` below supplies it
 for the actual inverse integral. -/
lemma vanishes_of_shifted_bound {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) (hconv : Convex ℝ K)
    {f : Euclidean d → ℂ} {x : Euclidean d} (hx : x ∉ K)
    (hbound : ∀ η : Euclidean d, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖f x‖ ≤ C * Real.exp (-(2 * Real.pi * t *
        (inner ℝ x η - supportFunction K η)))) : f x = 0 := by
  obtain ⟨η, hη⟩ := separation d K hne hK hconv x hx
  obtain ⟨C, hC⟩ := hbound η
  let a : ℝ := 2 * Real.pi * (inner ℝ x η - supportFunction K η)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlim : Filter.Tendsto (fun t : ℝ => C * Real.exp (-(a * t)))
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Filter.tendsto_const_mul_atTop_of_pos ha).mpr Filter.tendsto_id)).const_mul C
  have hle : ‖f x‖ ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    convert hC t ht using 1
    dsimp [a]
    congr 2
    ring
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

lemma support_subset_of_shifted_bound {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) (hconv : Convex ℝ K)
    {f : Euclidean d → ℂ}
    (hbound : ∀ x η : Euclidean d, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖f x‖ ≤ C * Real.exp (-(2 * Real.pi * t *
        (inner ℝ x η - supportFunction K η)))) : tsupport f ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  exact hx (vanishes_of_shifted_bound hne hK hconv hxK (hbound x))

/-- All polynomial moments of the real restriction are integrable. -/
lemma real_axis_moment_integrable {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hcont : Continuous F)
    (hF : RapidExponentialType K F) (n : ℕ) :
    Integrable (fun ξ : Euclidean d => ‖ξ‖ ^ n * ‖F (realFrequency ξ)‖) := by
  let M := Module.finrank ℝ (Euclidean d) + 1
  obtain ⟨C, hC, h⟩ := real_axis_bound hne hF (n + M)
  have hi : Integrable (fun ξ : Euclidean d => (1 + ‖ξ‖) ^ (-(M : ℤ))) := by
    simp_rw [← Real.rpow_neg_natCast]
    apply integrable_one_add_norm
    dsimp [M]
    norm_num
  apply (hi.const_mul C).mono'
    (by apply Continuous.aestronglyMeasurable; fun_prop)
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : 0 < 1 + ‖ξ‖ := by positivity
  calc
    ‖ξ‖ ^ n * ‖F (realFrequency ξ)‖ ≤
        (1 + ‖ξ‖) ^ n * (C * (1 + ‖ξ‖) ^ (-((n + M : ℕ) : ℤ))) := by
      gcongr
      · exact le_add_of_nonneg_left zero_le_one
      · exact h ξ
    _ = C * (1 + ‖ξ‖) ^ (-(M : ℤ)) := by
      rw [← zpow_natCast (1 + ‖ξ‖) n]
      rw [mul_left_comm, ← zpow_add₀ hp.ne']
      congr 2
      omega

/-- Rapid decay of the entire function already suffices for smoothness of
its inverse integral; support and transform recovery require further arguments. -/
lemma contDiff_inverse {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hcont : Continuous F)
    (hF : RapidExponentialType K F) : ContDiff ℝ ∞ (inverseRealIntegral F) := by
  have hdiff : ContDiff ℝ ∞
      (FourierTransform.fourier (fun ξ : Euclidean d => F (realFrequency ξ))) :=
    Real.contDiff_fourier (fun n _ => real_axis_moment_integrable hne hcont hF n)
  have heq : inverseRealIntegral F = fun x : Euclidean d =>
      FourierTransform.fourier (fun ξ : Euclidean d => F (realFrequency ξ)) (-x) := by
    funext x
    rw [Real.fourier_eq]
    unfold inverseRealIntegral
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [inner_neg_right, real_inner_comm ξ x]
    congr 2
    push_cast
    ring
  rw [heq]
  exact hdiff.comp contDiff_neg

/-- The linear exponent in the complex frequency variable. -/
def laplaceExponentCLM {d : ℕ} (x : Euclidean d) : ComplexEuclidean d →L[ℂ] ℂ :=
  ∑ j, (-2 * (Real.pi : ℂ) * Complex.I * (x j : ℂ)) • EuclideanSpace.proj j

lemma laplaceExponentCLM_apply {d : ℕ} (x : Euclidean d) (z : ComplexEuclidean d) :
    laplaceExponentCLM x z = -2 * (Real.pi : ℂ) * Complex.I * complexPairing x z := by
  simp only [laplaceExponentCLM, sum_apply,
    smul_apply, smul_eq_mul, EuclideanSpace.coe_proj,
    complexPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[fun_prop] lemma continuous_laplaceExponentCLM (d : ℕ) :
    Continuous (@laplaceExponentCLM d) := by
  unfold laplaceExponentCLM
  fun_prop

lemma laplace_integrand_hasFDerivAt {d : ℕ} (f : Euclidean d → ℂ)
    (x : Euclidean d) (z : ComplexEuclidean d) :
    HasFDerivAt (fun w : ComplexEuclidean d =>
      Complex.exp (laplaceExponentCLM x w) * f x)
      ((Complex.exp (laplaceExponentCLM x z) * f x) • laplaceExponentCLM x) z := by
  convert ((laplaceExponentCLM x).hasFDerivAt.cexp.mul_const (f x)) using 1
  ext w
  simp [mul_comm, mul_left_comm]

/-- Compact support gives an integrable local uniform bound for the complex
frequency derivative, so differentiation under the actual integral is valid. -/
lemma differentiable_fourierLaplace {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsCompact K) {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f) :
    Differentiable ℂ (fourierLaplace f) := by
  have hfc := hf.1.continuous
  let G : ComplexEuclidean d → Euclidean d → ℂ :=
    fun z x => Complex.exp (laplaceExponentCLM x z) * f x
  let G' : ComplexEuclidean d → Euclidean d → ComplexEuclidean d →L[ℂ] ℂ :=
    fun z x => G z x • laplaceExponentCLM x
  have hG : Continuous (fun p : ComplexEuclidean d × Euclidean d => G p.1 p.2) := by
    dsimp [G]
    fun_prop
  have hG' : Continuous (fun p : ComplexEuclidean d × Euclidean d => G' p.1 p.2) := by
    dsimp [G']
    exact (hG.smul ((continuous_laplaceExponentCLM d).comp continuous_snd))
  have heq : fourierLaplace f = fun z => ∫ x in K, G z x := by
    funext z
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [fourierLaplace, G, laplaceExponentCLM_apply]
    · intro x hx
      have hfx : f x = 0 := by
        by_contra h
        exact hx (hf.2 (subset_tsupport f h))
      simp [G, hfx]
  rw [heq]
  intro z₀
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod hK).exists_bound_of_continuousOn
    hG'.continuousOn
  have hfin : (volume : Measure (Euclidean d)) K < ⊤ := hK.measure_lt_top
  let : IsFiniteMeasure ((volume : Measure (Euclidean d)).restrict K) :=
    ⟨by simpa using hfin⟩
  apply HasFDerivAt.differentiableAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := G') (bound := fun _ => C) (s := Metric.ball z₀ 1)
    (Metric.ball_mem_nhds z₀ zero_lt_one)
  · exact Filter.Eventually.of_forall (fun z =>
      (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact ((hG.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK)
  · exact (hG'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro z hz
    exact hC (z, x) ⟨Metric.ball_subset_closedBall hz, hx⟩
  · exact integrable_const C
  · filter_upwards [] with x
    intro z _
    exact laplace_integrand_hasFDerivAt f x z

/-- The same exponent, now linear over the real spatial variable. -/
def spatialExponentCLM {d : ℕ} (z : ComplexEuclidean d) : Euclidean d →L[ℝ] ℂ :=
  ∑ j, (-2 * (Real.pi : ℂ) * Complex.I * z j) •
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j))

lemma spatialExponentCLM_apply {d : ℕ} (z : ComplexEuclidean d) (x : Euclidean d) :
    spatialExponentCLM z x = -2 * (Real.pi : ℂ) * Complex.I * complexPairing x z := by
  simp only [spatialExponentCLM, sum_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, EuclideanSpace.coe_proj,
    complexPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma SmoothSupportedIn.fderiv_apply {d : ℕ} {K : Set (Euclidean d)}
    {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f) (v : Euclidean d) :
    SmoothSupportedIn K (fun x => fderiv ℝ f x v) := by
  refine ⟨?_, (tsupport_fderiv_apply_subset ℝ v).trans hf.2⟩
  exact (hf.1.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)

/-- Integration by parts holds also at complex frequencies, with exactly
 the adopted factor `2πi`. -/
lemma fourierLaplace_fderiv {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsCompact K) {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f)
    (v : Euclidean d) (z : ComplexEuclidean d) :
    fourierLaplace (fun x => fderiv ℝ f x v) z =
      (2 * (Real.pi : ℂ) * Complex.I * complexPairing v z) * fourierLaplace f z := by
  let k : Euclidean d → ℂ := fun x => Complex.exp (spatialExponentCLM z x)
  let k' : Euclidean d → Euclidean d →L[ℝ] ℂ :=
    fun x => k x • spatialExponentCLM z
  have hk (x : Euclidean d) : HasFDerivAt k (k' x) x :=
    (spatialExponentCLM z).hasFDerivAt.cexp
  have hki : Integrable (fun x => k x * f x) := by
    simpa only [k, spatialExponentCLM_apply] using fourierLaplace_integrable hf hK z
  have hkdi : Integrable (fun x => k x * fderiv ℝ f x v) := by
    simpa only [k, spatialExponentCLM_apply] using
      fourierLaplace_integrable (hf.fderiv_apply v) hK z
  have hk'i : Integrable (fun x => k' x v * f x) := by
    simpa only [k', smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      hki.const_mul (spatialExponentCLM z v)
  have hi := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := v) hk'i hkdi hki
    (fun x _ => hk x) (fun x _ => (hf.1.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change (∫ x, k x * fderiv ℝ f x v) = -(∫ x, k' x v * f x) at hi
  have heq : (∫ x, k' x v * f x) = spatialExponentCLM z v * fourierLaplace f z := by
    unfold fourierLaplace
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [k', smul_apply, smul_eq_mul, k, spatialExponentCLM_apply]
    ring
  rw [heq, spatialExponentCLM_apply] at hi
  simpa only [k, spatialExponentCLM_apply, fourierLaplace, neg_mul,
    neg_neg] using hi

lemma complexPairing_basisVector {d : ℕ} (j : Fin d) (z : ComplexEuclidean d) :
    complexPairing (basisVector j) z = z j := by
  classical
  simp [complexPairing, basisVector, PiLp.single_apply, apply_ite]

lemma norm_le_sum_coordinates {d : ℕ} (z : ComplexEuclidean d) : ‖z‖ ≤ ∑ j, ‖z j‖ := by
  have heq : z = ∑ j, EuclideanSpace.single j (z j) := by
    ext j
    simp
  calc
    ‖z‖ = ‖∑ j, EuclideanSpace.single j (z j)‖ := congrArg norm heq
    _ ≤ ∑ j, ‖EuclideanSpace.single j (z j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖z j‖ := by simp only [PiLp.norm_single]

lemma norm_mul_fourierLaplace_le_sum_derivatives {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsCompact K) {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f)
    (z : ComplexEuclidean d) :
    ‖z‖ * ‖fourierLaplace f z‖ ≤
      ∑ j, ‖fourierLaplace (fun x => fderiv ℝ f x (basisVector j)) z‖ := by
  calc
    ‖z‖ * ‖fourierLaplace f z‖ ≤ (∑ j, ‖z j‖) * ‖fourierLaplace f z‖ :=
      mul_le_mul_of_nonneg_right (norm_le_sum_coordinates z) (norm_nonneg _)
    _ = ∑ j, ‖z j‖ * ‖fourierLaplace f z‖ := Finset.sum_mul _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [fourierLaplace_fderiv hK hf, complexPairing_basisVector]
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [mul_nonneg (norm_nonneg (z j)) (norm_nonneg (fourierLaplace f z))]

/-- Polynomially weighted estimates follow inductively by integration by
 parts. Summing over coordinates also treats the zero-dimensional case. -/
lemma weighted_fourierLaplace_bound {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) (N : ℕ) :
    ∀ (f : Euclidean d → ℂ), SmoothSupportedIn K f →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ComplexEuclidean d,
      (1 + ‖z‖) ^ N * ‖fourierLaplace f z‖ ≤
        C * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
  induction N with
  | zero =>
    intro f hf
    refine ⟨∫ x, ‖f x‖, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
    simpa only [pow_zero, one_mul] using zeroth_bound d K hne hK f hf
  | succ N ih =>
    intro f hf
    obtain ⟨C, hC, hb⟩ := ih f hf
    have hd : ∀ j : Fin d, ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ComplexEuclidean d,
        (1 + ‖z‖) ^ N * ‖fourierLaplace
          (fun x => fderiv ℝ f x (basisVector j)) z‖ ≤
          D * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) :=
      fun j => ih _ (hf.fderiv_apply (basisVector j))
    choose D hD hbD using hd
    refine ⟨C + ∑ j, D j, add_nonneg hC (Finset.sum_nonneg (fun j _ => hD j)), ?_⟩
    intro z
    calc
      (1 + ‖z‖) ^ (N + 1) * ‖fourierLaplace f z‖ =
          (1 + ‖z‖) ^ N * ‖fourierLaplace f z‖ +
          (1 + ‖z‖) ^ N * (‖z‖ * ‖fourierLaplace f z‖) := by
        rw [pow_succ]; ring
      _ ≤ C * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) +
          (1 + ‖z‖) ^ N * ∑ j,
            ‖fourierLaplace (fun x => fderiv ℝ f x (basisVector j)) z‖ :=
        add_le_add (hb z) (mul_le_mul_of_nonneg_left
          (norm_mul_fourierLaplace_le_sum_derivatives hK hf z) (by positivity))
      _ ≤ C * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) +
          ∑ j, D j * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
        gcongr
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _ => hbD j z)
      _ = _ := by rw [add_mul, Finset.sum_mul]

lemma rapidExponentialType_fourierLaplace {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) {f : Euclidean d → ℂ}
    (hf : SmoothSupportedIn K f) : RapidExponentialType K (fourierLaplace f) := by
  intro N
  obtain ⟨C, hC, hb⟩ := weighted_fourierLaplace_bound hne hK N f hf
  refine ⟨C, hC, fun z => ?_⟩
  have hp : 0 < (1 + ‖z‖) ^ N := by positivity
  have h := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hb z)
  simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem forward : Specs.ExpandedFA.Fourier.SmoothPaleyWiener.forwardType := by
  intro d K hne hK _hconv f hf
  exact ⟨differentiable_fourierLaplace hK hf, rapidExponentialType_fourierLaplace hne hK hf⟩

theorem inverse_smoothness :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.inverseSmoothnessType := by
  intro d K hne F hdiff hF
  exact contDiff_inverse hne hdiff.continuous hF

/-- One-variable identity theorem with agreement along the real axis. -/
lemma entire_eq_of_eq_on_reals {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (heq : ∀ r : ℝ, f r = g r) : f = g := by
  have hacc : (0 : ℂ) ∈ closure ({z | f z = g z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨heq _, ?_⟩, ?_⟩
    · simpa only [mem_singleton_iff, Complex.ofReal_eq_zero] using (by linarith : ε / 2 ≠ 0)
    · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < ε / 2)] using (by linarith : ε / 2 < ε)
  funext z
  exact (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_mem_closure
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ 0) hacc
      (mem_univ z)

/-- Successive one-variable identity theorems show that the real subspace
 determines an entire function in every finite complex dimension. -/
lemma entire_eq_of_real_restriction {d : ℕ} {F G : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (heq : ∀ ξ : Euclidean d, F (realFrequency ξ) = G (realFrequency ξ)) : F = G := by
  classical
  have h : ∀ S : Finset (Fin d), ∀ z : ComplexEuclidean d,
      (∀ j, j ∉ S → (z j).im = 0) → F z = G z := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro z hz
      let ξ : Euclidean d := WithLp.toLp 2 (fun j => (z j).re)
      have he : realFrequency ξ = z := by
        ext j
        apply Complex.ext
        · rfl
        · exact (hz j (by simp)).symm
      simpa only [he] using heq ξ
    | @insert j S hj ih =>
      intro z hz
      let L : ℂ → ComplexEuclidean d := fun w =>
        WithLp.toLp 2 (fun i => if i = j then w else z i)
      have hL : Differentiable ℂ L := by
        apply (differentiable_piLp 2).mpr
        intro i
        dsimp [L]
        split_ifs <;> fun_prop
      have hh : (fun w => F (L w)) = (fun w => G (L w)) := by
        apply entire_eq_of_eq_on_reals (hF.comp hL) (hG.comp hL)
        intro r
        apply ih
        intro i hi
        by_cases hij : i = j
        · simp [L, hij]
        · simpa [L, hij] using hz i (by simp [hi, hij])
      have hLz : L (z j) = z := by
        ext i
        simp only [L]
        split_ifs with hij
        · exact congrArg (fun k => z k) hij.symm
        · rfl
      simpa only [hLz] using congrFun hh (z j)
  funext z
  exact h Finset.univ z (by simp)

lemma inverseRealIntegral_eq_fourierInv {d : ℕ} (F : ComplexEuclidean d → ℂ) :
    inverseRealIntegral F = FourierTransform.fourierInv (fun ξ : Euclidean d =>
      F (realFrequency ξ)) := by
  funext x
  rw [Real.fourierInv_eq']
  unfold inverseRealIntegral
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [smul_eq_mul]
  congr 2
  rw [real_inner_comm ξ x]
  push_cast
  ring

lemma integralFourier_eq_fourier {d : ℕ} (f : Euclidean d → ℂ) :
    integralFourier f = FourierTransform.fourier f := by
  funext ξ
  rw [Real.fourier_eq']
  unfold integralFourier
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- Once the support assertion is proved, ordinary integrable Fourier
 inversion and the entire identity theorem give exact complex recovery. -/
lemma inverse_of_support {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    (hK : IsCompact K) {F : ComplexEuclidean d → ℂ} (hF : Differentiable ℂ F)
    (hbound : RapidExponentialType K F) (hsupp : tsupport (inverseRealIntegral F) ⊆ K) :
    SmoothSupportedIn K (inverseRealIntegral F) ∧ fourierLaplace (inverseRealIntegral F) = F := by
  have hsmooth : SmoothSupportedIn K (inverseRealIntegral F) :=
    ⟨contDiff_inverse hne hF.continuous hbound, hsupp⟩
  refine ⟨hsmooth, ?_⟩
  apply entire_eq_of_real_restriction (differentiable_fourierLaplace hK hsmooth) hF
  intro ξ
  rw [real_restriction, integralFourier_eq_fourier]
  have hc : Continuous (fun ξ : Euclidean d => F (realFrequency ξ)) :=
    hF.continuous.comp (continuous_realFrequency d)
  have hi := real_axis_integrable hne hF.continuous hbound
  have hfi : Integrable (FourierTransform.fourierInv (fun ξ : Euclidean d =>
      F (realFrequency ξ))) := by
    rw [← inverseRealIntegral_eq_fourierInv]
    exact hsmooth.1.continuous.integrable_of_hasCompactSupport (hsmooth.hasCompactSupport hK)
  have hfourier : Integrable (FourierTransform.fourier (fun ξ : Euclidean d =>
      F (realFrequency ξ))) := by
    have hneg : Integrable (fun ξ : Euclidean d =>
        FourierTransform.fourier (fun ξ : Euclidean d => F (realFrequency ξ)) (-ξ)) := by
      simpa only [← Real.fourierInv_eq_fourier_neg] using hfi
    exact ((LinearIsometryEquiv.neg ℝ (E := Euclidean d)).measurePreserving.integrable_comp_emb
      (LinearIsometryEquiv.neg ℝ (E := Euclidean d)).toHomeomorph.measurableEmbedding).mp hneg
  rw [inverseRealIntegral_eq_fourierInv, hc.fourier_fourierInv_eq hi hfourier]

/-- Translation of a real frequency in a purely imaginary direction. -/
def shiftedFrequency {d : ℕ} (ξ η : Euclidean d) : ComplexEuclidean d :=
  realFrequency ξ + Complex.I • realFrequency η

@[simp] lemma imaginaryPart_shiftedFrequency {d : ℕ} (ξ η : Euclidean d) :
    imaginaryPart (shiftedFrequency ξ η) = η := by
  ext j
  simp [shiftedFrequency, realFrequency, imaginaryPart, Complex.mul_im]

lemma norm_shiftedFrequency_sq {d : ℕ} (ξ η : Euclidean d) :
    ‖shiftedFrequency ξ η‖ ^ 2 = ‖ξ‖ ^ 2 + ‖η‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, shiftedFrequency, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, realFrequency,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  simp only [zero_mul, zero_add, one_mul, mul_zero, sub_zero, add_zero, ← pow_two,
    Real.norm_eq_abs, sq_abs, Finset.sum_add_distrib]
  simp

lemma norm_le_shiftedFrequency {d : ℕ} (ξ η : Euclidean d) :
    ‖ξ‖ ≤ ‖shiftedFrequency ξ η‖ := by
  nlinarith [norm_shiftedFrequency_sq ξ η, norm_nonneg ξ,
    norm_nonneg (shiftedFrequency ξ η), sq_nonneg ‖η‖]

@[fun_prop] lemma continuous_shiftedFrequency {d : ℕ} (η : Euclidean d) :
    Continuous (fun ξ => shiftedFrequency ξ η) := by
  unfold shiftedFrequency
  fun_prop

noncomputable def shiftedInverseIntegral {d : ℕ} (F : ComplexEuclidean d → ℂ)
    (η x : Euclidean d) : ℂ :=
  ∫ ξ : Euclidean d, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    complexPairing x (shiftedFrequency ξ η)) * F (shiftedFrequency ξ η)

lemma shifted_inverse_kernel_norm {d : ℕ} (x ξ η : Euclidean d) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      complexPairing x (shiftedFrequency ξ η))‖ =
      Real.exp (-(2 * Real.pi * inner ℝ x η)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, complexPairing_im]

/-- The rapid bound controls every shifted inverse integrand by a fixed
 integrable power on the real axes. -/
lemma shifted_integrand_bound {d : ℕ} {K : Set (Euclidean d)}
    {F : ComplexEuclidean d → ℂ} (hF : RapidExponentialType K F) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x ξ η : Euclidean d),
      ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          complexPairing x (shiftedFrequency ξ η)) * F (shiftedFrequency ξ η)‖ ≤
        C * (1 + ‖ξ‖) ^ (-(N : ℤ)) *
          Real.exp (2 * Real.pi * (supportFunction K η - inner ℝ x η)) := by
  obtain ⟨C, hC, hb⟩ := hF N
  refine ⟨C, hC, fun x ξ η => ?_⟩
  have hp : (1 + ‖shiftedFrequency ξ η‖) ^ (-(N : ℤ)) ≤
      (1 + ‖ξ‖) ^ (-(N : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
    gcongr
    exact norm_le_shiftedFrequency ξ η
  have hval : ‖F (shiftedFrequency ξ η)‖ ≤
      C * (1 + ‖ξ‖) ^ (-(N : ℤ)) * Real.exp (2 * Real.pi * supportFunction K η) := by
    apply (hb (shiftedFrequency ξ η)).trans
    rw [imaginaryPart_shiftedFrequency]
    gcongr
  rw [norm_mul, shifted_inverse_kernel_norm]
  calc
    _ ≤ Real.exp (-(2 * Real.pi * inner ℝ x η)) *
        (C * (1 + ‖ξ‖) ^ (-(N : ℤ)) * Real.exp (2 * Real.pi * supportFunction K η)) :=
      mul_le_mul_of_nonneg_left hval (Real.exp_nonneg _)
    _ = _ := by
      rw [show 2 * Real.pi * (supportFunction K η - inner ℝ x η) =
        -(2 * Real.pi * inner ℝ x η) + 2 * Real.pi * supportFunction K η by ring,
        Real.exp_add]
      ring

lemma shifted_inverse_estimate {d : ℕ} {K : Set (Euclidean d)}
    {F : ComplexEuclidean d → ℂ} (hcont : Continuous F) (hF : RapidExponentialType K F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x η : Euclidean d),
      ‖shiftedInverseIntegral F η x‖ ≤
        C * Real.exp (2 * Real.pi * (supportFunction K η - inner ℝ x η)) := by
  let N := Module.finrank ℝ (Euclidean d) + 1
  let g : Euclidean d → ℝ := fun ξ => (1 + ‖ξ‖) ^ (-(N : ℤ))
  have hi : Integrable g := by
    dsimp [g]
    simp_rw [← Real.rpow_neg_natCast]
    apply integrable_one_add_norm
    dsimp [N]
    norm_num
  obtain ⟨C, hC, hb⟩ := shifted_integrand_bound hF N
  refine ⟨C * ∫ ξ, g ξ, mul_nonneg hC (integral_nonneg (fun _ => by dsimp [g]; positivity)), ?_⟩
  intro x η
  let E := Real.exp (2 * Real.pi * (supportFunction K η - inner ℝ x η))
  have hci : Continuous (fun ξ : Euclidean d => Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * complexPairing x (shiftedFrequency ξ η)) *
        F (shiftedFrequency ξ η)) := by
    unfold complexPairing
    have hfc := hcont.comp (continuous_shiftedFrequency η)
    unfold shiftedFrequency realFrequency
    fun_prop
  have hdom : Integrable (fun ξ => C * g ξ * E) := (hi.const_mul C).mul_const E
  have hint : Integrable (fun ξ : Euclidean d => Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * complexPairing x (shiftedFrequency ξ η)) *
        F (shiftedFrequency ξ η)) :=
    hdom.mono' hci.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => hb x ξ η))
  calc
    ‖shiftedInverseIntegral F η x‖ ≤ ∫ ξ : Euclidean d, ‖Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * complexPairing x (shiftedFrequency ξ η)) *
          F (shiftedFrequency ξ η)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, C * g ξ * E := integral_mono hint.norm hdom (fun ξ => hb x ξ η)
    _ = _ := by rw [integral_mul_const, integral_const_mul]

/-- All support and inverse-recovery obligations reduce to proving the
 genuine contour-shift equality; that equality is not assumed globally. -/
lemma inverse_of_contour_shift {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) {F : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (hb : RapidExponentialType K F)
    (hshift : ∀ x η : Euclidean d,
      inverseRealIntegral F x = shiftedInverseIntegral F η x) :
    SmoothSupportedIn K (inverseRealIntegral F) ∧ fourierLaplace (inverseRealIntegral F) = F := by
  apply inverse_of_support hne hK hF hb
  apply support_subset_of_shifted_bound hne hK hconv
  obtain ⟨C, _hC, hC⟩ := shifted_inverse_estimate hF.continuous hb
  intro x η
  refine ⟨C, fun t ht => ?_⟩
  rw [hshift x (t • η)]
  convert hC x (t • η) using 1
  rw [supportFunction_smul_nonneg hne hK η ht, inner_smul_right]
  congr 2
  ring

/-- Holomorphic dependence of an integral under local integrable domination.
 Using primitives avoids any assumed bounds on derivatives of the integrand. -/
lemma differentiable_integral_of_locally_dominated {d : ℕ}
    {g : ℂ → Euclidean d → ℂ}
    (hc : Continuous (fun p : ℂ × Euclidean d => g p.1 p.2))
    (hd : ∀ ξ, Differentiable ℂ (fun w => g w ξ))
    (hb : ∀ L : Set ℂ, IsCompact L → ∃ b : Euclidean d → ℝ, Integrable b ∧
      ∀ ξ w, w ∈ L → ‖g w ξ‖ ≤ b ξ) :
    Differentiable ℂ (fun w => ∫ ξ, g w ξ) := by
  let H : ℂ → Euclidean d → ℂ := fun w ξ =>
    Complex.wedgeIntegral 0 w (fun z => g z ξ)
  have hH (ξ : Euclidean d) (w : ℂ) : HasDerivAt (fun z => H z ξ) (g w ξ) w := by
    apply Complex.IsConservativeOn.hasDerivAt_wedgeIntegral
      (c := 0) (r := ‖w‖ + 1)
      ((hd ξ).continuous.continuousOn) (by simp [Metric.mem_ball, dist_zero_right])
    exact (hd ξ).differentiableOn.isConservativeOn
  have hHm (w : ℂ) : AEStronglyMeasurable (H w) := by
    have hm (c : ℝ → ℂ) (hcm : Continuous c) (a b : ℝ) :
        StronglyMeasurable (fun ξ : Euclidean d => ∫ t in a..b, g (c t) ξ) := by
      have hh : Continuous (fun p : Euclidean d × ℝ => g (c p.2) p.1) :=
        hc.comp ((hcm.comp continuous_snd).prodMk continuous_fst)
      unfold intervalIntegral
      exact hh.stronglyMeasurable.integral_prod_right'.sub
        hh.stronglyMeasurable.integral_prod_right'
    dsimp [H, Complex.wedgeIntegral]
    exact ((hm (fun t => (t : ℂ) + (0 : ℂ).im * Complex.I) (by fun_prop) _ _).add
      ((hm (fun t => w.re + (t : ℂ) * Complex.I) (by fun_prop) _ _).const_smul
        Complex.I)).aestronglyMeasurable
  have hHi (w : ℂ) : Integrable (H w) := by
    obtain ⟨b, hbi, hbb⟩ := hb (Metric.closedBall 0 (‖w‖ + 1)) (isCompact_closedBall _ _)
    apply (hbi.mul_const ‖w‖).mono' (hHm w)
    filter_upwards [] with ξ
    have hh := (convex_ball (0 : ℂ) (‖w‖ + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hH ξ z).hasDerivWithinAt)
      (fun z hz => hbb ξ z (Metric.ball_subset_closedBall hz))
      (show (0 : ℂ) ∈ Metric.ball 0 (‖w‖ + 1) by
        simpa only [Metric.mem_ball, dist_self] using (by positivity : 0 < ‖w‖ + 1))
      (show w ∈ Metric.ball 0 (‖w‖ + 1) by simp [Metric.mem_ball, dist_zero_right])
    simpa [H, Complex.wedgeIntegral] using hh
  have hJ (w : ℂ) : HasDerivAt (fun z => ∫ ξ, H z ξ) (∫ ξ, g w ξ) w := by
    obtain ⟨b, hbi, hbb⟩ := hb (Metric.closedBall w 1) (isCompact_closedBall _ _)
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := H) (F' := g) (bound := b) (s := Metric.ball w 1)
      (Metric.ball_mem_nhds w zero_lt_one)
      (Filter.Eventually.of_forall hHm) (hHi w)
      ((hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ξ z hz => hbb ξ z (Metric.ball_subset_closedBall hz)))
      hbi (Filter.Eventually.of_forall (fun ξ z _ => hH ξ z))).2
  have hJd : Differentiable ℂ (fun z => ∫ ξ, H z ξ) := fun z => (hJ z).differentiableAt
  have heq : deriv (fun z => ∫ ξ, H z ξ) = (fun z => ∫ ξ, g z ξ) :=
    funext (fun z => (hJ z).deriv)
  rw [← heq]
  exact hJd.deriv

lemma contour_shift_of_domination {d : ℕ} {F : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (x η : Euclidean d)
    (hb : ∀ L : Set ℂ, IsCompact L → ∃ b : Euclidean d → ℝ, Integrable b ∧
      ∀ ξ w, w ∈ L → ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        complexPairing x (realFrequency ξ + w • realFrequency η)) *
          F (realFrequency ξ + w • realFrequency η)‖ ≤ b ξ) :
    inverseRealIntegral F x = shiftedInverseIntegral F η x := by
  let g : ℂ → Euclidean d → ℂ := fun w ξ =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      complexPairing x (realFrequency ξ + w • realFrequency η)) *
        F (realFrequency ξ + w • realFrequency η)
  have hc : Continuous (fun p : ℂ × Euclidean d => g p.1 p.2) := by
    have hz : Continuous (fun p : ℂ × Euclidean d =>
        realFrequency p.2 + p.1 • realFrequency η) := by fun_prop
    have hfc := hF.continuous.comp hz
    dsimp [g]
    have he (z : ComplexEuclidean d) :
        2 * (Real.pi : ℂ) * Complex.I * complexPairing x z = -laplaceExponentCLM x z := by
      rw [laplaceExponentCLM_apply]
      ring
    simp_rw [he]
    exact (((laplaceExponentCLM x).continuous.comp hz).neg.cexp).mul hfc
  have hd : ∀ ξ, Differentiable ℂ (fun w => g w ξ) := by
    intro ξ
    have hz : Differentiable ℂ (fun w : ℂ =>
        realFrequency ξ + w • realFrequency η) := by fun_prop
    have hfd := hF.comp hz
    dsimp [g]
    unfold complexPairing
    fun_prop
  have hJ : Differentiable ℂ (fun w => ∫ ξ, g w ξ) :=
    differentiable_integral_of_locally_dominated hc hd hb
  have hr (r : ℝ) : (∫ ξ, g (r : ℂ) ξ) = inverseRealIntegral F x := by
    unfold inverseRealIntegral
    rw [← integral_add_right_eq_self (fun ξ : Euclidean d =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
        F (realFrequency ξ)) (r • η)]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have hz : realFrequency (ξ + r • η) = realFrequency ξ + (r : ℂ) • realFrequency η := by
      ext j
      simp [realFrequency]
    simp only [g, ← hz, complexPairing_realFrequency]
  have heq := entire_eq_of_eq_on_reals hJ (differentiable_const (c := inverseRealIntegral F x)) hr
  have hi := congrFun heq Complex.I
  exact hi.symm


lemma complex_frequency_decomposition {d : ℕ} (ξ η : Euclidean d) (w : ℂ) :
    realFrequency ξ + w • realFrequency η =
      shiftedFrequency (ξ + w.re • η) (w.im • η) := by
  ext j
  apply Complex.ext <;>
    simp [shiftedFrequency, realFrequency, PiLp.add_apply, PiLp.smul_apply,
      Complex.mul_re, Complex.mul_im]

lemma rapid_integrand_compact_domination {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) {F : ComplexEuclidean d → ℂ}
    (hF : RapidExponentialType K F) (x η : Euclidean d)
    (L : Set ℂ) (hL : IsCompact L) :
    ∃ b : Euclidean d → ℝ, Integrable b ∧ ∀ ξ w, w ∈ L →
      ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * complexPairing x
          (realFrequency ξ + w • realFrequency η)) *
        F (realFrequency ξ + w • realFrequency η)‖ ≤ b ξ := by
  obtain ⟨M, hM, hMK⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨R, hR, hRL⟩ := hL.isBounded.exists_pos_norm_le
  let N := Module.finrank ℝ (Euclidean d) + 1
  let D : ℝ := (1 + R * ‖η‖) ^ N
  let E : ℝ := Real.exp (2 * Real.pi * ((M + ‖x‖) * R * ‖η‖))
  obtain ⟨C, hC, hb⟩ := shifted_integrand_bound hF N
  have hi : Integrable (fun ξ : Euclidean d => (1 + ‖ξ‖) ^ (-(N : ℤ))) := by
    simp_rw [← Real.rpow_neg_natCast]
    apply integrable_one_add_norm
    dsimp [N]
    norm_num
  refine ⟨fun ξ => C * D * E * (1 + ‖ξ‖) ^ (-(N : ℤ)),
    hi.const_mul (C * D * E), ?_⟩
  intro ξ w hw
  rw [complex_frequency_decomposition]
  have hnRe : ‖w.re • η‖ ≤ R * ‖η‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm w).trans (hRL w hw))
      (norm_nonneg η)
  have hnIm : ‖w.im • η‖ ≤ R * ‖η‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm w).trans (hRL w hw))
      (norm_nonneg η)
  have hnorm : ‖ξ‖ ≤ ‖ξ + w.re • η‖ + R * ‖η‖ := by
    calc
      ‖ξ‖ = ‖ξ + w.re • η - w.re • η‖ := by congr 1; abel
      _ ≤ ‖ξ + w.re • η‖ + ‖w.re • η‖ := norm_sub_le _ _
      _ ≤ _ := by gcongr
  have hbase : 1 + ‖ξ‖ ≤ (1 + R * ‖η‖) * (1 + ‖ξ + w.re • η‖) := by
    nlinarith [mul_nonneg (mul_nonneg hR.le (norm_nonneg η))
      (norm_nonneg (ξ + w.re • η))]
  have hp : (1 + ‖ξ + w.re • η‖) ^ (-(N : ℤ)) ≤
      D * (1 + ‖ξ‖) ^ (-(N : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
    rw [le_mul_inv_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    simpa [D, mul_pow, mul_comm] using pow_le_pow_left₀ (by positivity) hbase N
  have hsupp : supportFunction K (w.im • η) ≤ M * ‖w.im • η‖ := by
    apply csSup_le (hne.image _)
    rintro _ ⟨y, hy, rfl⟩
    exact (real_inner_le_norm y (w.im • η)).trans
      (mul_le_mul_of_nonneg_right (hMK y hy) (norm_nonneg _))
  have hexp : Real.exp (2 * Real.pi * (supportFunction K (w.im • η) -
      inner ℝ x (w.im • η))) ≤ E := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      supportFunction K (w.im • η) - inner ℝ x (w.im • η) ≤
          M * ‖w.im • η‖ + ‖x‖ * ‖w.im • η‖ := by
        have hh := (neg_le_abs (inner ℝ x (w.im • η))).trans
          (abs_real_inner_le_norm x (w.im • η))
        linarith
      _ = (M + ‖x‖) * ‖w.im • η‖ := by ring
      _ ≤ (M + ‖x‖) * (R * ‖η‖) :=
        mul_le_mul_of_nonneg_left hnIm (by positivity)
      _ = _ := by ring
  calc
    _ ≤ C * (1 + ‖ξ + w.re • η‖) ^ (-(N : ℤ)) *
        Real.exp (2 * Real.pi * (supportFunction K (w.im • η) -
          inner ℝ x (w.im • η))) := hb x (ξ + w.re • η) (w.im • η)
    _ ≤ C * (D * (1 + ‖ξ‖) ^ (-(N : ℤ))) * E := by
      gcongr
    _ = _ := by ring


/-- The rapid bounds justify the contour shift in every real direction.
Holomorphic dependence on the translation parameter and real translation
invariance give the equality without a boundary integral limit. -/
lemma contour_shift {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    (hK : IsCompact K) {F : ComplexEuclidean d → ℂ} (hF : Differentiable ℂ F)
    (hb : RapidExponentialType K F) (x η : Euclidean d) :
    inverseRealIntegral F x = shiftedInverseIntegral F η x :=
  contour_shift_of_domination hF x η
    (rapid_integrand_compact_domination hne hK hb x η)

/-- The actual inverse Fourier integral has support in K and recovers the
entire function at every complex frequency. -/
theorem inverse : Specs.ExpandedFA.Fourier.SmoothPaleyWiener.inverseType := by
  intro d K hne hK hconv F hF hb
  exact inverse_of_contour_shift hne hK hconv hF hb
    (contour_shift hne hK hF hb)

/-- The smooth Paley–Wiener characterization, including compact convex sets
with empty interior and Euclidean dimension zero. -/
theorem characterization :
    Specs.ExpandedFA.Fourier.SmoothPaleyWiener.characterizationType := by
  intro d K hne hK hconv F
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact forward d K hne hK hconv f hf
  · rintro ⟨hF, hb⟩
    obtain ⟨hsmooth, heq⟩ := inverse d K hne hK hconv F hF hb
    exact ⟨inverseRealIntegral F, hsmooth, heq⟩

end ExpandedFA.Fourier.PaleyWiener
