import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.HeatLpMaximalDomain
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.MeasureTheory.Integral.Pi
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Basic.Real.ConjExponents
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The Gaussian heat semigroup and its exact maximal distributional domain,
`fa2:p3:heat-poisson`. Gaussian normalization, convolution, and translation
continuity construct the contraction C0 semigroup. Differentiation in L1 and
integration by parts identify its generator in distributions. A Schwartz cutoff
argument and Fourier elliptic uniqueness, combined with the Laplace resolvent,
prove the converse inclusion, including p = 1 and dimension zero. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExpandedFA.Models.HeatLp

/-- Tensor factor for the Gaussian kernel. -/
def gaussianFactor (t x : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-1 / 2 : ℝ) * Real.exp (-(4 * t)⁻¹ * x ^ 2)

lemma gaussianFactor_integrable {t : ℝ} (ht : 0 < t) : Integrable (gaussianFactor t) :=
  (integrable_exp_neg_mul_sq (inv_pos.mpr (mul_pos (by norm_num) ht))).const_mul _

lemma gaussianFactor_integral {t : ℝ} (ht : 0 < t) : ∫ x, gaussianFactor t x = 1 := by
  have ha : 0 < 4 * Real.pi * t := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  simp only [gaussianFactor, integral_const_mul, integral_gaussian]
  have harg : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by
    simp only [div_inv_eq_mul]; ring
  rw [harg, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne'

lemma gaussian_eq_prod {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) :
    gaussian t x = ∏ i, gaussianFactor t (x i) := by
  have ha : 0 < 4 * Real.pi * t := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hs : -(∑ i, (x i) ^ 2) / (4 * t) = ∑ i, -(4 * t)⁻¹ * (x i) ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  simp only [gaussian, gaussianFactor, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, hs]
  rw [← Real.rpow_mul_natCast ha.le]
  congr 2
  ring

/-- This includes the empty tensor product, hence dimension zero. -/
theorem gaussian_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (gaussian (d := d) t) := by
  have heq : gaussian (d := d) t = fun x => ∏ i, gaussianFactor t (x i) :=
    funext (gaussian_eq_prod ht)
  rw [heq]
  exact Integrable.fintype_prod (fun _ : Fin d => gaussianFactor_integrable ht)

theorem gaussian_mass_one {d : ℕ} {t : ℝ} (ht : 0 < t) :
    ∫ x : Space d, gaussian t x = 1 := by
  simp_rw [gaussian_eq_prod ht]
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [gaussianFactor_integral ht, Finset.prod_const_one]

theorem gaussian_nonneg {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) :
    0 ≤ gaussian t x := by
  apply le_of_lt
  exact mul_pos (Real.rpow_pos_of_pos
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) ht) _) (Real.exp_pos _)

/-- Completion of the square in one dimension, with the normalization
constants included. This is the kernel semigroup law before integration. -/
lemma gaussianFactor_completion {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x y : ℝ) :
    gaussianFactor t y * gaussianFactor s (x-y) =
      gaussianFactor (t+s) x *
        gaussianFactor (t*s/(t+s)) (y - t/(t+s)*x) := by
  have hts : 0 < t+s := add_pos ht hs
  have hv : 0 < t*s/(t+s) := div_pos (mul_pos ht hs) hts
  have hN : (4*Real.pi*t)^(-1/2 : ℝ) * (4*Real.pi*s)^(-1/2 : ℝ) =
      (4*Real.pi*(t+s))^(-1/2 : ℝ) * (4*Real.pi*(t*s/(t+s)))^(-1/2 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
    <;> ring
  have hE : -(4*t)⁻¹*y^2 + -(4*s)⁻¹*(x-y)^2 =
      -(4*(t+s))⁻¹*x^2 + -(4*(t*s/(t+s)))⁻¹*(y-t/(t+s)*x)^2 := by
    field_simp
    <;> ring
  unfold gaussianFactor
  calc
    _ = ((4*Real.pi*t)^(-1/2 : ℝ) * (4*Real.pi*s)^(-1/2 : ℝ)) *
        Real.exp (-(4*t)⁻¹*y^2 + -(4*s)⁻¹*(x-y)^2) := by rw [Real.exp_add]; ring
    _ = _ := by rw [hN, hE, Real.exp_add]; ring

lemma gaussian_completion {d : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x y : Space d) :
    gaussian t y * gaussian s (x-y) =
      gaussian (t+s) x * gaussian (t*s/(t+s)) (y - (t/(t+s)) • x) := by
  have hts : 0 < t+s := add_pos ht hs
  have hv : 0 < t*s/(t+s) := div_pos (mul_pos ht hs) hts
  simp_rw [gaussian_eq_prod ht, gaussian_eq_prod hs, gaussian_eq_prod hts,
    gaussian_eq_prod hv]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    gaussianFactor_completion ht hs (x i) (y i)

lemma gaussian_convolution_integrable {d : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x : Space d) : Integrable (fun y : Space d => gaussian t y * gaussian s (x-y)) := by
  simp_rw [gaussian_completion ht hs]
  exact ((gaussian_integrable (div_pos (mul_pos ht hs) (add_pos ht hs))).comp_sub_right
    ((t/(t+s)) • x)).const_mul _

/-- The normalized Gaussian kernels obey the convolution law pointwise. -/
theorem gaussian_convolution {d : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x : Space d) :
    (∫ y : Space d, gaussian t y * gaussian s (x-y)) = gaussian (t+s) x := by
  simp_rw [gaussian_completion ht hs]
  rw [integral_const_mul, integral_sub_right_eq_self,
    gaussian_mass_one (div_pos (mul_pos ht hs) (add_pos ht hs)), mul_one]

/-- A real Gaussian as a scalar-valued L¹ kernel has norm exactly one. -/
lemma gaussian_scalar_memLp_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : Space d => (gaussian t x : 𝕜)) 1 volume ∧
      eLpNorm (fun x : Space d => (gaussian t x : 𝕜)) 1 volume = 1 := by
  have hi : Integrable (fun x : Space d => (gaussian t x : 𝕜)) :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integrable_comp (gaussian_integrable ht)
  refine ⟨memLp_one_iff_integrable.mpr hi, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable]
  simp_rw [← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg (gaussian_nonneg ht _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_integrable ht)
    (Filter.Eventually.of_forall (gaussian_nonneg ht)), gaussian_mass_one ht]
  simp

/-- Young's endpoint estimate applies to the actual Gaussian, without a
compact-support hypothesis and including p = 1. -/
theorem heatConvolution_memLp_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => gaussian t y • f (x - y))) ∧
    MemLp (heatConvolution t f) p volume ∧
    eLpNorm (heatConvolution t f) p volume ≤ eLpNorm f p volume := by
  obtain ⟨hk, hknorm⟩ := gaussian_scalar_memLp_norm (𝕜 := 𝕜) (d := d) ht
  obtain ⟨hi, _, hm, hb⟩ := Distributions.young_l1_lp_endpoint p hp
    (fun x => (gaussian t x : 𝕜)) f hk hf
  have heq : Distributions.ConvolutionEndpointBoundsSpec.ConvolutionValue
      (fun x => (gaussian t x : 𝕜)) f = heatConvolution t f := by
    funext x
    simp only [Distributions.ConvolutionEndpointBoundsSpec.ConvolutionValue,
      heatConvolution, RCLike.real_smul_eq_coe_mul]
  rw [heq, hknorm, one_mul] at hb
  rw [heq] at hm
  refine ⟨?_, hm, hb⟩
  simpa only [RCLike.real_smul_eq_coe_mul] using hi

theorem gaussian_properties : Spec.GaussianProperties := by
  intro d t ht
  exact ⟨gaussian_integrable ht, gaussian_mass_one ht, gaussian_nonneg ht⟩

theorem heat_convolution_bounds : Spec.HeatConvolutionBound := by
  intro 𝕜 _ d p hp t ht f hf
  exact heatConvolution_memLp_bound p hp ht f hf

/-- Continuity is in the coordinate topology; no Euclidean norm is
silently substituted for the norm on the product space. -/
lemma gaussian_continuous {d : ℕ} (t : ℝ) : Continuous (gaussian (d := d) t) := by
  unfold gaussian
  fun_prop

/-- The heat kernel is the dilation of the fixed time-one probability density. -/
lemma gaussian_dilation {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Space d) :
    gaussian (s ^ 2) (s • x) = (s ^ d)⁻¹ * gaussian 1 x := by
  have ha : 0 < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpow : (s ^ 2) ^ (-(d : ℝ) / 2) = (s ^ d)⁻¹ := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by ring,
      Real.rpow_neg hs.le, Real.rpow_natCast]
  have hsum : (∑ i : Fin d, ((s • x) i) ^ 2) = s ^ 2 * ∑ i, (x i) ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  unfold gaussian
  rw [show 4 * Real.pi * s ^ 2 = (4 * Real.pi) * (s ^ 2) by ring,
    Real.mul_rpow ha.le (sq_nonneg _), hpow, hsum]
  have hexp : -(s ^ 2 * ∑ i, (x i) ^ 2) / (4 * s ^ 2) =
      -(∑ i, (x i) ^ 2) / (4 * 1) := by
    field_simp
  rw [hexp]
  simp only [mul_one]
  ring

/-- Change of variables is valid for arbitrary representatives; both sides
use the Bochner integral's usual zero convention outside integrability. -/
lemma heatConvolution_dilation {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {s : ℝ} (hs : 0 < s) (f : Space d → 𝕜) (x : Space d) :
    heatConvolution (s ^ 2) f x = ∫ y, gaussian 1 y • f (x - s • y) := by
  have he := Measure.integral_comp_smul_of_nonneg volume
    (fun y : Space d => gaussian (s ^ 2) y • f (x-y)) s (hR := hs.le)
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  simp_rw [gaussian_dilation hs, mul_smul, integral_smul] at he
  apply (smul_right_injective _ (inv_ne_zero (pow_ne_zero _ hs.ne')))
  exact he.symm

section HeatOperators
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive-time convolution as an actual Lp class. -/
def heatLpValue (t : ℝ) (ht : 0 < t) (f : ScalarLp 𝕜 d p) : ScalarLp 𝕜 d p :=
  ((heatConvolution_memLp_bound p Fact.out ht f (Lp.memLp f)).2.1).toLp
    (heatConvolution t f)

lemma heatLpValue_representative (t : ℝ) (ht : 0 < t) (f : ScalarLp 𝕜 d p) :
    heatLpValue t ht f =ᵐ[volume] heatConvolution t f :=
  MemLp.coeFn_toLp _

lemma heatConvolution_congr {t : ℝ} {f g : Space d → 𝕜} (h : f =ᵐ[volume] g) :
    heatConvolution t f = heatConvolution t g := by
  funext x
  apply integral_congr_ae
  filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae h]
    with y hy
  rw [hy]

lemma heatLpValue_norm_le (t : ℝ) (ht : 0 < t) (f : ScalarLp 𝕜 d p) :
    ‖heatLpValue t ht f‖ ≤ ‖f‖ := by
  rw [heatLpValue, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne
    (heatConvolution_memLp_bound p Fact.out ht f (Lp.memLp f)).2.2

lemma heatLpValue_add (t : ℝ) (ht : 0 < t) (f g : ScalarLp 𝕜 d p) :
    heatLpValue t ht (f + g) = heatLpValue t ht f + heatLpValue t ht g := by
  apply Lp.ext
  have hrep := heatConvolution_congr (t := t) (Lp.coeFn_add f g)
  filter_upwards [heatLpValue_representative t ht (f + g),
    heatLpValue_representative t ht f, heatLpValue_representative t ht g,
    Lp.coeFn_add (heatLpValue t ht f) (heatLpValue t ht g),
    (heatConvolution_memLp_bound p Fact.out ht f (Lp.memLp f)).1,
    (heatConvolution_memLp_bound p Fact.out ht g (Lp.memLp g)).1]
    with x hfg hf hg hadd hfi hgi
  rw [hfg, hadd, Pi.add_apply, hf, hg, hrep]
  change (∫ y, gaussian t y • (f (x-y) + g (x-y))) = _
  simp_rw [smul_add]
  exact integral_add hfi hgi

lemma heatLpValue_smul (t : ℝ) (ht : 0 < t) (c : 𝕜) (f : ScalarLp 𝕜 d p) :
    heatLpValue t ht (c • f) = c • heatLpValue t ht f := by
  apply Lp.ext
  have hrep := heatConvolution_congr (t := t) (Lp.coeFn_smul c f)
  filter_upwards [heatLpValue_representative t ht (c • f),
    heatLpValue_representative t ht f, Lp.coeFn_smul c (heatLpValue t ht f)]
    with x hcf hf hsmul
  rw [hcf, hsmul, Pi.smul_apply, hf, hrep]
  change (∫ y, gaussian t y • (c • f (x-y))) = c • ∫ y, gaussian t y • f (x-y)
  simp_rw [smul_comm (gaussian t _) c]
  exact integral_smul c _

/-- The positive heat operators are bounded scalar-linear contractions on
all Lp spaces, including p = infinity. No continuity in time is asserted here. -/
def heatOperatorPositive (t : ℝ) (ht : 0 < t) :
    ScalarLp 𝕜 d p →L[𝕜] ScalarLp 𝕜 d p :=
  LinearMap.mkContinuous
    { toFun := heatLpValue t ht
      map_add' := heatLpValue_add t ht
      map_smul' := heatLpValue_smul t ht }
    1 (fun f => by
      change ‖heatLpValue t ht f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using heatLpValue_norm_le t ht f)

lemma heatOperatorPositive_norm_le (t : ℝ) (ht : 0 < t) :
    ‖heatOperatorPositive (𝕜 := 𝕜) (d := d) (p := p) t ht‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by
      change ‖heatLpValue t ht f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using heatLpValue_norm_le t ht f)

end HeatOperators

section StrongContinuity
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Express translation errors using the continuous Lp translation orbit. -/
lemma translationError_eq (f : Space d → 𝕜) (hf : MemLp f p volume) (y : Space d) :
    eLpNorm (fun x => f (x-y) - f x) p volume =
      ENNReal.ofReal ‖Distributions.LpTranslationContinuitySpec.LpTranslationValue
        p y (hf.toLp f) - hf.toLp f‖ := by
  rw [ofReal_norm, Lp.enorm_def]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub
      (Distributions.LpTranslationContinuitySpec.LpTranslationValue p y (hf.toLp f))
      (hf.toLp f),
    Distributions.lpTranslation_representative p y (hf.toLp f),
    (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae hf.coeFn_toLp,
    hf.coeFn_toLp] with x hsub ht hs hv
  simp only [Pi.sub_apply] at hsub
  rw [hsub, ht, hs, hv]

lemma translationError_continuous (hp : p ≠ ∞)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    Continuous (fun y => eLpNorm (fun x => f (x-y) - f x) p volume) := by
  simp_rw [translationError_eq f hf]
  exact ENNReal.continuous_ofReal.comp
    ((Distributions.lpTranslation_continuous p hp (hf.toLp f)).sub continuous_const).norm

lemma translationError_le (f : Space d → 𝕜) (hf : MemLp f p volume) (y : Space d) :
    eLpNorm (fun x => f (x-y) - f x) p volume ≤
      eLpNorm f p volume + eLpNorm f p volume := by
  calc
    _ ≤ eLpNorm (fun x => f (x-y)) p volume + eLpNorm f p volume :=
      eLpNorm_sub_le Fact.out
    _ = _ := congrArg (· + eLpNorm f p volume)
      (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        (measurePreserving_sub_right volume y))

/-- Minkowski controls the error by a Gaussian-weighted translation error.
The integral is over the fixed time-one density, which makes domination
independent of the dilation parameter. -/
lemma gaussian_dilation_error_bound [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (hp : p ≠ ∞) (f : Space d → 𝕜) (hf : MemLp f p volume) (hfm : Measurable f)
    (s : ℝ) :
    eLpNorm ((fun x => ∫ y : Space d, gaussian 1 y • f (x-s • y)) - f) p volume ≤
      ∫⁻ y : Space d, ‖gaussian 1 y‖ₑ *
        eLpNorm (fun x => f (x-s • y) - f x) p volume := by
  let F : Space d × Space d → 𝕜 := fun z =>
    gaussian 1 z.2 • (f (z.1-s • z.2) - f z.1)
  have hF : Measurable F := ((gaussian_continuous 1).measurable.comp measurable_snd).smul
    ((hfm.comp (measurable_fst.sub (measurable_snd.const_smul s))).sub
      (hfm.comp measurable_fst))
  have hmass : (∫⁻ y : Space d, ‖gaussian 1 y‖ₑ) = 1 := by
    simp_rw [← ofReal_norm, Real.norm_of_nonneg (gaussian_nonneg zero_lt_one _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_integrable zero_lt_one)
      (Eventually.of_forall (gaussian_nonneg zero_lt_one)), gaussian_mass_one zero_lt_one]
    simp
  have hs (y : Space d) : eLpNorm (fun x => F (x,y)) p volume =
      ‖gaussian 1 y‖ₑ * eLpNorm (fun x => f (x-s • y) - f x) p volume := by
    change eLpNorm ((gaussian 1 y) • (fun x => f (x-s • y) - f x)) p volume = _
    exact eLpNorm_const_smul _ _ _ _
  have hbound : (∫⁻ y : Space d, eLpNorm (fun x => F (x,y)) p volume) ≤
      eLpNorm f p volume + eLpNorm f p volume := by
    simp_rw [hs]
    calc
      _ ≤ ∫⁻ y : Space d, ‖gaussian 1 y‖ₑ *
          (eLpNorm f p volume + eLpNorm f p volume) :=
        lintegral_mono fun y => by
          gcongr
          exact translationError_le f hf _
      _ = _ := by rw [lintegral_mul_const _ (gaussian_continuous 1).measurable.enorm,
        hmass, one_mul]
  obtain ⟨hi, hb⟩ := Distributions.minkowski_integral_eLpNorm volume volume p Fact.out hp F hF
    (hbound.trans_lt (ENNReal.add_lt_top.mpr ⟨hf.eLpNorm_lt_top, hf.eLpNorm_lt_top⟩))
  have heq : (fun x => ∫ y, F (x,y)) =ᵐ[volume]
      ((fun x => ∫ y : Space d, gaussian 1 y • f (x-s • y)) - f) := by
    filter_upwards [hi] with x hx
    have hc : Integrable (fun y : Space d => gaussian 1 y • f x) :=
      (gaussian_integrable zero_lt_one).smul_const (f x)
    have hconv : Integrable (fun y : Space d => gaussian 1 y • f (x-s • y)) := by
      convert hx.add hc using 1
      ext y
      simp [F, smul_sub]
    change (∫ y, gaussian 1 y • (f (x-s • y) - f x)) = _
    simp_rw [smul_sub]
    rw [integral_sub hconv hc, integral_smul_const, gaussian_mass_one zero_lt_one, one_smul]
    rfl
  rw [← eLpNorm_congr_ae heq]
  simpa only [hs] using hb

/-- Gaussian-weighted translation errors vanish for every finite p >= 1.
This is also valid at p = 1: no finite conjugate exponent is used. -/
lemma gaussian_translationError_tendsto (hp : p ≠ ∞)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    Tendsto (fun s : ℝ => ∫⁻ y : Space d, ‖gaussian 1 y‖ₑ *
      eLpNorm (fun x => f (x-s • y) - f x) p volume) (𝓝 0) (𝓝 0) := by
  have hc := translationError_continuous hp f hf
  have hmass : (∫⁻ y : Space d, ‖gaussian 1 y‖ₑ) = 1 := by
    simp_rw [← ofReal_norm, Real.norm_of_nonneg (gaussian_nonneg zero_lt_one _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_integrable zero_lt_one)
      (Eventually.of_forall (gaussian_nonneg zero_lt_one)), gaussian_mass_one zero_lt_one]
    simp
  have hfin : (∫⁻ y : Space d, ‖gaussian 1 y‖ₑ *
      (eLpNorm f p volume + eLpNorm f p volume)) ≠ ∞ := by
    rw [lintegral_mul_const _ (gaussian_continuous 1).measurable.enorm, hmass, one_mul]
    exact ENNReal.add_ne_top.mpr ⟨hf.ne, hf.ne⟩
  have hlim (y : Space d) : Tendsto
      (fun s : ℝ => ‖gaussian 1 y‖ₑ * eLpNorm (fun x => f (x-s • y) - f x) p volume)
      (𝓝 0) (𝓝 0) := by
    have hz : eLpNorm (fun x => f (x-(0 : Space d)) - f x) p volume = 0 := by simp
    have hscale : Tendsto (fun s : ℝ => s • y) (𝓝 0) (𝓝 (0 : Space d)) := by
      have hcscale : Continuous (fun s : ℝ => s • y) := continuous_id.smul continuous_const
      simpa only [zero_smul] using hcscale.tendsto (0 : ℝ)
    have ht := (hc.tendsto (0 : Space d)).comp hscale
    change Tendsto (fun s : ℝ => eLpNorm (fun x => f (x-s • y) - f x) p volume)
      (𝓝 0) (𝓝 (eLpNorm (fun x => f (x-(0 : Space d)) - f x) p volume)) at ht
    rw [hz] at ht
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul ht (Or.inr (by simp : ‖gaussian 1 y‖ₑ ≠ ∞))
  simpa only [lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence
      (F := fun s : ℝ => fun y : Space d => ‖gaussian 1 y‖ₑ *
        eLpNorm (fun x => f (x-s • y) - f x) p volume)
      (f := fun _ => 0)
      (fun y : Space d => ‖gaussian 1 y‖ₑ * (eLpNorm f p volume + eLpNorm f p volume))
      (Eventually.of_forall fun s : ℝ =>
        (gaussian_continuous 1).measurable.enorm.mul
          (hc.measurable.comp (measurable_id.const_smul s)))
      (Eventually.of_forall fun s : ℝ => Eventually.of_forall fun y : Space d =>
        by
          change ‖gaussian 1 y‖ₑ * eLpNorm (fun x => f (x-s • y) - f x) p volume ≤ _
          gcongr
          exact translationError_le f hf _)
      hfin (Eventually.of_forall hlim)

lemma gaussian_dilation_eLpNorm_tendsto [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (hp : p ≠ ∞) (f : Space d → 𝕜) (hf : MemLp f p volume) (hfm : Measurable f) :
    Tendsto (fun s : ℝ =>
      eLpNorm ((fun x => ∫ y : Space d, gaussian 1 y • f (x-s • y)) - f) p volume)
      (𝓝 0) (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (gaussian_translationError_tendsto hp f hf) (fun _ => bot_le)
    (gaussian_dilation_error_bound hp f hf hfm)

/-- Strong continuity of the actual Gaussian convolutions. The null-set
replacement is made before applying the measurable-product Minkowski theorem. -/
theorem heatConvolution_eLpNorm_tendsto (hp : p ≠ ∞)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    Tendsto (fun t : ℝ => eLpNorm (heatConvolution t f - f) p volume)
      (𝓝[>] 0) (𝓝 0) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht := (gaussian_dilation_eLpNorm_tendsto hp f' (hf.ae_eq hff) hfm).comp hsqrt
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have heq : heatConvolution t f = heatConvolution t f' := heatConvolution_congr hff
  have hdil : heatConvolution t f' =
      fun x => ∫ y : Space d, gaussian 1 y • f' (x - Real.sqrt t • y) := by
    simpa only [Real.sq_sqrt ht.le] using
      funext (heatConvolution_dilation (Real.sqrt_pos.mpr ht) f')
  rw [Function.comp_apply, ← hdil, ← heq]
  exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub hff.symm)

/-- Zero time is the identity operator; the Gaussian formula is used only
at positive times. -/
def heatOperators (t : ℝ≥0) : ScalarLp 𝕜 d p →L[𝕜] ScalarLp 𝕜 d p :=
  if ht : 0 < t then heatOperatorPositive t (NNReal.coe_pos.mpr ht)
  else ContinuousLinearMap.id 𝕜 _

@[simp] lemma heatOperators_zero :
    heatOperators (𝕜 := 𝕜) (d := d) (p := p) 0 = ContinuousLinearMap.id 𝕜 _ := by
  simp [heatOperators]

lemma heatOperators_representative (t : ℝ≥0) (ht : 0 < t) (f : ScalarLp 𝕜 d p) :
    heatOperators t f =ᵐ[volume] heatConvolution (t : ℝ) f := by
  simp only [heatOperators, dite_eq_left ht]
  exact heatLpValue_representative t (NNReal.coe_pos.mpr ht) f

lemma heatOperators_norm_le (t : ℝ≥0) :
    ‖heatOperators (𝕜 := 𝕜) (d := d) (p := p) t‖ ≤ 1 := by
  unfold heatOperators
  split_ifs with ht
  · exact heatOperatorPositive_norm_le _ _
  · exact ContinuousLinearMap.norm_id_le

/-- The Gaussian contraction family has strong continuity at zero for all
finite exponents, without any semigroup law being assumed. -/
theorem heatOperators_strong_zero (hp : p ≠ ∞) (f : ScalarLp 𝕜 d p) :
    Tendsto (fun h : ℝ => heatOperators h.toNNReal f) (𝓝[>] 0) (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
    (heatConvolution_eLpNorm_tendsto hp f (Lp.memLp f))
  simp only [ENNReal.toReal_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hpos : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
  have hrep := heatOperators_representative t.toNNReal hpos f
  rw [Real.coe_toNNReal t ht.le] at hrep
  have heq : (fun x => (heatOperators t.toNNReal f - f) x) =ᵐ[volume]
      heatConvolution t f - f := (Lp.coeFn_sub _ f).trans (hrep.sub (EventuallyEq.refl _ _))
  rw [Lp.norm_def, eLpNorm_congr_ae heq]
  rfl

end StrongContinuity

section SemigroupLaw
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma heatConvolution_assoc {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    heatConvolution (t+s) f =ᵐ[volume] heatConvolution t (heatConvolution s f) := by
  have hnorm : MemLp (fun x => ‖f x‖) p volume := hf.norm
  obtain ⟨hsnorm, hsnormmem, _⟩ := heatConvolution_memLp_bound p Fact.out hs _ hnorm
  obtain ⟨htsnorm, _, _⟩ := heatConvolution_memLp_bound p Fact.out ht _ hsnormmem
  have hfg : ∀ x : Space d, ConvolutionExistsAt (gaussian t) (gaussian s) x
      (ContinuousLinearMap.mul ℝ ℝ) volume := gaussian_convolution_integrable ht hs
  have hgabs (u : ℝ) (hu : 0 < u) (z : Space d) : ‖gaussian u z‖ = gaussian u z :=
    Real.norm_of_nonneg (gaussian_nonneg hu z)
  have hnormt : (fun x : Space d => ‖gaussian t x‖) = gaussian t :=
    funext fun x => Real.norm_of_nonneg (gaussian_nonneg ht x)
  have hnorms : (fun x : Space d => ‖gaussian s x‖) = gaussian s :=
    funext fun x => Real.norm_of_nonneg (gaussian_nonneg hs x)
  have hconv : MeasureTheory.convolution (gaussian (d := d) t) (gaussian s)
      (ContinuousLinearMap.mul ℝ ℝ) volume = gaussian (t+s) :=
    funext (gaussian_convolution ht hs)
  have hreal (g : Space d → ℝ) (u : ℝ) : MeasureTheory.convolution (gaussian u) g
      (ContinuousLinearMap.mul ℝ ℝ) volume = heatConvolution u g := by
    rfl
  filter_upwards [htsnorm] with x hx
  have h := MeasureTheory.convolution_assoc (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (x₀ := x)
    (fun a b c => by simp only [ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.lsmul_apply, mul_smul])
    (gaussian_integrable ht).aestronglyMeasurable
    (gaussian_integrable hs).aestronglyMeasurable hf.aestronglyMeasurable
    (Eventually.of_forall hfg)
    (by simpa only [hgabs s hs, ConvolutionExistsAt, ContinuousLinearMap.mul_apply', smul_eq_mul] using hsnorm)
    (by simpa only [hnormt, hnorms, hreal, hgabs t ht, hgabs s hs, ConvolutionExistsAt, ContinuousLinearMap.mul_apply', smul_eq_mul] using hx)
  simpa only [hconv, heatConvolution, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply] using h

lemma heatOperators_add_time (t s : ℝ≥0) :
    heatOperators (𝕜 := 𝕜) (d := d) (p := p) (t+s) =
      (heatOperators t).comp (heatOperators s) := by
  by_cases ht : 0 < t
  · by_cases hs : 0 < s
    · apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      have hts : 0 < t+s := add_pos ht hs
      have hrep := heatConvolution_congr (t := (t : ℝ))
        (heatOperators_representative s hs f)
      have hassoc := heatConvolution_assoc (NNReal.coe_pos.mpr ht) (NNReal.coe_pos.mpr hs)
        f (Lp.memLp f)
      filter_upwards [heatOperators_representative (t+s) hts f,
        heatOperators_representative t ht (heatOperators s f), hassoc] with x hleft hright ha
      simpa only [ContinuousLinearMap.comp_apply, hleft, hright, hrep, NNReal.coe_add] using ha
    · have hs0 : s = 0 := le_antisymm (not_lt.mp hs) (show 0 ≤ s from zero_le)
      simp [hs0]
  · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) (show 0 ≤ t from zero_le)
    simp [ht0]

/-- Convolution by the actual Gaussian is a contraction C0 semigroup. -/
def heatSemigroup (hp : p ≠ ∞) : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p) where
  operators := heatOperators
  at_zero := heatOperators_zero
  add_time := heatOperators_add_time
  strong_zero := heatOperators_strong_zero hp

lemma heatSemigroup_isHeat (hp : p ≠ ∞) : IsHeatSemigroup (heatSemigroup (𝕜 := 𝕜) (d := d) hp) :=
  heatOperators_representative

end SemigroupLaw

theorem heat_semigroup_existence : Spec.HeatSemigroupExistence := by
  intro 𝕜 _ d p _ hp
  exact ⟨heatSemigroup hp, heatSemigroup_isHeat hp, heatOperators_norm_le⟩


@[simp] lemma gaussian_neg {d : ℕ} (t : ℝ) (x : Space d) : gaussian t (-x) = gaussian t x := by
  simp only [gaussian, Pi.neg_apply, neg_sq]

lemma heatConvolution_reflection {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (t : ℝ) (f : Space d → 𝕜) (x : Space d) :
    heatConvolution t (fun z => f (-z)) (-x) = heatConvolution t f x := by
  unfold heatConvolution
  rw [← integral_neg_eq_self (μ := (volume : Measure (Space d)))]
  simp only [gaussian_neg, neg_sub_neg, neg_sub]

section
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]

lemma heatConvolution_pairing {t : ℝ} (ht : 0 < t)
    (f g : Space d → 𝕜) (hf : MemLp f p volume) (hg : MemLp g q volume) :
    (∫ x, heatConvolution t f x * g x) = ∫ x, f x * heatConvolution t g x := by
  let ψ : Space d → 𝕜 := fun x => g (-x)
  have hψ : MemLp ψ q volume := hg.comp_measurePreserving (volume.measurePreserving_neg)
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hq : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  obtain ⟨hgf, _, _⟩ := heatConvolution_memLp_bound p hp ht f hf
  obtain ⟨hgψ, hmψ, _⟩ := heatConvolution_memLp_bound q hq ht _ hψ.norm
  let A := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
  let B := ContinuousLinearMap.mul ℝ 𝕜
  have hfg : ∀ᵐ x ∂volume, ConvolutionExistsAt f (gaussian t) x A.flip volume := by
    filter_upwards [hgf] with x hx
    exact (show ConvolutionExistsAt (gaussian t) f x A volume from hx).integrable_swap
  have hgaussnorm (x : Space d) : ‖gaussian t x‖ = gaussian t x :=
    Real.norm_of_nonneg (gaussian_nonneg ht x)
  have hnormk : (fun x : Space d => ‖gaussian t x‖) = gaussian t :=
    funext fun x => Real.norm_of_nonneg (gaussian_nonneg ht x)
  have hfgψ : ConvolutionExistsAt (fun x => ‖f x‖)
      (MeasureTheory.convolution (fun x => ‖gaussian t x‖) (fun x => ‖ψ x‖)
        (ContinuousLinearMap.mul ℝ ℝ) volume) 0 (ContinuousLinearMap.mul ℝ ℝ) volume := by
    rw [hnormk]
    exact ConvolutionExists.of_memLp_memLp _ hf.norm hmψ 0
  have hassoc := MeasureTheory.convolution_assoc A.flip B B A
    (f := f) (g := gaussian t) (k := ψ) (x₀ := (0 : Space d))
    (fun a b c => by simp [A, B, smul_eq_mul, RCLike.real_smul_eq_coe_mul, mul_assoc, mul_left_comm])
    hf.aestronglyMeasurable (gaussian_integrable ht).aestronglyMeasurable
    hψ.aestronglyMeasurable hfg
    (by simpa only [hgaussnorm, ConvolutionExistsAt, ContinuousLinearMap.mul_apply', smul_eq_mul] using hgψ)
    hfgψ
  have hconv : MeasureTheory.convolution f (gaussian t) A.flip volume = heatConvolution t f := by
    rw [MeasureTheory.convolution_flip]
    rfl
  rw [hconv] at hassoc
  change (∫ x, heatConvolution t f x * ψ (0-x)) =
    ∫ x, f x * heatConvolution t ψ (0-x) at hassoc
  simpa only [zero_sub, ψ, neg_neg, heatConvolution_reflection] using hassoc
end

lemma gaussian_hasDerivAt_time {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) :
    HasDerivAt (fun s : ℝ => gaussian s x)
      (gaussian t x * ((∑ i, (x i)^2) / (4*t^2) - (d : ℝ)/(2*t))) t := by
  have hN := (((hasDerivAt_id t).const_mul (4 * Real.pi)).rpow_const
    (p := -(d : ℝ)/2) (Or.inl (ne_of_gt (by positivity : 0 < (4*Real.pi)*t))))
  have hE := (((hasDerivAt_id t).const_mul 4).inv (by positivity : (4:ℝ)*t ≠ 0)).const_mul
    (-(∑ i : Fin d, (x i)^2))
  have hd := hN.mul hE.exp
  convert hd using 1
  · ext s
    simp only [gaussian, div_eq_mul_inv, mul_assoc, Pi.mul_apply, Pi.inv_apply, id_eq]
  · dsimp
    rw [Real.rpow_sub_one (by positivity : 4*Real.pi*t ≠ 0)]
    unfold gaussian
    field_simp
    ; ring

lemma gaussian_hasFDerivAt_space {d : ℕ} (t : ℝ) (x : Space d) :
    HasFDerivAt (gaussian t)
      ((gaussian t x) • ((-(4*t)⁻¹) •
        (∑ i : Fin d, (2*x i) • (ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ)))) x := by
  have hs : HasFDerivAt (fun y : Space d => ∑ i : Fin d, (y i)^2)
      (∑ i : Fin d, (2*x i) • (ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    simpa only [show (2-1 : ℕ) = 1 from rfl, pow_one, nsmul_eq_mul, Nat.cast_ofNat] using
      (hasFDerivAt_apply (𝕜 := ℝ) i x).pow 2
  have hE := (hs.const_mul (-(4*t)⁻¹)).exp
  have hd := hE.const_mul ((4 * Real.pi * t) ^ (-(d : ℝ) / 2))
  convert! hd using 1
  · ext y
    simp only [gaussian, div_eq_mul_inv]
    congr 2
    ring
  · ext z
    simp only [gaussian, smul_smul, smul_apply, smul_eq_mul]
    rw [show -(∑ i : Fin d, (x i)^2)/(4*t) = -(4*t)⁻¹ * ∑ i, (x i)^2 by ring]
    ring

lemma gaussian_partial {d : ℕ} (t : ℝ) (x : Space d) (i : Fin d) :
    fderiv ℝ (gaussian t) x (Distributions.coordinateVector i) =
      -(x i / (2*t)) * gaussian t x := by
  rw [(gaussian_hasFDerivAt_space t x).fderiv]
  simp only [smul_apply, sum_apply,
    Distributions.coordinateVector, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp only [Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  field_simp
  ; ring

lemma gaussian_second_partial {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) (i : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (gaussian t) y (Distributions.coordinateVector i))
      x (Distributions.coordinateVector i) =
      gaussian t x * ((x i)^2 / (4*t^2) - 1/(2*t)) := by
  simp_rw [gaussian_partial]
  have hc := ((hasFDerivAt_apply (𝕜 := ℝ) i x).mul_const (2*t)⁻¹).neg
  have hd := hc.mul (gaussian_hasFDerivAt_space t x)
  have heq : (fun y : Space d => -(y i / (2*t)) * gaussian t y) =
      (fun y => -(y i * (2*t)⁻¹)) * gaussian t := by
    ext y
    simp only [Pi.mul_apply, div_eq_mul_inv]
  rw [heq]
  change fderiv ℝ ((-fun y : Space d => y i * (2*t)⁻¹) * gaussian t)
    x (Distributions.coordinateVector i) = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    neg_apply, Pi.neg_apply,
    Distributions.coordinateVector, ContinuousLinearMap.proj_apply,
    sum_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  field_simp [ht.ne']
  ; ring

lemma gaussian_rawLaplacian {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) :
    rawLaplacian (gaussian t) x =
      gaussian t x * ((∑ i, (x i)^2) / (4*t^2) - (d : ℝ)/(2*t)) := by
  unfold rawLaplacian
  simp_rw [gaussian_second_partial ht]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma gaussian_heat_equation {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) :
    HasDerivAt (fun s : ℝ => gaussian s x) (rawLaplacian (gaussian t) x) t := by
  rw [gaussian_rawLaplacian ht]
  exact gaussian_hasDerivAt_time ht x

lemma testPartial_single {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) (φ : Test 𝕜 d) (x : Space d) :
    Distributions.testPartialCLM [i] φ x =
      fderiv ℝ φ x (Distributions.coordinateVector i) := by
  change TestFunction.lineDerivCLM 𝕜 (Distributions.coordinateVector i) φ x = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]

lemma integral_smul_testPartial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Space d → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (i : Fin d) (φ : Test 𝕜 d) :
    (∫ x, a x • Distributions.testPartialCLM [i] φ x) =
      -(∫ x, fderiv ℝ a x (Distributions.coordinateVector i) • φ x) := by
  have hda : Continuous (fun x => fderiv ℝ a x (Distributions.coordinateVector i)) :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ' : HasCompactSupport
      (fun x => fderiv ℝ φ x (Distributions.coordinateVector i)) := by
    simpa only [← testPartial_single i φ] using
      (Distributions.testPartialCLM [i] φ).hasCompactSupport
  have hcφ' : Continuous
      (fun x => fderiv ℝ φ x (Distributions.coordinateVector i)) := by
    simpa only [← testPartial_single i φ] using
      (Distributions.testPartialCLM [i] φ).continuous
  simp_rw [testPartial_single]
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    ((hda.smul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.smul_left)
    ((ha.continuous.smul hcφ').integrable_of_hasCompactSupport hφ'.smul_left)
    ((ha.continuous.smul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.smul_left)
    (fun x _ => ha.differentiable (by simp) x)
    (fun x _ => φ.contDiff.differentiable (by simp) x)

lemma integral_smul_testPartial_twice {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Space d → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (i : Fin d) (φ : Test 𝕜 d) :
    (∫ x, a x • Distributions.testPartialCLM [i,i] φ x) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ a y (Distributions.coordinateVector i))
        x (Distributions.coordinateVector i) • φ x := by
  have hda : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ a x (Distributions.coordinateVector i)) :=
    (ha.fderiv_right (by simp)).clm_apply contDiff_const
  have hcomp : Distributions.testPartialCLM [i,i] φ =
      Distributions.testPartialCLM [i] (Distributions.testPartialCLM [i] φ) := rfl
  rw [hcomp, integral_smul_testPartial a ha i,
    integral_smul_testPartial _ hda i, neg_neg]

lemma integral_smul_testLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Space d → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (φ : Test 𝕜 d) :
    (∫ x, a x • testLaplacian φ x) = ∫ x, rawLaplacian a x • φ x := by
  simp only [testLaplacian, sum_apply, Finset.smul_sum, rawLaplacian, Finset.sum_smul]
  rw [integral_finsetSum, integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_smul_testPartial_twice a ha i φ)
  · intro i _
    have hda : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => fderiv ℝ a x (Distributions.coordinateVector i)) :=
      (ha.fderiv_right (by simp)).clm_apply contDiff_const
    have hdda : Continuous (fun x => fderiv ℝ
        (fun y => fderiv ℝ a y (Distributions.coordinateVector i)) x
        (Distributions.coordinateVector i)) :=
      (hda.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hdda.smul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_left
  · intro i _
    exact (ha.continuous.smul
      (Distributions.testPartialCLM [i,i] φ).continuous).integrable_of_hasCompactSupport
      (Distributions.testPartialCLM [i,i] φ).hasCompactSupport.smul_left

lemma gaussian_smul_testLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (t : ℝ) (φ : Test 𝕜 d) :
    (∫ x, gaussian t x • testLaplacian φ x) =
      ∫ x, rawLaplacian (gaussian t) x • φ x := by
  apply integral_smul_testLaplacian
  unfold gaussian
  fun_prop


lemma gaussianFactor_sq_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x^2 * gaussianFactor t x) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq
    (inv_pos.mpr (mul_pos (by norm_num : (0:ℝ)<4) ht)) (by norm_num : (-1 : ℝ) < 2)).const_mul
      ((4 * Real.pi * t) ^ (-1/2 : ℝ))
  convert hi using 1
  ext x
  simp only [Real.rpow_two, gaussianFactor]
  ring

lemma gaussian_coordinate_sq_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) (i : Fin d) :
    Integrable (fun x : Space d => (x i)^2 * gaussian t x) := by
  classical
  let F : Fin d → ℝ → ℝ := fun j x => (if j = i then x^2 else 1) * gaussianFactor t x
  have hF : ∀ j, Integrable (F j) := by
    intro j
    by_cases hj : j = i
    · simpa only [F, if_pos hj] using gaussianFactor_sq_integrable ht
    · simpa only [F, if_neg hj, one_mul] using gaussianFactor_integrable ht
  have hi := Integrable.fintype_prod hF
  convert hi using 1
  ext x
  simp only [F, gaussian_eq_prod ht, Finset.prod_mul_distrib]
  congr 1
  simp

lemma gaussian_sum_sq_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Space d => (∑ i, (x i)^2) * gaussian t x) := by
  simp_rw [Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => gaussian_coordinate_sq_integrable ht i)

/-- An integrable envelope for all Gaussian time derivatives in a compact
positive-time interval. Its polynomial factor has degree two. -/
def gaussianTimeEnvelope {d : ℕ} (t : ℝ) (x : Space d) : ℝ :=
  ((4*Real.pi*(t/2))^(-(d:ℝ)/2) / (4*Real.pi*(2*t))^(-(d:ℝ)/2)) *
    gaussian (2*t) x * ((∑ i, (x i)^2) / t^2 + (d:ℝ)/t)

lemma gaussianTimeEnvelope_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianTimeEnvelope (d := d) t) := by
  have h2t : 0 < 2*t := by positivity
  have hi := ((gaussian_sum_sq_integrable (d := d) h2t).div_const (t^2)).add
    ((gaussian_integrable (d := d) h2t).mul_const ((d:ℝ)/t))
  convert hi.const_mul
    ((4*Real.pi*(t/2))^(-(d:ℝ)/2) / (4*Real.pi*(2*t))^(-(d:ℝ)/2)) using 1
  ext x
  simp only [gaussianTimeEnvelope, Pi.add_apply]
  ring

lemma gaussian_time_derivative_bound {d : ℕ} {t s : ℝ} (ht : 0 < t)
    (hslo : t/2 ≤ s) (hshi : s ≤ 2*t) (x : Space d) :
    ‖gaussian s x * ((∑ i, (x i)^2) / (4*s^2) - (d:ℝ)/(2*s))‖ ≤
      gaussianTimeEnvelope t x := by
  have hs : 0 < s := (half_pos ht).trans_le hslo
  have hQ : 0 ≤ ∑ i : Fin d, (x i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hN : (4*Real.pi*s)^(-(d:ℝ)/2) ≤ (4*Real.pi*(t/2))^(-(d:ℝ)/2) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by
      have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
      linarith)
    exact mul_le_mul_of_nonneg_left hslo (by positivity)
  have hE : Real.exp (-(∑ i : Fin d, (x i)^2)/(4*s)) ≤
      Real.exp (-(∑ i, (x i)^2)/(8*t)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hQ (by positivity) (by linarith)
  have hkernel : gaussian s x ≤
      (4*Real.pi*(t/2))^(-(d:ℝ)/2) * Real.exp (-(∑ i, (x i)^2)/(8*t)) :=
    mul_le_mul hN hE (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
  have hden : t^2 ≤ 4*s^2 := by nlinarith
  have hcoeff : |(∑ i : Fin d, (x i)^2)/(4*s^2) - (d:ℝ)/(2*s)| ≤
      (∑ i, (x i)^2)/t^2 + (d:ℝ)/t := by
    calc
      _ ≤ |(∑ i : Fin d, (x i)^2)/(4*s^2)| + |(d:ℝ)/(2*s)| := abs_sub _ _
      _ = (∑ i : Fin d, (x i)^2)/(4*s^2) + (d:ℝ)/(2*s) := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_left hQ (by positivity) hden)
        (div_le_div_of_nonneg_left (by positivity) ht (by linarith))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussian_nonneg hs x)]
  calc
    _ ≤ ((4*Real.pi*(t/2))^(-(d:ℝ)/2) * Real.exp (-(∑ i, (x i)^2)/(8*t))) *
        ((∑ i, (x i)^2)/t^2 + (d:ℝ)/t) :=
      mul_le_mul hkernel hcoeff (abs_nonneg _) (by positivity)
    _ = gaussianTimeEnvelope t x := by
      unfold gaussianTimeEnvelope gaussian
      rw [show 4*Real.pi*(2*t) = 8*Real.pi*t by ring,
        show 4*(2*t) = 8*t by ring]
      have hn : (8*Real.pi*t)^(-(d:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
      field_simp

/-- No surjectivity of the larger graph is assumed. -/
theorem resolvent_graph_criterion : Spec.ResolventGraphCriterion := by
  intro 𝕜 X _ _ _ A G ζ R hAG huniq
  apply le_antisymm hAG
  rintro ⟨x, y⟩ hxy
  let u : A.domain := ⟨R.inverse (ζ • x - y), R.mem_domain _⟩
  have hu : ((u : X), A u) ∈ G := hAG (A.mem_graph u)
  have heq : ζ • (u : X) - A u = ζ • x - y := R.right_inverse _
  have hhom : (x - (u : X), ζ • (x - (u : X))) ∈ G := by
    have hsub := G.sub_mem hxy hu
    have hy : y - A u = ζ • (x - (u : X)) := by
      rw [smul_sub]
      exact (sub_eq_sub_iff_sub_eq_sub.mp heq.symm).symm
    change (x - (u : X), y - A u) ∈ G at hsub
    rwa [hy] at hsub
  have hxu : x = (u : X) := sub_eq_zero.mp (huniq _ hhom)
  have hyu : y = A u := by
    rw [hxu] at heq
    exact (sub_right_inj.mp heq).symm
  exact A.mem_graph_iff.mpr ⟨u, hxu.symm, hyu.symm⟩

/-- The test operator differentiates the underlying function twice in each
coordinate, with the positive transpose sign. -/
theorem testLaplacian_formula : Spec.TestLaplacianFormula := by
  intro 𝕜 _ d φ x
  simp only [testLaplacian, sum_apply, rawLaplacian]
  apply Finset.sum_congr rfl
  intro i _
  change TestFunction.lineDerivCLM 𝕜 (Distributions.coordinateVector i)
    (Distributions.testPartialCLM [i] φ) x = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]
  congr 2

/-- No test functions are lost when passing between bundled and raw tests. -/
theorem weakLaplacian_iff_raw : Spec.RawWeakLaplacianBridge := by
  intro 𝕜 _ d p f g
  constructor
  · intro h φ hφ hc
    let ψ : Test 𝕜 d := ⟨φ, hφ, hc, Set.subset_univ _⟩
    simpa only [testLaplacian_formula 𝕜 d, ψ, TestFunction.coe_mk] using h ψ
  · intro h φ
    simpa only [testLaplacian_formula 𝕜 d] using h φ φ.contDiff φ.hasCompactSupport

section WeakGraph
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- This ensures that the weak equation uses genuine integrals. -/
theorem integrable_mul_test (f : ScalarLp 𝕜 d p) (φ : Test 𝕜 d) :
    Integrable (fun x => f x * φ x) volume := by
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
    φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (((Lp.memLp f).locallyIntegrable (Fact.out : 1 ≤ p)).locallyIntegrableOn _)

/-- Pairing against a test is scalar-linear on actual a.e. classes. -/
def testPairing (φ : Test 𝕜 d) : ScalarLp 𝕜 d p →ₗ[𝕜] 𝕜 where
  toFun f := ∫ x, f x * φ x
  map_add' f g := by
    calc
      _ = ∫ x, (f x + g x) * φ x := integral_congr_ae <| by
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx]; rfl
      _ = _ := by
        simp_rw [add_mul]
        exact integral_add (integrable_mul_test f φ) (integrable_mul_test g φ)
  map_smul' c f := by
    calc
      _ = ∫ x, c * (f x * φ x) := integral_congr_ae <| by
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
      _ = _ := integral_const_mul c _

@[simp] theorem testPairing_apply (φ : Test 𝕜 d) (f : ScalarLp 𝕜 d p) :
    testPairing φ f = ∫ x, f x * φ x := rfl

/-- The maximal distributional graph is a linear subspace. -/
def weakLaplacianGraph : Submodule 𝕜 (ScalarLp 𝕜 d p × ScalarLp 𝕜 d p) where
  carrier := {z | WeakLaplacian z.1 z.2}
  zero_mem' := by
    intro φ
    change testPairing (testLaplacian φ) 0 = testPairing φ 0
    rw [map_zero, map_zero]
  add_mem' := by
    intro z w hz hw φ
    change testPairing (testLaplacian φ) (z.1 + w.1) = testPairing φ (z.2 + w.2)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (hz φ) (hw φ)
  smul_mem' := by
    intro c z hz φ
    change testPairing (testLaplacian φ) (c • z.1) = testPairing φ (c • z.2)
    rw [map_smul, map_smul]
    exact congrArg (c • ·) (hz φ)

@[simp] theorem mem_weakLaplacianGraph (f g : ScalarLp 𝕜 d p) :
    (f, g) ∈ (weakLaplacianGraph : Submodule 𝕜 _) ↔ WeakLaplacian f g := Iff.rfl

end WeakGraph

section WeakGraphContinuity
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Integration against a smooth compactly supported test is a bounded
scalar-linear functional. Its Hölder partner is infinity when p = 1. -/
def testPairingCLM (φ : Test 𝕜 d) : ScalarLp 𝕜 d p →L[𝕜] 𝕜 := by
  let q := (1 - p⁻¹)⁻¹
  letI : ENNReal.HolderConjugate p q := ENNReal.HolderConjugate.inv_one_sub_inv' Fact.out
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  exact ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing volume p q).flip
    ((φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ)

@[simp] theorem testPairingCLM_apply (φ : Test 𝕜 d) (f : ScalarLp 𝕜 d p) :
    testPairingCLM φ f = ∫ x, f x * φ x := by
  letI : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ := ENNReal.HolderConjugate.inv_one_sub_inv' Fact.out
  letI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  unfold testPairingCLM
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(φ.continuous.memLp_of_hasCompactSupport (p := (1 - p⁻¹)⁻¹)
    (μ := volume) φ.hasCompactSupport).coeFn_toLp] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

lemma testPairing_continuous (φ : Test 𝕜 d) :
    Continuous (testPairing (p := p) φ) := by
  have heq : (testPairing (p := p) φ : ScalarLp 𝕜 d p → 𝕜) = testPairingCLM φ := by
    funext f
    simp
  rw [heq]
  exact (testPairingCLM φ).continuous

lemma generator_testPairing_tendsto
    (T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p))
    (f g : ScalarLp 𝕜 d p)
    (hg : Semigroups.C0SemigroupSpec.hasGeneratorLimitValue T f g) (φ : Test 𝕜 d) :
    Tendsto (fun h : ℝ => (algebraMap ℝ 𝕜 h)⁻¹ *
      ((∫ x, (T.operators h.toNNReal f) x * φ x) - ∫ x, f x * φ x))
      (𝓝[>] 0) (𝓝 (∫ x, g x * φ x)) := by
  have ht := ((testPairingCLM φ).continuous.tendsto g).comp hg
  change Tendsto (fun h : ℝ => testPairingCLM φ
    ((algebraMap ℝ 𝕜 h)⁻¹ • (T.operators h.toNNReal f - f)))
    (𝓝[>] 0) (𝓝 (testPairingCLM φ g)) at ht
  simpa only [map_smul, map_sub, testPairingCLM_apply, smul_eq_mul] using ht


/-- To identify a generator value distributionally, it suffices to differentiate
the tested kernel flow. The norm limit is passed through the bounded pairing. -/
lemma generator_weakLaplacian_of_tested_limit
    (T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p))
    (f g : ScalarLp 𝕜 d p)
    (hg : Semigroups.C0SemigroupSpec.hasGeneratorLimitValue T f g)
    (hflow : ∀ φ : Test 𝕜 d,
      Tendsto (fun h : ℝ => (algebraMap ℝ 𝕜 h)⁻¹ *
        ((∫ x, (T.operators h.toNNReal f) x * φ x) - ∫ x, f x * φ x))
        (𝓝[>] 0) (𝓝 (∫ x, f x * testLaplacian φ x))) :
    WeakLaplacian f g := by
  intro φ
  exact tendsto_nhds_unique (hflow φ) (generator_testPairing_tendsto T f g hg φ)
end WeakGraphContinuity

end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp

/-- Assembly of the full theorem from the three analytic subproblems. -/
theorem heat_lp_of_analytic_inputs : Spec.Assembly := by
  intro hexists hinclusion huniqueness 𝕜 _ d p _ hp
  obtain ⟨T, hheat, hcontract⟩ := hexists 𝕜 d p hp
  refine ⟨T, hheat, hcontract, ?_⟩
  have hbound : Semigroups.C0SemigroupSpec.exponentialBoundValue T 1 0 := by
    refine ⟨le_rfl, ?_⟩
    intro t
    simpa only [zero_mul, Real.exp_zero, mul_one] using hcontract t
  obtain ⟨R, _⟩ := Semigroups.LaplaceResolvent.laplace_inverse T 1 0 (1 : 𝕜)
    hbound (by simp)
  have hAG : (Semigroups.C0SemigroupSpec.generatorValue T).graph ≤
      (weakLaplacianGraph : Submodule 𝕜 _) := by
    rintro ⟨f, g⟩ hfg
    exact hinclusion 𝕜 d p hp T hheat f g
      ((Semigroups.mem_generator_graph_iff T f g).mp hfg)
  have hgraph := resolvent_graph_criterion _ weakLaplacianGraph (1 : 𝕜) R hAG
    (fun f hf => huniqueness 𝕜 d p hp f (by simpa only [one_smul, mem_weakLaplacianGraph] using hf))
  intro f g
  rw [← Semigroups.mem_generator_graph_iff T f g, hgraph]
  rfl

end ExpandedFA.Models.HeatLp

noncomputable section
open Filter Topology
open scoped SchwartzMap ContDiff
namespace HeatSchwartzDensity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_iterated_scaled_le (χ : 𝓢(E, ℝ)) {a : ℝ} (ha : ‖a‖ ≤ 1)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => χ (a • y)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n χ := by
  let L : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ 1 := by
    calc
      ‖L‖ ≤ ‖a‖ * ‖ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 * 1 := mul_le_mul ha ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have heq : (fun y => χ (a • y)) = χ ∘ L := rfl
  rw [heq, L.iteratedFDeriv_comp_right (χ.smooth ⊤) x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n χ (L x)‖ * ∏ i : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n χ (L x)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)
    _ ≤ SchwartzMap.seminorm ℝ 0 n χ := by
      simpa only [mul_one, pow_zero, one_mul] using SchwartzMap.le_seminorm ℝ 0 n χ (L x)

variable [FiniteDimensional ℝ E]

def bump : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, by norm_num⟩
def cutoff : 𝓢(E, ℝ) := (bump (E := E)).hasCompactSupport.toSchwartzMap
  (bump (E := E)).contDiff

def cutoffApprox (a : ℝ) (φ : 𝓢(E, F)) : 𝓢(E, F) :=
  SchwartzMap.smulLeftCLM F (fun x => cutoff (a • x)) φ

lemma cutoff_scaled_growth (a : ℝ) : (fun x : E => cutoff (a • x)).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.comp
  · exact SchwartzMap.hasTemperateGrowth _
  · fun_prop

lemma cutoffApprox_apply (a : ℝ) (φ : 𝓢(E, F)) (x : E) :
    cutoffApprox a φ x = cutoff (a • x) • φ x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (cutoff_scaled_growth a) φ x

lemma cutoffApprox_compact {a : ℝ} (ha : a ≠ 0) (φ : 𝓢(E, F)) :
    HasCompactSupport (cutoffApprox a φ) := by
  have heq : (cutoffApprox a φ : E → F) = fun x => cutoff (a • x) • φ x :=
    funext (cutoffApprox_apply a φ)
  rw [heq]
  exact ((bump (E := E)).hasCompactSupport.comp_smul ha).smul_right

lemma cutoffApprox_eventuallyEq {a : ℝ} (φ : 𝓢(E, F)) {x : E}
    (hx : ‖a‖ * ‖x‖ < 1) : (cutoffApprox a φ : E → F) =ᶠ[𝓝 x] φ := by
  have hm : a • x ∈ Metric.ball (0 : E) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul] using hx
  have he := (bump (E := E)).eventuallyEq_one_of_mem_ball hm
  have hc : Continuous (fun y : E => a • y) := continuous_const.smul continuous_id
  filter_upwards [hc.continuousAt.eventually he] with y hy
  rw [cutoffApprox_apply]
  change (bump (E := E)) (a • y) • φ y = φ y
  simpa only [Pi.one_apply, one_smul] using congrArg (fun r : ℝ => r • φ y) hy

lemma weighted_derivative_le_scaled (φ : 𝓢(E, F)) (k n : ℕ)
    {a : ℝ} {x : E} (hx : 1 ≤ ‖a‖ * ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n φ x‖ ≤
      ‖a‖ * SchwartzMap.seminorm ℝ (k+1) n φ := by
  calc
    _ ≤ (‖a‖ * ‖x‖) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n φ x‖) :=
      le_mul_of_one_le_left (by positivity) hx
    _ = ‖a‖ * (‖x‖ ^ (k+1) * ‖iteratedFDeriv ℝ n φ x‖) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℝ (k+1) n φ x) (norm_nonneg _)

lemma cutoffApprox_seminorm_le (φ : 𝓢(E, F)) (k n : ℕ)
    {a : ℝ} (ha : ‖a‖ ≤ 1) :
    SchwartzMap.seminorm ℝ k n (cutoffApprox a φ - φ) ≤ ‖a‖ *
      ((∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℝ 0 i (cutoff (E := E)) * SchwartzMap.seminorm ℝ (k+1) (n-i) φ) +
        SchwartzMap.seminorm ℝ (k+1) n φ) := by
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((cutoffApprox a φ : E → F) - (φ : E → F)) x‖ ≤ _
  by_cases hx : ‖a‖ * ‖x‖ < 1
  · have heq := (cutoffApprox_eventuallyEq φ hx).iteratedFDeriv (𝕜 := ℝ) n
    rw [iteratedFDeriv_sub (SchwartzMap.smooth _ n) (φ.smooth n)]
    simp only [heq.self_of_nhds, Pi.sub_apply, sub_self, norm_zero, mul_zero]
    positivity
  · have hx' : 1 ≤ ‖a‖ * ‖x‖ := le_of_not_gt hx
    have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => cutoff (a • y)) :=
      (SchwartzMap.smooth _ ⊤).comp (contDiff_const.smul contDiff_id)
    have hprod := norm_iteratedFDeriv_smul_le hcut (φ.smooth ⊤) x (n := n) (by simp)
    have hrep : (cutoffApprox a φ : E → F) = fun y => cutoff (a • y) • φ y :=
      funext (cutoffApprox_apply a φ)
    rw [← hrep] at hprod
    rw [iteratedFDeriv_sub (SchwartzMap.smooth _ n) (φ.smooth n)]
    calc
      _ ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n (cutoffApprox a φ) x‖ + ‖iteratedFDeriv ℝ n φ x‖) := by
        gcongr; exact norm_sub_le _ _
      _ ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => cutoff (a • y)) x‖ * ‖iteratedFDeriv ℝ (n-i) φ x‖) +
          ‖a‖ * SchwartzMap.seminorm ℝ (k+1) n φ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
          (weighted_derivative_le_scaled φ k n hx')
      _ ≤ ‖a‖ * (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (cutoff (E := E)) * SchwartzMap.seminorm ℝ (k+1) (n-i) φ) +
          ‖a‖ * SchwartzMap.seminorm ℝ (k+1) n φ := by
        gcongr ?_ + _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ = ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => cutoff (a • y)) x‖) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n-i) φ x‖) := by ring
          _ ≤ ((n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (cutoff (E := E))) *
              (‖a‖ * SchwartzMap.seminorm ℝ (k+1) (n-i) φ) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (norm_iterated_scaled_le _ ha i x) (by positivity))
              (weighted_derivative_le_scaled φ k (n-i) hx') (by positivity) (by positivity)
          _ = _ := by ring
      _ = _ := by ring

lemma cutoffApprox_tendsto (φ : 𝓢(E, F)) :
    Tendsto (fun a : ℝ => cutoffApprox a φ) (𝓝[>] 0) (𝓝 φ) := by
  apply ((schwartz_withSeminorms ℝ E F).tendsto_nhds (fun a : ℝ => cutoffApprox a φ) φ).mpr
  rintro ⟨k,n⟩ ε hε
  let C : ℝ := (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (cutoff (E := E)) * SchwartzMap.seminorm ℝ (k+1) (n-i) φ) +
    SchwartzMap.seminorm ℝ (k+1) n φ
  have hlim : Tendsto (fun a : ℝ => ‖a‖ * C) (𝓝[>] 0) (𝓝 0) := by
    simpa only [norm_zero, zero_mul] using
      ((show Continuous (fun a : ℝ => ‖a‖ * C) from continuous_norm.mul continuous_const).tendsto 0).mono_left
        nhdsWithin_le_nhds
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, ‖a‖ ≤ 1 := by
    have hnorm : Tendsto (fun a : ℝ => ‖a‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact ((tendsto_order.mp hnorm).2 1 zero_lt_one).mono (fun _ h => h.le)
  filter_upwards [hsmall, (tendsto_order.mp hlim).2 ε hε] with a ha hbound
  exact (cutoffApprox_seminorm_le φ k n ha).trans_lt hbound

lemma tempered_eq_zero_of_compact_tests
    (u : 𝓢(E, ℂ) →L[ℂ] ℂ)
    (hu : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → u φ = 0) : u = 0 := by
  ext φ
  have ht := (u.continuous.tendsto φ).comp (cutoffApprox_tendsto φ)
  have heq : (fun a : ℝ => u (cutoffApprox a φ)) =ᶠ[𝓝[>] 0] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    exact hu _ (cutoffApprox_compact ha.ne' _)
  have hz : Tendsto (fun a : ℝ => u (cutoffApprox a φ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique ht hz

lemma native_tempered_eq_zero_of_compact_tests
    (u : 𝓢'(E, ℂ))
    (hu : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → u φ = 0) : u = 0 := by
  change (u : 𝓢(E, ℂ) →L[ℂ] ℂ) = 0
  exact tempered_eq_zero_of_compact_tests u hu

end HeatSchwartzDensity

noncomputable section
open MeasureTheory Laplacian FourierTransform
open scoped SchwartzMap ENNReal NNReal
namespace ExpandedFA.Models.HeatLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma resolvent_symbol_growth :
    (fun x : E => (1 + (2 * Real.pi)^2 * ‖x‖ ^ 2 : ℝ)).HasTemperateGrowth := by
  fun_prop

lemma resolvent_inverse_growth :
    (fun x : E => (1 + (2 * Real.pi)^2 * ‖x‖ ^ 2 : ℝ)⁻¹).HasTemperateGrowth := by
  have h := (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-1)).comp
    ((2 * Real.pi) • (ContinuousLinearMap.id ℝ E)).hasTemperateGrowth
  convert h using 1
  ext x
  simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    Real.rpow_neg_one, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma tempered_fourierMultiplier_add {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth)
    (u : 𝓢'(E, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ (g₁ + g₂) u =
      TemperedDistribution.fourierMultiplierCLM ℂ g₁ u +
        TemperedDistribution.fourierMultiplierCLM ℂ g₂ u := by
  simp only [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_add hg₁ hg₂, add_apply,
    FourierTransform.fourierInv_add]

lemma tempered_elliptic_uniqueness (u : 𝓢'(E, ℂ)) (hu : Δ u = u) : u = 0 := by
  let g : E → ℂ := fun x => ((1 + (2 * Real.pi)^2 * ‖x‖ ^ 2 : ℝ) : ℂ)
  let h : E → ℂ := fun x => (((1 + (2 * Real.pi)^2 * ‖x‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)
  have hg : g.HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp resolvent_symbol_growth
  have hh : h.HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp resolvent_inverse_growth
  have hgh : g * h = fun _ => 1 := by
    ext x
    change ((1 + (2 * Real.pi)^2 * ‖x‖ ^ 2 : ℝ) : ℂ) *
      (((1 + (2 * Real.pi)^2 * ‖x‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
  have hgdef : g = (fun _ : E => (1 : ℂ)) +
      ((2 * (Real.pi : ℂ))^2) • (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x
    simp [g]
  have hM : TemperedDistribution.fourierMultiplierCLM ℂ g u = 0 := by
    rw [hgdef, tempered_fourierMultiplier_add (by fun_prop) (by fun_prop),
      TemperedDistribution.fourierMultiplierCLM_const,
      TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop)]
    simp only [one_smul, ContinuousLinearMap.id_apply, smul_apply]
    have hlap := TemperedDistribution.laplacian_eq_fourierMultiplierCLM u
    rw [hu] at hlap
    rw [← Complex.coe_smul] at hlap
    have hlap' : u = -(((2 * (Real.pi : ℂ)) ^ 2) •
        TemperedDistribution.fourierMultiplierCLM ℂ (fun x : E => (‖x‖ ^ 2 : ℝ)) u) := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat, neg_smul] using hlap
    exact eq_neg_iff_add_eq_zero.mp hlap'
  calc
    u = TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : E => (1 : ℂ)) u := by simp
    _ = TemperedDistribution.fourierMultiplierCLM ℂ h
      (TemperedDistribution.fourierMultiplierCLM ℂ g u) := by
      rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hg hh, hgh]
    _ = 0 := by rw [hM, map_zero]


open WithLp
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

def coordEquiv (d : ℕ) : Euclidean d ≃L[ℝ] Space d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

lemma rawLaplacian_toEuclidean {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Euclidean d → 𝕜) (x : Space d) :
    rawLaplacian (φ ∘ (coordEquiv d).symm) x =
      ∑ i : Fin d, fderiv ℝ (fun y =>
        fderiv ℝ φ y (EuclideanSpace.single i 1)) ((coordEquiv d).symm x)
          (EuclideanSpace.single i 1) := by
  simp only [rawLaplacian]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ
      ((fun y : Euclidean d => fderiv ℝ φ y (EuclideanSpace.single i 1)) ∘
        (coordEquiv d).symm) x (Distributions.coordinateVector i) = _
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rfl

lemma schwartz_laplacian_coordinate {d : ℕ} (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    (Δ φ) x = ∑ i : Fin d, fderiv ℝ (fun y =>
      fderiv ℝ φ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  congr 2



theorem complex_elliptic_uniqueness {d : ℕ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (f : ScalarLp ℂ d p) (hf : RawWeakLaplacian f f) : f = 0 := by
  let F : Lp ℂ p (volume : Measure (Euclidean d)) :=
    Lp.compMeasurePreserving ofLp (PiLp.volume_preserving_ofLp (Fin d)) f
  have hF : F =ᵐ[volume] f ∘ ofLp :=
    Lp.coeFn_compMeasurePreserving f (PiLp.volume_preserving_ofLp (Fin d))
  let u : 𝓢'(Euclidean d, ℂ) := Lp.toTemperedDistribution F
  have hu : Δ u = u := by
    apply sub_eq_zero.mp
    apply HeatSchwartzDensity.native_tempered_eq_zero_of_compact_tests
    intro φ hφ
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ((φ : Euclidean d → ℂ) ∘ (coordEquiv d).symm) :=
      (φ.smooth ⊤).comp (coordEquiv d).symm.contDiff
    have hψc : HasCompactSupport ((φ : Euclidean d → ℂ) ∘ (coordEquiv d).symm) :=
      hφ.comp_homeomorph (coordEquiv d).symm.toHomeomorph
    have hw := hf _ hψ hψc
    have he (ψ : 𝓢(Euclidean d, ℂ)) :
        (∫ x : Euclidean d, ψ x * F x) =
          ∫ x : Space d, f x * ψ ((coordEquiv d).symm x) := by
      calc
        _ = ∫ x : Euclidean d, f (ofLp x) * ψ x := integral_congr_ae <| by
          filter_upwards [hF] with x hx
          rw [hx]
          exact mul_comm _ _
        _ = _ := by
          exact (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
            (coordEquiv d).toHomeomorph.measurableEmbedding
            (fun x : Space d => f x * ψ ((coordEquiv d).symm x))
    change (Δ u) φ - u φ = 0
    rw [TemperedDistribution.laplacian_apply_apply]
    simp only [u, Lp.toTemperedDistribution_apply, smul_eq_mul]
    rw [he, he]
    apply sub_eq_zero.mpr
    convert hw using 1
    · apply integral_congr_ae
      filter_upwards [] with x
      rw [rawLaplacian_toEuclidean, schwartz_laplacian_coordinate]
    · rfl
  have hu0 : u = 0 := tempered_elliptic_uniqueness u hu
  have hF0 : F = 0 := by
    have hker : F ∈ (Lp.toTemperedDistributionCLM ℂ volume p).ker := hu0
    rw [Lp.ker_toTemperedDistributionCLM_eq_bot, Submodule.mem_bot] at hker
    exact hker
  apply (Lp.isometry_compMeasurePreserving (PiLp.volume_preserving_ofLp (Fin d))).injective
  simpa only [map_zero] using hF0

end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp
lemma rawLaplacian_compCLM {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜'] {d : ℕ}
    (L : 𝕜 →L[ℝ] 𝕜') (φ : Space d → 𝕜) (hφ : ContDiff ℝ ∞ φ) (x : Space d) :
    rawLaplacian (L ∘ φ) x = L (rawLaplacian φ x) := by
  unfold rawLaplacian
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hfirst : (fun y => fderiv ℝ (L ∘ φ) y (Distributions.coordinateVector i)) =
      L ∘ (fun y => fderiv ℝ φ y (Distributions.coordinateVector i)) := by
    funext y
    rw [fderiv_comp y L.differentiableAt (hφ.differentiable (by simp) y), L.fderiv]
    rfl
  rw [hfirst, fderiv_comp x L.differentiableAt
    (((hφ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp) x), L.fderiv]
  rfl

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma complexMap_injective : Function.Injective (RCLike.map 𝕜 ℂ) := by
  intro a b h
  have hn : ‖a-b‖ = 0 := by
    rw [← RCLike.norm_to_complex (a-b)]
    change ‖RCLike.map 𝕜 ℂ (a-b)‖ = 0
    rw [map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def complexifyLp (f : ScalarLp 𝕜 d p) : ScalarLp ℂ d p :=
  (RCLike.map 𝕜 ℂ).compLp f

lemma complexifyLp_representative (f : ScalarLp 𝕜 d p) :
    complexifyLp f =ᵐ[volume] fun x => RCLike.map 𝕜 ℂ (f x) :=
  ContinuousLinearMap.coeFn_compLp _ _

lemma complexifyLp_eq_zero_iff (f : ScalarLp 𝕜 d p) : complexifyLp f = 0 ↔ f = 0 := by
  constructor
  · intro h
    rw [Lp.eq_zero_iff_ae_eq_zero] at h ⊢
    filter_upwards [complexifyLp_representative f, h] with x hx hz
    apply complexMap_injective
    simpa only [map_zero, Pi.zero_apply] using hx.symm.trans hz
  · intro h
    subst f
    simp [complexifyLp, ContinuousLinearMap.compLp]

lemma cf_integrable_mul_test (f : ScalarLp 𝕜 d p) (φ : Test 𝕜 d) :
    Integrable (fun x => f x * φ x) volume := by
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
    φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (((Lp.memLp f).locallyIntegrable (Fact.out : 1 ≤ p)).locallyIntegrableOn _)

/-- Postcompose a real test by the canonical real scalar embedding. -/
def liftRealTest (φ : Test ℝ d) : Test 𝕜 d :=
  TestFunction.postcompCLM (𝕜 := ℝ) RCLike.ofRealCLM φ

@[simp] lemma liftRealTest_apply (φ : Test ℝ d) (x : Space d) :
    liftRealTest (𝕜 := 𝕜) φ x = (φ x : 𝕜) := rfl

lemma liftRealTest_laplacian (φ : Test ℝ d) (x : Space d) :
    testLaplacian (liftRealTest (𝕜 := 𝕜) φ) x = (testLaplacian φ x : 𝕜) := by
  simp only [testLaplacian_formula 𝕜 d, testLaplacian_formula ℝ d]
  exact rawLaplacian_compCLM RCLike.ofRealCLM φ φ.contDiff x

lemma complexMap_mul_ofReal (a : 𝕜) (r : ℝ) :
    RCLike.map 𝕜 ℂ (a * (r : 𝕜)) = RCLike.map 𝕜 ℂ a * (r : ℂ) := by
  rw [mul_comm a, ← RCLike.real_smul_eq_coe_mul, map_smul, RCLike.real_smul_eq_coe_mul]
  exact mul_comm _ _

lemma complexify_real_test_equation (f : ScalarLp 𝕜 d p) (hf : WeakLaplacian f f)
    (φ : Test ℝ d) :
    (∫ x, complexifyLp f x * (testLaplacian φ x : ℂ)) =
      ∫ x, complexifyLp f x * (φ x : ℂ) := by
  have heq := congrArg (RCLike.map 𝕜 ℂ) (hf (liftRealTest φ))
  rw [← (RCLike.map 𝕜 ℂ).integral_comp_comm (cf_integrable_mul_test f (testLaplacian (liftRealTest φ))),
    ← (RCLike.map 𝕜 ℂ).integral_comp_comm (cf_integrable_mul_test f (liftRealTest φ))] at heq
  have hleft : (fun x => RCLike.map 𝕜 ℂ (f x * testLaplacian (liftRealTest φ) x)) =ᵐ[volume]
      (fun x => complexifyLp f x * (testLaplacian φ x : ℂ)) := by
    filter_upwards [complexifyLp_representative f] with x hx
    rw [liftRealTest_laplacian, complexMap_mul_ofReal, hx]
  have hright : (fun x => RCLike.map 𝕜 ℂ (f x * liftRealTest φ x)) =ᵐ[volume]
      (fun x => complexifyLp f x * (φ x : ℂ)) := by
    filter_upwards [complexifyLp_representative f] with x hx
    rw [liftRealTest_apply, complexMap_mul_ofReal, hx]
  exact (integral_congr_ae hleft).symm.trans (heq.trans (integral_congr_ae hright))

def cf_testPairingTranspose (f : ScalarLp 𝕜 d p) : Test 𝕜 d →ₗ[𝕜] 𝕜 where
  toFun φ := ∫ x, f x * φ x
  map_add' φ ψ := by
    simp only [add_apply, mul_add]
    exact integral_add (cf_integrable_mul_test f φ) (cf_integrable_mul_test f ψ)
  map_smul' c φ := by
    change (∫ x, f x * (c * φ x)) = c * ∫ x, f x * φ x
    simp_rw [show ∀ x, f x * (c * φ x) = c * (f x * φ x) by intro x; ring]
    exact integral_const_mul _ _

lemma complexify_weakLaplacian (f : ScalarLp 𝕜 d p) (hf : WeakLaplacian f f) :
    WeakLaplacian (complexifyLp f) (complexifyLp f) := by
  let F := complexifyLp f
  let B := cf_testPairingTranspose F
  let D : Test ℂ d →ₗ[ℂ] ℂ := B.comp testLaplacian.toLinearMap - B
  have hreal (φ : Test ℝ d) : D (liftRealTest φ) = 0 := by
    change (∫ x, F x * testLaplacian (liftRealTest φ) x) - (∫ x, F x * liftRealTest φ x) = 0
    simp only [liftRealTest_laplacian, liftRealTest_apply]
    exact sub_eq_zero.mpr (complexify_real_test_equation f hf φ)
  intro ψ
  let ψre : Test ℝ d := TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM ψ
  let ψim : Test ℝ d := TestFunction.postcompCLM (𝕜 := ℝ) Complex.imCLM ψ
  have hψ : ψ = liftRealTest ψre + Complex.I • liftRealTest ψim := by
    ext x
    change ψ x = (Complex.re (ψ x) : ℂ) + Complex.I * (Complex.im (ψ x) : ℂ)
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (ψ x)).symm
  have hD : D ψ = 0 := by
    rw [hψ, map_add, map_smul, hreal, hreal, smul_zero, add_zero]
  exact sub_eq_zero.mp hD

lemma rclike_elliptic_uniqueness_of_complex
    (hcomplex : ∀ {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ScalarLp ℂ d p),
      WeakLaplacian f f → f = 0)
    (f : ScalarLp 𝕜 d p) (hf : WeakLaplacian f f) : f = 0 := by
  exact (complexifyLp_eq_zero_iff f).mp (hcomplex _ (complexify_weakLaplacian f hf))


/-- Homogeneous elliptic uniqueness includes the L1 endpoint. -/
theorem elliptic_uniqueness : Spec.EllipticUniqueness := by
  intro 𝕜 _ d p _ _ f hf
  exact rclike_elliptic_uniqueness_of_complex
    (fun {d p} _ g hg => complex_elliptic_uniqueness g
      ((weakLaplacian_iff_raw ℂ d p g g).mp hg)) f hf
end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp
section
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
open Distributions.ConvolutionEndpointBoundsSpec

def convolutionLpValue (f : ScalarLp 𝕜 d p) (k : ScalarLp 𝕜 d 1) : ScalarLp 𝕜 d p :=
  ((Distributions.young_l1_lp_endpoint p Fact.out k f (Lp.memLp k) (Lp.memLp f)).2.2.1).toLp
    (ConvolutionValue k f)

lemma convolutionLpValue_representative (f : ScalarLp 𝕜 d p) (k : ScalarLp 𝕜 d 1) :
    convolutionLpValue f k =ᵐ[volume] ConvolutionValue k f := MemLp.coeFn_toLp _

lemma convolutionLpValue_norm (f : ScalarLp 𝕜 d p) (k : ScalarLp 𝕜 d 1) :
    ‖convolutionLpValue f k‖ ≤ ‖f‖ * ‖k‖ := by
  rw [convolutionLpValue, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp k).ne (Lp.memLp f).ne)
    (Distributions.young_l1_lp_endpoint p Fact.out k f (Lp.memLp k) (Lp.memLp f)).2.2.2).trans_eq
      (by simp only [ENNReal.toReal_mul]; ring)

lemma convolutionLpValue_add (f : ScalarLp 𝕜 d p) (k l : ScalarLp 𝕜 d 1) :
    convolutionLpValue f (k+l) = convolutionLpValue f k + convolutionLpValue f l := by
  apply Lp.ext
  have heq := (Distributions.convolution_representative_independence (k+l)
    (fun x => k x+l x) f f (Lp.coeFn_add k l) (EventuallyEq.refl _ _)).2
  filter_upwards [convolutionLpValue_representative f (k+l),
    convolutionLpValue_representative f k, convolutionLpValue_representative f l,
    Lp.coeFn_add (convolutionLpValue f k) (convolutionLpValue f l),
    (Distributions.young_l1_lp_endpoint p Fact.out k f (Lp.memLp k) (Lp.memLp f)).1,
    (Distributions.young_l1_lp_endpoint p Fact.out l f (Lp.memLp l) (Lp.memLp f)).1]
    with x hkl hk hl hadd hki hli
  rw [hkl, hadd, Pi.add_apply, hk, hl, heq]
  change (∫ y, (k y+l y)*f (x-y)) = _
  simp_rw [add_mul]
  exact integral_add hki hli

lemma convolutionLpValue_smul (f : ScalarLp 𝕜 d p) (k : ScalarLp 𝕜 d 1) (c : 𝕜) :
    convolutionLpValue f (c • k) = c • convolutionLpValue f k := by
  apply Lp.ext
  have heq := (Distributions.convolution_representative_independence (c • k)
    (fun x => c * k x) f f (Lp.coeFn_smul c k) (EventuallyEq.refl _ _)).2
  filter_upwards [convolutionLpValue_representative f (c • k),
    convolutionLpValue_representative f k, Lp.coeFn_smul c (convolutionLpValue f k)]
    with x hck hk hsmul
  rw [hck, hsmul, Pi.smul_apply, hk, heq]
  change (∫ y, (c*k y)*f (x-y)) = c * ∫ y, k y*f (x-y)
  simp_rw [mul_assoc]
  exact integral_const_mul c _

/-- Fixing the Lp factor leaves a bounded linear map in the L1 kernel. -/
def convolutionKernelCLM (f : ScalarLp 𝕜 d p) : ScalarLp 𝕜 d 1 →L[𝕜] ScalarLp 𝕜 d p :=
  LinearMap.mkContinuous
    { toFun := convolutionLpValue f
      map_add' := convolutionLpValue_add f
      map_smul' := fun c k => convolutionLpValue_smul f k c }
    ‖f‖ (convolutionLpValue_norm f)

/-- Real L1 kernels act continuously and real-linearly on scalar Lp. -/
def realKernelCLM (f : ScalarLp 𝕜 d p) : ScalarLp ℝ d 1 →L[ℝ] ScalarLp 𝕜 d p :=
  ((convolutionKernelCLM f).restrictScalars ℝ).comp
    ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLpL (p := 1) (μ := volume))

lemma realKernelCLM_representative (f : ScalarLp 𝕜 d p) (k : ScalarLp ℝ d 1) :
    realKernelCLM f k =ᵐ[volume] (fun x => ∫ y, k y • f (x-y)) := by
  have hk := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLp k
  have hc := convolutionLpValue_representative f ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k)
  have heq := (Distributions.convolution_representative_independence
    ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k) (fun x => (k x : 𝕜)) f f hk
    (EventuallyEq.refl _ _)).2
  filter_upwards [hc] with x hx
  change convolutionLpValue f ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k) x = _
  rw [hx, heq]
  simp only [ConvolutionValue, RCLike.real_smul_eq_coe_mul]
end

end ExpandedFA.Models.HeatLp

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MeasureTheory

lemma eLpNorm_one_slope_sub_derivative_tendsto
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {F F' : ℝ → α → E} {D : α → ℝ} {t : ℝ} {I : Set ℝ}
    (hI : I ∈ 𝓝 t) (hconv : Convex ℝ I)
    (hF : ∀ s, Measurable (F s)) (hF' : Measurable (F' t))
    (hDiff : ∀ s ∈ I, ∀ x, HasDerivAt (fun r => F r x) (F' s x) s)
    (hBound : ∀ s ∈ I, ∀ x, ‖F' s x‖ ≤ D x) (hD : Integrable D μ) :
    Tendsto (fun s : ℝ => eLpNorm
      (fun x => (s-t)⁻¹ • (F s x - F t x) - F' t x) 1 μ)
      (𝓝[≠] t) (𝓝 0) := by
  have htI : t ∈ I := mem_of_mem_nhds hI
  have hDpos (x : α) : 0 ≤ D x := (norm_nonneg (F' t x)).trans (hBound t htI x)
  have hLip (x : α) : LipschitzOnWith (Real.nnabs (D x)) (fun s => F s x) I := by
    apply hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (hDiff s hs x).hasDerivWithinAt)
    intro s hs
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg (hDpos x)]
    exact hBound s hs x
  have hSlope (s : ℝ) (hs : s ∈ I) (x : α) :
      ‖(s-t)⁻¹ • (F s x - F t x)‖ ≤ D x := by
    have hb := (hLip x).norm_sub_le hs htI
    rw [Real.coe_nnabs, abs_of_nonneg (hDpos x)] at hb
    by_cases hst : s = t
    · simp only [hst, sub_self, inv_zero, zero_smul, norm_zero]
      exact hDpos x
    · rw [norm_smul, norm_inv]
      calc
        _ ≤ ‖s-t‖⁻¹ * (D x * ‖s-t‖) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = D x := by
          rw [mul_comm (D x), ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hst)), one_mul]
  have hErr (s : ℝ) (hs : s ∈ I) (x : α) :
      ‖(s-t)⁻¹ • (F s x-F t x) - F' t x‖ ≤ D x + D x := by
    exact (norm_sub_le _ _).trans (add_le_add (hSlope s hs x) (hBound t htI x))
  have hMeas (s : ℝ) : Measurable
      (fun x => (s-t)⁻¹ • (F s x-F t x) - F' t x) :=
    (((hF s).sub (hF t)).const_smul _).sub hF'
  have hPoint (x : α) : Tendsto
      (fun s : ℝ => ‖(s-t)⁻¹ • (F s x-F t x) - F' t x‖ₑ)
      (𝓝[≠] t) (𝓝 0) := by
    have hp := ((hDiff t htI x).tendsto_slope.sub_const (F' t x)).enorm
    simpa only [slope_def_module, sub_self, enorm_zero] using hp
  have hDom : ∀ᶠ s : ℝ in 𝓝[≠] t, ∀ᵐ x ∂μ,
      ‖(s-t)⁻¹ • (F s x-F t x) - F' t x‖ₑ ≤ ‖D x + D x‖ₑ := by
    filter_upwards [nhdsWithin_le_nhds hI] with s hs
    apply Eventually.of_forall
    intro x
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hDpos x) (hDpos x))]
    exact hErr s hs x
  have hLim := tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ) (F := fun s : ℝ => fun x : α =>
      ‖(s-t)⁻¹ • (F s x-F t x) - F' t x‖ₑ) (f := fun _ => 0)
    (fun x => ‖D x + D x‖ₑ)
    (Eventually.of_forall fun s => (hMeas s).enorm)
    hDom ((hasFiniteIntegral_iff_enorm.mp (hD.add hD).2).ne)
    (Eventually.of_forall hPoint)
  simp only [lintegral_zero] at hLim
  simpa only [eLpNorm_one_eq_lintegral_enorm (hMeas _).aestronglyMeasurable] using hLim

end MeasureTheory

namespace ExpandedFA.Models.HeatLp
lemma gaussian_time_derivative_eLpNorm_tendsto {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s : ℝ => eLpNorm
      ((s-t)⁻¹ • (gaussian (d := d) s - gaussian t) -
        (fun x : Space d => gaussian t x *
          ((∑ i, (x i)^2) / (4*t^2) - (d:ℝ)/(2*t)))) 1 volume)
      (𝓝[≠] t) (𝓝 0) := by
  apply eLpNorm_one_slope_sub_derivative_tendsto
    (F := fun s : ℝ => gaussian (d := d) s)
    (F' := fun s x => gaussian s x *
      ((∑ i, (x i)^2)/(4*s^2) - (d:ℝ)/(2*s)))
    (I := Set.Icc (t/2) (2*t)) (D := gaussianTimeEnvelope t)
    (Icc_mem_nhds (by linarith) (by linarith)) (convex_Icc _ _)
    (fun s => (gaussian_continuous s).measurable)
  · apply Continuous.measurable
    apply Continuous.mul (gaussian_continuous t)
    fun_prop
  · intro s hs x
    exact gaussian_hasDerivAt_time ((half_pos ht).trans_le hs.1) x
  · intro s hs x
    exact gaussian_time_derivative_bound ht hs.1 hs.2 x
  · exact gaussianTimeEnvelope_integrable ht

lemma gaussian_time_derivative_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Space d => gaussian t x *
      ((∑ i, (x i)^2)/(4*t^2) - (d:ℝ)/(2*t))) := by
  apply (gaussianTimeEnvelope_integrable ht).mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (gaussian_continuous t)
    fun_prop
  · apply Eventually.of_forall
    intro x
    exact gaussian_time_derivative_bound ht (by linarith) (by linarith) x

/-- The Gaussian as an actual L1 curve, extended by zero outside positive times. -/
def gaussianL1 {d : ℕ} (t : ℝ) : Lp ℝ 1 (volume : Measure (Space d)) :=
  if ht : 0 < t then (gaussian_integrable ht).toL1 (gaussian t) else 0

lemma gaussianL1_representative {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (gaussianL1 (d := d) t : Space d → ℝ) =ᵐ[volume] gaussian t := by
  simp only [gaussianL1, dite_eq_left ht]
  exact Integrable.coeFn_toL1 _

lemma gaussianL1_hasDerivAt {d : ℕ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianL1 (d := d))
      ((gaussian_time_derivative_integrable (d := d) ht).toL1
        (fun x : Space d => gaussian t x *
          ((∑ i, (x i)^2)/(4*t^2) - (d:ℝ)/(2*t)))) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply (gaussian_time_derivative_eLpNorm_tendsto (d := d) ht).congr'
  have hpos : ∀ᶠ s : ℝ in 𝓝[≠] t, 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds ht)
  filter_upwards [hpos] with s hs
  have hrep : (slope (gaussianL1 (d := d)) t s : Space d → ℝ) =ᵐ[volume]
      (s-t)⁻¹ • (gaussian s - gaussian t) := by
    rw [slope_def_module]
    exact (Lp.coeFn_smul _ _).trans
      (((Lp.coeFn_sub _ _).trans
        ((gaussianL1_representative hs).sub (gaussianL1_representative ht))).const_smul _)
  exact (eLpNorm_congr_ae (hrep.sub (Integrable.coeFn_toL1 _))).symm

end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp
lemma gaussian_continuousAt_joint {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Space d) :
    ContinuousAt (fun z : ℝ × Space d => gaussian z.1 z.2) (s,x) := by
  have hN : ContinuousAt (fun z : ℝ × Space d => 4*Real.pi*z.1) (s,x) := by
    exact (continuous_const.mul continuous_fst).continuousAt
  have hS : Continuous (fun z : ℝ × Space d => ∑ i, (z.2 i)^2) := by fun_prop
  have hD : ContinuousAt (fun z : ℝ × Space d => 4*z.1) (s,x) :=
    (continuous_const.mul continuous_fst).continuousAt
  have hE : ContinuousAt (fun z : ℝ × Space d => Real.exp (-(∑ i, (z.2 i)^2)/(4*z.1))) (s,x) :=
    Real.continuous_exp.continuousAt.comp
      (hS.continuousAt.neg.div hD (by positivity : (4:ℝ)*s ≠ 0))
  exact (hN.rpow_const (p := -(d : ℝ)/2) (Or.inl (by positivity))).mul hE

set_option maxHeartbeats 500000 in
lemma gaussian_test_integral_hasDerivAt {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {t : ℝ} (ht : 0 < t) (φ : Test 𝕜 d) :
    HasDerivAt (fun s : ℝ => ∫ x, gaussian s x • φ x)
      (∫ x, gaussian t x • testLaplacian φ x) t := by
  let D : ℝ → Space d → 𝕜 := fun s x =>
    (gaussian s x * ((∑ i, (x i)^2)/(4*s^2) - (d : ℝ)/(2*s))) • φ x
  let K : Set (ℝ × Space d) := Set.Icc (t/2) (3*t/2) ×ˢ tsupport φ
  have hDc : ContinuousOn (Function.uncurry D) K := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hs : 0 < z.1 := lt_of_lt_of_le (half_pos ht) hz.1.1
    have hga := gaussian_continuousAt_joint hs z.2
    have hS : ContinuousAt (fun w : ℝ × Space d => ∑ i, (w.2 i)^2) z := by fun_prop
    have hT : ContinuousAt (fun w : ℝ × Space d => w.1) z := continuous_fst.continuousAt
    have hcoef : ContinuousAt (fun w : ℝ × Space d =>
        (∑ i, (w.2 i)^2)/(4*w.1^2) - (d : ℝ)/(2*w.1)) z :=
      (hS.div ((continuous_const.continuousAt).mul (hT.pow 2))
        (by change 4*z.1^2 ≠ 0; positivity)).sub
        (continuous_const.continuousAt.div (continuous_const.continuousAt.mul hT)
          (by change 2*z.1 ≠ 0; positivity))
    exact (hga.mul hcoef).smul (φ.continuous.comp continuous_snd).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod φ.hasCompactSupport.isCompact).exists_bound_of_continuousOn hDc
  have hDcont : Continuous (D t) := by
    have hga : Continuous (gaussian (d := d) t) :=
      continuous_iff_continuousAt.mpr fun x => (gaussian_hasFDerivAt_space t x).continuousAt
    have hsum : Continuous (fun x : Space d => ∑ i : Fin d, (x i)^2) :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2
    have hcoef : Continuous (fun x : Space d =>
        (∑ i, (x i)^2)/(4*t^2) - (d : ℝ)/(2*t)) :=
      (hsum.div_const _).sub continuous_const
    exact (hga.mul hcoef).smul φ.continuous
  have hFint : Integrable (fun x : Space d => gaussian t x • φ x) := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.smul _ φ.continuous
      unfold gaussian
      fun_prop
    · exact φ.hasCompactSupport.smul_left (f := gaussian t)
  have hI : Set.Icc (t/2) (3*t/2) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hBoundInt : Integrable ((tsupport φ).indicator (fun _ : Space d => C)) := by
    rw [integrable_indicator_iff φ.hasCompactSupport.isCompact.measurableSet]
    exact integrableOn_const φ.hasCompactSupport.isCompact.measure_lt_top.ne
  have hDiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s : ℝ => fun x : Space d => gaussian s x • φ x)
    (F' := D) hI
    (Eventually.of_forall fun s => by
      apply Continuous.aestronglyMeasurable
      apply Continuous.smul _ φ.continuous
      unfold gaussian
      fun_prop)
    hFint hDcont.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      intro s hs
      by_cases hx : x ∈ tsupport φ
      · rw [Set.indicator_of_mem hx]
        exact hC (s,x) ⟨hs,hx⟩
      · rw [Set.indicator_of_notMem hx]
        simp [D, image_eq_zero_of_notMem_tsupport hx])
    hBoundInt
    (Eventually.of_forall fun x => by
      intro s hs
      have hspos : 0 < s := lt_of_lt_of_le (half_pos ht) hs.1
      exact (gaussian_hasDerivAt_time hspos x).smul_const (φ x))
  have hDeq : (∫ x, D t x) = ∫ x, gaussian t x • testLaplacian φ x := by
    rw [gaussian_smul_testLaplacian]
    congr 1
    ext x
    simp only [D, gaussian_rawLaplacian ht]
  exact hDeq ▸ hDiff.2


end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The positive-time heat equation in duality identifies the generator by
extending the scalar derivative to zero. Only primal Lp continuity is used. -/
lemma generator_weakLaplacian_of_positive_derivative
    (T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p))
    (hderiv : ∀ (f : ScalarLp 𝕜 d p) (φ : Test 𝕜 d) (t : ℝ), 0 < t →
      HasDerivAt (fun s : ℝ => testPairingCLM φ (T.operators s.toNNReal f))
        (testPairingCLM (testLaplacian φ) (T.operators t.toNNReal f)) t)
    (f g : ScalarLp 𝕜 d p)
    (hg : Semigroups.C0SemigroupSpec.hasGeneratorLimitValue T f g) :
    WeakLaplacian f g := by
  apply generator_weakLaplacian_of_tested_limit T f g hg
  intro φ
  let H : ℝ → 𝕜 := fun s => testPairingCLM φ (T.operators s.toNNReal f)
  have hlim : ContinuousWithinAt H (Set.Ioi 0) 0 := by
    change Tendsto H (𝓝[>] 0) (𝓝 (H 0))
    have heq : H 0 = testPairingCLM φ f := by simp [H, T.at_zero]
    rw [heq]
    exact ((testPairingCLM φ).continuous.tendsto f).comp (T.strong_zero f)
  have hdiff : DifferentiableOn ℝ H (Set.Ioi 0) := by
    intro t ht
    exact (hderiv f φ t ht).differentiableAt.differentiableWithinAt
  have hderlim : Tendsto (fun s => deriv H s) (𝓝[>] 0)
      (𝓝 (testPairingCLM (testLaplacian φ) f)) := by
    have hlim := ((testPairingCLM (testLaplacian φ)).continuous.tendsto f).comp (T.strong_zero f)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (hderiv f φ t ht).deriv.symm
  have hd := (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hlim self_mem_nhdsWithin hderlim).Ioi_of_Ici
  have hquot := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Set.Ioi 0)).mp hd
  simpa only [slope_fun_def, vsub_eq_sub, sub_zero, H, Real.toNNReal_zero, T.at_zero,
    ContinuousLinearMap.id_apply, testPairingCLM_apply, RCLike.real_smul_eq_coe_mul,
    map_inv₀, RCLike.algebraMap_eq_ofReal] using hquot

end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp
def realConvolution {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : Space d → ℝ) (f : Space d → 𝕜) (x : Space d) : 𝕜 :=
  ∫ y, k y • f (x-y)

lemma realConvolution_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : Space d → ℝ) (hk : Integrable k)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => k y • f (x-y))) ∧ MemLp (realConvolution k f) p volume := by
  have hkc : MemLp (fun x => (k x : 𝕜)) 1 volume :=
    (memLp_one_iff_integrable.mpr hk).ofReal
  obtain ⟨hi, _, hm, _⟩ := Distributions.young_l1_lp_endpoint p hp (fun x => (k x : 𝕜)) f hkc hf
  have heq : Distributions.ConvolutionEndpointBoundsSpec.ConvolutionValue (fun x => (k x : 𝕜)) f =
      realConvolution k f := by
    funext x
    simp only [Distributions.ConvolutionEndpointBoundsSpec.ConvolutionValue,
      realConvolution, RCLike.real_smul_eq_coe_mul]
  rw [heq] at hm
  exact ⟨by simpa only [RCLike.real_smul_eq_coe_mul] using hi, hm⟩

lemma realConvolution_reflection {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : Space d → ℝ) (hk : ∀ x, k (-x) = k x) (f : Space d → 𝕜) (x : Space d) :
    realConvolution k (fun z => f (-z)) (-x) = realConvolution k f x := by
  unfold realConvolution
  rw [← integral_neg_eq_self (μ := (volume : Measure (Space d)))]
  simp only [hk, neg_sub_neg, neg_sub]

lemma realConvolution_flip {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : Space d → ℝ) (f : Space d → 𝕜) (x : Space d) :
    realConvolution k f x = ∫ y, k (x-y) • f y := by
  change MeasureTheory.convolution k f (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
    MeasureTheory.convolution f k (ContinuousLinearMap.lsmul ℝ ℝ).flip volume x
  rw [MeasureTheory.convolution_flip]

lemma realConvolution_pairing {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (k : Space d → ℝ) (hk : Integrable k) (hkeven : ∀ x, k (-x) = k x)
    (f g : Space d → 𝕜) (hf : MemLp f p volume) (hg : MemLp g q volume) :
    (∫ x, realConvolution k f x * g x) = ∫ x, f x * realConvolution k g x := by
  let ψ : Space d → 𝕜 := fun x => g (-x)
  have hψ : MemLp ψ q volume := hg.comp_measurePreserving (volume.measurePreserving_neg)
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hq : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  obtain ⟨hgf, _⟩ := realConvolution_memLp hp k hk f hf
  obtain ⟨hgψ, hmψ⟩ := realConvolution_memLp hq (fun x => ‖k x‖) hk.norm _ hψ.norm
  let A := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
  let B := ContinuousLinearMap.mul ℝ 𝕜
  have hfg : ∀ᵐ x ∂volume, ConvolutionExistsAt f k x A.flip volume := by
    filter_upwards [hgf] with x hx
    exact (show ConvolutionExistsAt k f x A volume from hx).integrable_swap
  have hfgψ : ConvolutionExistsAt (fun x => ‖f x‖)
      (MeasureTheory.convolution (fun x => ‖k x‖) (fun x => ‖ψ x‖)
        (ContinuousLinearMap.mul ℝ ℝ) volume) 0 (ContinuousLinearMap.mul ℝ ℝ) volume := by
    exact ConvolutionExists.of_memLp_memLp _ hf.norm hmψ 0
  have hassoc := MeasureTheory.convolution_assoc A.flip B B A
    (f := f) (g := k) (k := ψ) (x₀ := (0 : Space d))
    (fun a b c => by simp [A, B, smul_eq_mul, RCLike.real_smul_eq_coe_mul, mul_assoc, mul_left_comm])
    hf.aestronglyMeasurable hk.aestronglyMeasurable
    hψ.aestronglyMeasurable hfg
    (by simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', smul_eq_mul] using hgψ)
    hfgψ
  have hconv : MeasureTheory.convolution f k A.flip volume = realConvolution k f := by
    rw [MeasureTheory.convolution_flip]
    rfl
  rw [hconv] at hassoc
  change (∫ x, realConvolution k f x * ψ (0-x)) =
    ∫ x, f x * realConvolution k ψ (0-x) at hassoc
  simpa only [zero_sub, ψ, neg_neg, realConvolution_reflection k hkeven] using hassoc

lemma gaussian_laplacian_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (rawLaplacian (gaussian (d := d) t)) := by
  have hi := ((gaussian_sum_sq_integrable (d := d) ht).div_const (4*t^2)).sub
    ((gaussian_integrable (d := d) ht).mul_const ((d:ℝ)/(2*t)))
  convert hi using 1
  ext x
  rw [gaussian_rawLaplacian ht]
  simp only [Pi.sub_apply]
  ring

lemma gaussian_laplacian_neg {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Space d) :
    rawLaplacian (gaussian t) (-x) = rawLaplacian (gaussian t) x := by
  simp only [gaussian_rawLaplacian ht, gaussian_neg, Pi.neg_apply, neg_sq]

lemma rawLaplacian_comp_sub {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Space d → 𝕜) (x y : Space d) :
    rawLaplacian (fun z => f (z-x)) y = rawLaplacian f (y-x) := by
  simp only [rawLaplacian, fderiv_comp_sub]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun z => (fun w => fderiv ℝ f w (Distributions.coordinateVector i)) (z-x)) y _ = _
  exact congrArg (fun L : Space d →L[ℝ] 𝕜 => L (Distributions.coordinateVector i))
    (fderiv_comp_sub (𝕜 := ℝ) (f := fun w => fderiv ℝ f w (Distributions.coordinateVector i)) (x := y) x)

lemma gaussian_laplacian_convolution_test {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {t : ℝ} (ht : 0 < t) (φ : Test 𝕜 d) (x : Space d) :
    realConvolution (rawLaplacian (gaussian t)) φ x = heatConvolution t (testLaplacian φ) x := by
  have hsym (y : Space d) : rawLaplacian (gaussian t) (x-y) = rawLaplacian (gaussian t) (y-x) := by
    rw [← gaussian_laplacian_neg ht, neg_sub]
  have hgsym (y : Space d) : gaussian t (x-y) = gaussian t (y-x) := by
    rw [← gaussian_neg t, neg_sub]
  rw [realConvolution_flip]
  simp_rw [hsym, ← rawLaplacian_comp_sub (gaussian t) x]
  have hi := integral_smul_testLaplacian (fun z : Space d => gaussian t (z-x)) (by
    unfold gaussian; fun_prop) φ
  rw [← hi]
  change _ = realConvolution (gaussian t) (testLaplacian φ) x
  rw [realConvolution_flip]
  simp_rw [hgsym]

lemma gaussian_laplacian_pairing {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {t : ℝ} (ht : 0 < t)
    (f : Space d → 𝕜) (hf : MemLp f p volume) (φ : Test 𝕜 d) :
    (∫ x, realConvolution (rawLaplacian (gaussian t)) f x * φ x) =
      ∫ x, heatConvolution t f x * testLaplacian φ x := by
  let q := (1-p⁻¹)⁻¹
  letI : ENNReal.HolderConjugate p q := ENNReal.HolderConjugate.inv_one_sub_inv' Fact.out
  have hφ : MemLp φ q volume := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hΔφ : MemLp (testLaplacian φ) q volume :=
    (testLaplacian φ).continuous.memLp_of_hasCompactSupport (testLaplacian φ).hasCompactSupport
  rw [realConvolution_pairing _ (gaussian_laplacian_integrable ht) (gaussian_laplacian_neg ht) f φ hf hφ]
  simp_rw [gaussian_laplacian_convolution_test ht φ]
  exact (heatConvolution_pairing ht f (testLaplacian φ) hf hΔφ).symm

lemma realKernelCLM_gaussian_laplacian_pairing {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {t : ℝ} (ht : 0 < t)
    (f : ScalarLp 𝕜 d p) (k : ScalarLp ℝ d 1)
    (hk : (k : Space d → ℝ) =ᵐ[volume] rawLaplacian (gaussian t)) (φ : Test 𝕜 d) :
    testPairingCLM φ (realKernelCLM f k) =
      testPairingCLM (testLaplacian φ) (heatOperatorPositive t ht f) := by
  have hconv (x : Space d) : (∫ y, k y • f (x-y)) =
      realConvolution (rawLaplacian (gaussian t)) f x := by
    apply integral_congr_ae
    filter_upwards [hk] with y hy
    rw [hy]
  rw [testPairingCLM_apply, testPairingCLM_apply]
  calc
    _ = ∫ x, realConvolution (rawLaplacian (gaussian t)) f x * φ x := by
      apply integral_congr_ae
      filter_upwards [realKernelCLM_representative f k] with x hx
      rw [hx, hconv]
    _ = ∫ x, heatConvolution t f x * testLaplacian φ x :=
      gaussian_laplacian_pairing ht f (Lp.memLp f) φ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [heatLpValue_representative t ht f] with x hx
      change _ = heatLpValue t ht f x * _
      rw [hx]


section
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma heatOperators_eq_realKernel {t : ℝ} (ht : 0 < t) (f : ScalarLp 𝕜 d p) :
    heatOperators t.toNNReal f = realKernelCLM f (gaussianL1 t) := by
  apply Lp.ext
  have hheat := heatOperators_representative t.toNNReal (Real.toNNReal_pos.mpr ht) f
  rw [Real.coe_toNNReal _ ht.le] at hheat
  have hker := realKernelCLM_representative f (gaussianL1 t)
  have hG := gaussianL1_representative (d := d) ht
  filter_upwards [hheat, hker] with x hx hk
  rw [hx, hk]
  unfold heatConvolution
  apply integral_congr_ae
  filter_upwards [hG] with y hy
  rw [hy]

lemma heatOperators_hasDerivAt {t : ℝ} (ht : 0 < t) (f : ScalarLp 𝕜 d p) :
    HasDerivAt (fun s : ℝ => heatOperators s.toNNReal f)
      (realKernelCLM f ((gaussian_time_derivative_integrable (d := d) ht).toL1
        (fun x : Space d => gaussian t x *
          ((∑ i, (x i)^2)/(4*t^2) - (d:ℝ)/(2*t))))) t := by
  have hd := (realKernelCLM f).hasFDerivAt.comp_hasDerivAt t (gaussianL1_hasDerivAt ht)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact heatOperators_eq_realKernel hs f

end

end ExpandedFA.Models.HeatLp

namespace ExpandedFA.Models.HeatLp
section FinalAssembly
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma heatOperators_test_hasDerivAt {t : ℝ} (ht : 0 < t)
    (f : ScalarLp 𝕜 d p) (φ : Test 𝕜 d) :
    HasDerivAt (fun s : ℝ => testPairingCLM φ (heatOperators s.toNNReal f))
      (testPairingCLM (testLaplacian φ) (heatOperators t.toNNReal f)) t := by
  let k : ScalarLp ℝ d 1 := (gaussian_time_derivative_integrable (d := d) ht).toL1
    (fun x : Space d => gaussian t x * ((∑ i, (x i)^2)/(4*t^2) - (d:ℝ)/(2*t)))
  have hrep : realKernelCLM f k =ᵐ[volume]
      realConvolution (rawLaplacian (gaussian t)) f := by
    have hk : (k : Space d → ℝ) =ᵐ[volume] rawLaplacian (gaussian t) := by
      filter_upwards [Integrable.coeFn_toL1
        (gaussian_time_derivative_integrable (d := d) ht)] with x hx
      simpa only [gaussian_rawLaplacian ht] using hx
    have heq : (fun x => ∫ y, k y • f (x-y)) =
        realConvolution (rawLaplacian (gaussian t)) f := by
      funext x
      apply integral_congr_ae
      filter_upwards [hk] with y hy
      rw [hy]
    exact (realKernelCLM_representative f k).trans (Eventually.of_forall (congrFun heq))
  have hheat := heatOperators_representative t.toNNReal (Real.toNNReal_pos.mpr ht) f
  rw [Real.coe_toNNReal t ht.le] at hheat
  have hpair : testPairingCLM φ (realKernelCLM f k) =
      testPairingCLM (testLaplacian φ) (heatOperators t.toNNReal f) := by
    rw [testPairingCLM_apply, testPairingCLM_apply]
    calc
      _ = ∫ x, realConvolution (rawLaplacian (gaussian t)) f x * φ x :=
        integral_congr_ae (hrep.mul (EventuallyEq.refl _ _))
      _ = ∫ x, heatConvolution t f x * testLaplacian φ x :=
        gaussian_laplacian_pairing ht f (Lp.memLp f) φ
      _ = _ := integral_congr_ae (hheat.symm.mul (EventuallyEq.refl _ _))
  have hd := ((testPairingCLM (p := p) φ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (heatOperators_hasDerivAt ht f)
  change HasDerivAt (fun s : ℝ => testPairingCLM φ (heatOperators s.toNNReal f))
    (testPairingCLM φ (realKernelCLM f k)) t at hd
  rwa [hpair] at hd

lemma heatSemigroup_operators_eq
    (T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p)) (hheat : IsHeatSemigroup T)
    (t : ℝ≥0) : T.operators t = heatOperators t := by
  by_cases ht : 0 < t
  · apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hheat t ht f).trans (heatOperators_representative t ht f).symm
  · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) (show 0 ≤ t from zero_le)
    rw [ht0, T.at_zero, heatOperators_zero]

end FinalAssembly

theorem generator_distribution_inclusion : Spec.GeneratorDistributionInclusion := by
  intro 𝕜 _ d p _ _ T hheat f g hg
  apply generator_weakLaplacian_of_positive_derivative T ?_ f g hg
  intro u φ t ht
  simpa only [heatSemigroup_operators_eq T hheat] using heatOperators_test_hasDerivAt ht u φ

/-- The exact maximal distributional generator domain of the Gaussian heat
semigroup on every finite Lp, with real or complex scalars. -/
theorem heat_lp_maximal_domain : Spec.HeatLpResult :=
  heat_lp_of_analytic_inputs heat_semigroup_existence generator_distribution_inclusion
    elliptic_uniqueness

end ExpandedFA.Models.HeatLp
