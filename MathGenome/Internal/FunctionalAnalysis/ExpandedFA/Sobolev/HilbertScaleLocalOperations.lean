import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.DistributionPaleyWiener
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Complex.OperatorNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace ExpandedFA.Sobolev.LocalOperations
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

lemma wordDerivative_eq {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d) :
    wordDerivative w T = temperedWordDerivative w T := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih => exact ih _

/-- The derivative in Fourier coordinates, at arbitrary real order. -/
def derivativeMap {d : ℕ} (s : ℝ) (α : Fin d → ℕ) :
    Hs d s →L[ℂ] Hs d (s - (∑ i, α i : ℕ)) :=
  ((coordinates d (s - (∑ i, α i : ℕ))).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((multiplierL2CLM
      (fun ξ => derivativeSymbol α ξ * complexWeight (-(∑ i, α i : ℕ)) ξ)
      ((derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _))
      (derivativeSymbol_weight_norm_le α (le_refl _))).comp
      (coordinates d s).toContinuousLinearEquiv.toContinuousLinearMap)

lemma derivativeMap_norm_le {d : ℕ} (s : ℝ) (α : Fin d → ℕ) (u : Hs d s) :
    ‖derivativeMap s α u‖ ≤ ‖u‖ := by
  change ‖(coordinates d (s - (∑ i, α i : ℕ))).symm
    (multiplierL2
      (fun ξ => derivativeSymbol α ξ * complexWeight (-(∑ i, α i : ℕ)) ξ)
      ((derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _))
      (derivativeSymbol_weight_norm_le α (le_refl _)) (coordinates d s u))‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map, ← (coordinates d s).norm_map u]
  simpa only [one_mul] using multiplierL2_norm_le _ _
    (derivativeSymbol_weight_norm_le α (le_refl _)) (coordinates d s u)

lemma derivativeMap_realization {d : ℕ} (s : ℝ) (α : Fin d → ℕ) (u : Hs d s) :
    realization (derivativeMap s α u) = multiDerivative α (realization u) := by
  let m : ℕ := ∑ i, α i
  let g : Euclidean d → ℂ := fun ξ => derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ
  have hg : g.HasTemperateGrowth :=
    (derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _)
  have hC : ∀ ξ, ‖g ξ‖ ≤ 1 := derivativeSymbol_weight_norm_le α (le_refl _)
  rw [multiDerivative, wordDerivative_eq, temperedMultiIndexDerivative_eq_multiplier]
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective
  change temperedFourier (realization (derivativeMap s α u)) =
    𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (derivativeSymbol α)
      (temperedFourier (realization u))))
  rw [FourierTransform.fourier_fourierInv_eq, fourier_realization, fourier_realization]
  change TemperedDistribution.smulLeftCLM ℂ (complexWeight (-(s - (m : ℝ))))
    (Lp.toTemperedDistribution (multiplierL2CLM g hg hC (coordinates d s u))) = _
  rw [multiplierL2_distribution,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg (complexWeight_hasTemperateGrowth _),
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (complexWeight_hasTemperateGrowth _) (derivativeSymbol_hasTemperateGrowth α)]
  congr 2
  funext ξ
  change (derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ) *
    complexWeight (-(s - (m : ℝ))) ξ = complexWeight (-s) ξ * derivativeSymbol α ξ
  have hw := congrFun (complexWeight_add (d := d) (-(m : ℝ)) (-(s - (m : ℝ)))) ξ
  have he : -(m : ℝ) + -(s - (m : ℝ)) = -s := by ring
  rw [he] at hw
  simpa only [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun z : ℂ => derivativeSymbol α ξ * z) hw.symm

theorem derivatives : Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.derivativesType := by
  intro d s α
  exact ⟨derivativeMap s α, fun u =>
    ⟨derivativeMap_realization s α u, derivativeMap_norm_le s α u⟩⟩

/-- A coarse comparison sufficient for integrability at a sufficiently negative order. -/
lemma norm_le_frequencyWeight {d : ℕ} (ξ : Euclidean d) :
    1 + ‖ξ‖ ≤ 2 * frequencyWeight ξ := by
  unfold frequencyWeight
  have hp := Real.pi_gt_three
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hπ (sq_nonneg ‖ξ‖)
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

lemma weight_neg_even {d : ℕ} (n : ℕ) (ξ : Euclidean d) :
    weight (-(2 * (n : ℝ))) ξ = (frequencyWeight ξ ^ n)⁻¹ := by
  unfold weight
  rw [show -(2 * (n : ℝ)) / 2 = -(n : ℝ) by ring,
    Real.rpow_neg (frequencyWeight_pos ξ).le, Real.rpow_natCast]

/-- Any continuous polynomially bounded Fourier density has some negative
Sobolev order. This uses a genuine L² integrability bound. -/
lemma polynomial_density_memLp {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f)
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ ξ, ‖f ξ‖ ≤ C * (1 + ‖ξ‖) ^ M) :
    ∃ N : ℕ, MemLp (fun ξ => complexWeight (-(N : ℝ)) ξ * f ξ) 2 volume := by
  obtain ⟨Q, hQ⟩ := (inferInstance : (volume : Measure (Euclidean d)).HasTemperateGrowth).exists_eLpNorm_lt_top 2
  have hmem : MemLp (fun ξ : Euclidean d => (1 + ‖ξ‖) ^ (-(Q : ℝ))) 2 volume := hQ
  refine ⟨2 * (M + Q), hmem.of_le_mul ?_ (c := C * 2 ^ (M + Q)) ?_⟩
  · exact ((complexWeight_hasTemperateGrowth _).1.continuous.mul hf).aestronglyMeasurable
  · filter_upwards [] with ξ
    have hp : 0 < 1 + ‖ξ‖ := by positivity
    have hw : 0 < frequencyWeight ξ := frequencyWeight_pos ξ
    have hbpow : (1 + ‖ξ‖) ^ (M + Q) ≤ 2 ^ (M + Q) * frequencyWeight ξ ^ (M + Q) := by
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖ξ‖)
        (norm_le_frequencyWeight ξ) (M + Q)
    have hratio : (frequencyWeight ξ ^ (M + Q))⁻¹ * (1 + ‖ξ‖) ^ M ≤
        2 ^ (M + Q) * ((1 + ‖ξ‖) ^ Q)⁻¹ := by
      rw [inv_mul_eq_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      simpa only [← pow_add] using hbpow
    rw [Real.rpow_neg hp.le, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    rw [norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (weight_pos _ _)]
    have hcast : -(↑(2 * (M + Q)) : ℝ) = -(2 * ((M + Q : ℕ) : ℝ)) := by push_cast; rfl
    rw [hcast, weight_neg_even]
    calc
      _ ≤ (frequencyWeight ξ ^ (M + Q))⁻¹ * (C * (1 + ‖ξ‖) ^ M) :=
        mul_le_mul_of_nonneg_left (hb ξ) (by positivity)
      _ = C * ((frequencyWeight ξ ^ (M + Q))⁻¹ * (1 + ‖ξ‖) ^ M) := by ring
      _ ≤ C * (2 ^ (M + Q) * ((1 + ‖ξ‖) ^ Q)⁻¹) := mul_le_mul_of_nonneg_left hratio hC
      _ = _ := by ring

open ExpandedFA.Distributions ExpandedFA.Fourier.PaleyWiener
open ExpandedFA.Fourier.DistributionPaleyWiener

lemma supportFunction_at_zero {d : ℕ} (K : Set (Euclidean d)) : supportFunction K 0 = 0 := by
  by_cases h : K.Nonempty
  · exact supportFunction_zero h
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    simp [supportFunction]

/-- Polynomial growth of the real Fourier transform of the actual compact
LF distribution. This also covers empty support. -/
lemma compact_transform_polynomial_bound {d : ℕ} (T : Distribution d) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ ξ : Euclidean d,
      ‖DistributionPaleyWiener.fourierLaplace T (realFrequency ξ)‖ ≤ C * (1 + ‖ξ‖) ^ M := by
  obtain ⟨Q, M, C, hC, hb⟩ := smooth_functional_laplace_growth (smoothExtension T)
  refine ⟨M, C, hC, fun ξ => ?_⟩
  simpa only [DistributionPaleyWiener.fourierLaplace, imaginaryPart_realFrequency, supportFunction_at_zero, mul_zero,
    Real.exp_zero, mul_one, norm_realFrequency] using hb (realFrequency ξ)

theorem compact_support : Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.compactSupportType := by
  intro d T hT
  have hc : IsCompact (euclideanSupport T) :=
    hT.image (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
  obtain ⟨U, hU, hFourier⟩ := compact_distribution_tempered_representation T hc
  let f : Euclidean d → ℂ := fun ξ => DistributionPaleyWiener.fourierLaplace T (realFrequency ξ)
  have hf : Continuous f := (entire d T hc).continuous.comp (continuous_realFrequency d)
  obtain ⟨M, C, hC, hb⟩ := compact_transform_polynomial_bound T
  obtain ⟨N, hN⟩ := polynomial_density_memLp f hf M C hC hb
  have hdensity : HasFourierDensity U f := by
    refine ⟨hf.locallyIntegrable, fun φ => ?_⟩
    simpa only [mul_comm] using hFourier φ
  obtain ⟨u, hu⟩ := (realization_image d (-(N : ℝ)) U).mpr ⟨f, hdensity, hN⟩
  exact ⟨N, u, fun φ => by rw [hu, ← hU]⟩

/-- A single square-integrable envelope controls all Fourier moments up to k. -/
def momentEnvelope {d : ℕ} (k : ℕ) (s : ℝ) (ξ : Euclidean d) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (((k : ℝ) - s) / 2)

lemma momentEnvelope_memLp {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) :
    MemLp (momentEnvelope (d := d) k s) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by
    exact ((Function.hasTemperateGrowth_one_add_norm_sq_rpow
      (Euclidean d) (((k : ℝ) - s) / 2)).1.continuous.aestronglyMeasurable))).mpr
  have hd : (Module.finrank ℝ (Euclidean d) : ℝ) < 2 * (s - k) := by
    simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin]
    linarith
  convert (integrable_rpow_neg_one_add_norm_sq (μ := volume) hd) using 1
  ext ξ
  unfold momentEnvelope
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

lemma norm_pow_mul_weight_le_envelope {d k j : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hj : j ≤ k) (ξ : Euclidean d) :
    ‖ξ‖ ^ j * weight (-s) ξ ≤ momentEnvelope k s ξ := by
  have hb : 1 ≤ 1 + ‖ξ‖ ^ 2 := by linarith [sq_nonneg ‖ξ‖]
  have hfreq : 1 + ‖ξ‖ ^ 2 ≤ frequencyWeight ξ := by
    unfold frequencyWeight
    have hp := Real.pi_gt_three
    have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hπ (sq_nonneg ‖ξ‖)
    linarith
  have hw : weight (-s) ξ ≤ (1 + ‖ξ‖ ^ 2) ^ (-s / 2) := by
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hfreq (by linarith)
  have hn : ‖ξ‖ ^ j ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
    calc
      ‖ξ‖ ^ j = (‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast (‖ξ‖) 2, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hb (by gcongr)
  calc
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) :=
      mul_le_mul hn hw (weight_pos _ _).le (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      unfold momentEnvelope
      congr 1
      ring

lemma fourier_moment_bound {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) (j : ℕ) (hj : j ≤ k)
    (ξ : Euclidean d) :
    ‖ξ‖ ^ j * ‖fourierDensity u ξ‖ ≤
      momentEnvelope k s ξ * ‖coordinates d s u ξ‖ := by
  rw [fourierDensity, norm_mul, complexWeight, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (weight_pos _ _), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (norm_pow_mul_weight_le_envelope (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hj ξ) (norm_nonneg _)

lemma fourier_moments_integrable {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) (j : ℕ) (hj : j ≤ k) :
    Integrable (fun ξ => ‖ξ‖ ^ j * ‖fourierDensity u ξ‖) volume := by
  have h := (momentEnvelope_memLp hs).integrable_mul (Lp.memLp (coordinates d s u)).norm
  apply h.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_norm.pow j).aestronglyMeasurable.mul
      (((complexWeight_hasTemperateGrowth (-s)).1.continuous.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable _)).norm))
  · rw [Real.norm_of_nonneg (by positivity)]
    exact fourier_moment_bound hs u j hj ξ

/-- The constant in the moment estimate depends only on d, k and s. -/
def momentConstant {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) : ℝ :=
  ‖(momentEnvelope_memLp hs).toLp (momentEnvelope (d := d) k s)‖

lemma fourier_moments_norm_le {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) (j : ℕ) (hj : j ≤ k) :
    (∫ ξ, ‖ξ‖ ^ j * ‖fourierDensity u ξ‖) ≤ momentConstant hs * ‖u‖ := by
  let a := (momentEnvelope_memLp hs).toLp (momentEnvelope (d := d) k s)
  let hb := (Lp.memLp (coordinates d s u)).norm
  let b := hb.toLp (fun ξ => ‖coordinates d s u ξ‖)
  have hnorm : ‖b‖ = ‖u‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable _)]
    exact ((coordinates d s).norm_map u).symm ▸ (Lp.norm_def _).symm
  have heq : (∫ ξ, momentEnvelope k s ξ * ‖coordinates d s u ξ‖) = inner ℝ a b := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(momentEnvelope_memLp hs).coeFn_toLp, hb.coeFn_toLp] with ξ h₁ h₂
    simp only [a, b, h₁, h₂, RCLike.inner_apply, conj_trivial, mul_comm]
  calc
    _ ≤ ∫ ξ, momentEnvelope k s ξ * ‖coordinates d s u ξ‖ :=
      integral_mono (fourier_moments_integrable hs u j hj)
        ((momentEnvelope_memLp hs).integrable_mul hb) (fourier_moment_bound hs u j hj)
    _ = inner ℝ a b := heq
    _ ≤ ‖a‖ * ‖b‖ := real_inner_le_norm _ _
    _ = _ := by rw [hnorm]; rfl

lemma fourierDensity_integrable {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) :
    Integrable (fourierDensity u) volume := by
  have hmeas : AEStronglyMeasurable (fourierDensity u) volume :=
    (complexWeight_hasTemperateGrowth (-s)).1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (coordinates d s u))
  apply (integrable_norm_iff hmeas).mp
  simpa only [pow_zero, one_mul] using fourier_moments_integrable hs u 0 (Nat.zero_le _)

/-- The inverse Fourier integral is an actual representative, not an abstract
isomorphism of the underlying Hilbert spaces. -/
def continuousRepresentative {d : ℕ} {s : ℝ} (u : Hs d s) : Euclidean d → ℂ :=
  𝓕⁻ (fourierDensity u)

lemma representative_contDiff {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) :
    ContDiff ℝ k (continuousRepresentative u) := by
  exact VectorFourier.contDiff_fourierIntegral (-innerSL ℝ)
    (fun j hj => fourier_moments_integrable hs u j (by exact_mod_cast hj))

lemma representative_derivative_norm_le {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) (j : ℕ) (hj : j ≤ k)
    (x : Euclidean d) :
    ‖iteratedFDeriv ℝ j (continuousRepresentative u) x‖ ≤
      (1 + 2 * Real.pi * ‖(-innerSL ℝ : Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℝ)‖) ^ k *
        momentConstant hs * ‖u‖ := by
  let L : Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℝ := -innerSL ℝ
  have hm : ∀ n : ℕ, (n : ℕ∞) ≤ k →
      Integrable (fun ξ => ‖ξ‖ ^ n * ‖fourierDensity u ξ‖) :=
    fun n hn => fourier_moments_integrable hs u n (by exact_mod_cast hn)
  have hmeas := (fourierDensity_integrable hs u).aestronglyMeasurable
  change ‖iteratedFDeriv ℝ j (VectorFourier.fourierIntegral Real.fourierChar volume
    L.toLinearMap₁₂ (fourierDensity u)) x‖ ≤ _
  rw [VectorFourier.iteratedFDeriv_fourierIntegral L hm hmeas (by exact_mod_cast hj)]
  have hint : Integrable (fun ξ => (2 * Real.pi * ‖L‖) ^ j *
      (‖ξ‖ ^ j * ‖fourierDensity u ξ‖)) :=
    (fourier_moments_integrable hs u j hj).const_mul _
  calc
    _ ≤ ∫ ξ, ‖VectorFourier.fourierPowSMulRight L (fourierDensity u) ξ j‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ, (2 * Real.pi * ‖L‖) ^ j * (‖ξ‖ ^ j * ‖fourierDensity u ξ‖) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
      exact Filter.Eventually.of_forall fun ξ => by
        simpa only [mul_assoc] using
          VectorFourier.norm_fourierPowSMulRight_le L (fourierDensity u) ξ j
    _ = (2 * Real.pi * ‖L‖) ^ j * ∫ ξ, ‖ξ‖ ^ j * ‖fourierDensity u ξ‖ := integral_const_mul _ _
    _ ≤ (2 * Real.pi * ‖L‖) ^ j * (momentConstant hs * ‖u‖) :=
      mul_le_mul_of_nonneg_left (fourier_moments_norm_le hs u j hj) (by positivity)
    _ ≤ (1 + 2 * Real.pi * ‖L‖) ^ k * (momentConstant hs * ‖u‖) := by
      apply mul_le_mul_of_nonneg_right _ (by unfold momentConstant; positivity)
      exact (pow_le_pow_left₀ (by positivity) (by linarith :
        2 * Real.pi * ‖L‖ ≤ 1 + 2 * Real.pi * ‖L‖) j).trans
        (pow_le_pow_right₀ (by linarith [show 0 ≤ 2 * Real.pi * ‖L‖ from by positivity] : 1 ≤ 1 + 2 * Real.pi * ‖L‖) hj)
    _ = _ := by dsimp only [L]; ring

lemma integral_inverse_fourier_pair {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Integrable f) (φ : Schwartz ℂ d) :
    (∫ x, (𝓕⁻ f) x * φ x) = ∫ ξ, f ξ * (𝓕⁻ φ) ξ := by
  have hflip : (-innerₗ (Euclidean d)).flip = -innerₗ (Euclidean d) := by
    ext v w
    change -inner ℝ w v = -inner ℝ v w
    rw [real_inner_comm]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := -innerₗ (Euclidean d)) (ν := volume)
    Real.continuous_fourierChar continuous_inner.neg hf φ.integrable
  rw [hflip] at h
  simpa only [SchwartzMap.fourierInv_coe, ContinuousLinearMap.mul_apply'] using! h


lemma representative_pairing {d k : ℕ} {s : ℝ}
    (hs : (k : ℝ) + (d : ℝ) / 2 < s) (u : Hs d s) (φ : Schwartz ℂ d) :
    Integrable (fun x => φ x * continuousRepresentative u x) ∧
      realization u φ = ∫ x, φ x * continuousRepresentative u x := by
  have hi := fourierDensity_integrable hs u
  constructor
  · have hb : ∀ x, ‖continuousRepresentative u x‖ ≤ ∫ ξ, ‖fourierDensity u ξ‖ :=
      fun x => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    apply (φ.integrable.norm.mul_const (∫ ξ, ‖fourierDensity u ξ‖)).mono'
    · exact φ.continuous.aestronglyMeasurable.mul
        (representative_contDiff hs u).continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  · calc
      realization u φ = ∫ ξ, (𝓕⁻ φ) ξ * fourierDensity u ξ := by
        change (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
          (Lp.toTemperedDistribution (coordinates d s u)))) φ = _
        rw [TemperedDistribution.fourierInv_apply]
        exact (weighted_regular_pair (-s) (coordinates d s u) (𝓕⁻ φ)).2
      _ = ∫ x, (𝓕⁻ (fourierDensity u)) x * φ x := by
        simpa only [mul_comm] using (integral_inverse_fourier_pair _ hi φ).symm
      _ = _ := by simp only [continuousRepresentative, mul_comm]

theorem embedding : Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.embeddingType := by
  intro d k s hs
  let C := (1 + 2 * Real.pi * ‖(-innerSL ℝ : Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℝ)‖) ^ k *
    momentConstant hs
  refine ⟨C, by dsimp [C, momentConstant]; positivity, fun u =>
    ⟨continuousRepresentative u, representative_contDiff hs u,
      representative_pairing hs u, fun j hj x => ?_⟩⟩
  exact representative_derivative_norm_le hs u j hj x

lemma frequencyWeight_add_le {d : ℕ} (x y : Euclidean d) :
    frequencyWeight (x + y) ≤ 2 * frequencyWeight x * frequencyWeight y := by
  have hn : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [norm_add_le x y, sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x + y)]
  have hscale := mul_le_mul_of_nonneg_left hn (show 0 ≤ 4 * Real.pi ^ 2 by positivity)
  unfold frequencyWeight
  have hp : 0 ≤ (4 * Real.pi ^ 2) ^ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by positivity
  nlinarith

lemma weight_peetre_nonneg {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (x y : Euclidean d) :
    weight s (x + y) * weight (-s) y ≤ (2 : ℝ) ^ (s / 2) * weight s x := by
  have hb := Real.rpow_le_rpow (frequencyWeight_pos (x+y)).le
    (frequencyWeight_add_le x y) (show 0 ≤ s / 2 by linarith)
  rw [Real.mul_rpow (mul_nonneg (by norm_num) (frequencyWeight_pos x).le) (frequencyWeight_pos y).le,
    Real.mul_rpow (by positivity) (frequencyWeight_pos x).le] at hb
  calc
    _ ≤ ((2 : ℝ) ^ (s / 2) * weight s x * weight s y) * weight (-s) y :=
      mul_le_mul_of_nonneg_right hb (weight_pos _ _).le
    _ = _ := by rw [mul_assoc, mul_assoc, mul_comm (weight s y), weight_neg_mul, mul_one]

lemma weight_peetre {d : ℕ} (s : ℝ) (ξ η : Euclidean d) :
    weight s ξ * weight (-s) (ξ - η) ≤
      (2 : ℝ) ^ (|s| / 2) * weight |s| η := by
  by_cases hs : 0 ≤ s
  · simpa only [abs_of_nonneg hs, add_sub_cancel] using weight_peetre_nonneg hs η (ξ-η)
  · have hn : 0 ≤ -s := by linarith
    have h := weight_peetre_nonneg hn (-η) ξ
    simpa only [abs_of_neg (lt_of_not_ge hs), neg_neg, weight, frequencyWeight, norm_neg,
      neg_add_eq_sub, mul_comm] using h

/-- Schwartz Fourier coordinates of multiplication by a fixed smooth coefficient. -/
def schwartzMultiplication {d : ℕ} (s : ℝ) (a : Schwartz ℂ d) :
    Schwartz ℂ d →L[ℂ] Schwartz ℂ d :=
  (SchwartzMap.smulLeftCLM ℂ (complexWeight s)).comp
    ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 a)).comp
      (SchwartzMap.smulLeftCLM ℂ (complexWeight (-s))))

def multiplicationKernel {d : ℕ} (s : ℝ) (a : Schwartz ℂ d) : Schwartz ℂ d :=
  SchwartzMap.smulLeftCLM ℂ (complexWeight |s|) (𝓕 a)

lemma multiplication_integrand_norm {d : ℕ} (s : ℝ) (a g : Schwartz ℂ d)
    (ξ η : Euclidean d) :
    ‖complexWeight s ξ * ((𝓕 a) η * (complexWeight (-s) (ξ-η) * g (ξ-η)))‖ ≤
      ((2 : ℝ) ^ (|s| / 2) * ‖multiplicationKernel s a η‖) * ‖g (ξ-η)‖ := by
  simp only [norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
    multiplicationKernel,
    SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth |s|),
    smul_eq_mul, norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos _ _)]
  nlinarith [mul_le_mul_of_nonneg_right (weight_peetre s ξ η)
    (mul_nonneg (norm_nonneg ((𝓕 a) η)) (norm_nonneg (g (ξ-η))))]

set_option maxHeartbeats 1600000 in
lemma schwartzMultiplication_norm_le {d : ℕ} (s : ℝ) (a g : Schwartz ℂ d) :
    ‖(schwartzMultiplication s a g).toLp 2‖ ≤
      ((2 : ℝ) ^ (|s| / 2) * ‖(multiplicationKernel s a).toLp 1‖) * ‖g.toLp 2‖ := by
  let K := multiplicationKernel s a
  let C : ℝ := (2 : ℝ) ^ (|s| / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let F : Euclidean d × Euclidean d → ℂ := fun z =>
    complexWeight s z.1 * ((𝓕 a) z.2 * (complexWeight (-s) (z.1-z.2) * g (z.1-z.2)))
  have hFm : Measurable F := by
    apply Continuous.measurable
    exact ((complexWeight_hasTemperateGrowth s).1.continuous.comp continuous_fst).mul
      (((𝓕 a).continuous.comp continuous_snd).mul
        (((complexWeight_hasTemperateGrowth (-s)).1.continuous.comp (continuous_fst.sub continuous_snd)).mul
          (g.continuous.comp (continuous_fst.sub continuous_snd))))
  have hb (η : Euclidean d) : eLpNorm (fun ξ => F (ξ,η)) 2 volume ≤
      ENNReal.ofReal C * ‖K η‖ₑ * eLpNorm g 2 volume := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
      ((hFm.comp measurable_prodMk_right).aestronglyMeasurable)
      (Filter.Eventually.of_forall (multiplication_integrand_norm s a g · η)) 2
    have htrans : eLpNorm (fun x => g (x-η)) 2 volume = eLpNorm g 2 volume := by
      exact eLpNorm_comp_measurePreserving g.continuous.aestronglyMeasurable
        (measurePreserving_sub_right volume η)
    rw [htrans] at h
    change eLpNorm (fun ξ => F (ξ,η)) 2 volume ≤
      ENNReal.ofReal (C * ‖K η‖) * eLpNorm g 2 volume at h
    rw [ENNReal.ofReal_mul hC, ofReal_norm] at h
    exact h
  have hR : (∫⁻ η, eLpNorm (fun ξ => F (ξ,η)) 2 volume) ≤
      ENNReal.ofReal C * eLpNorm K 1 volume * eLpNorm g 2 volume := by
    refine (lintegral_mono hb).trans_eq ?_
    rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [← eLpNorm_one_eq_lintegral_enorm K.continuous.aestronglyMeasurable]
  obtain ⟨_, hbound⟩ := minkowski_integral_eLpNorm volume volume 2 (by norm_num) (by norm_num) F hFm
    (hR.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top)
      (K.memLp 1).eLpNorm_lt_top) (g.memLp 2).eLpNorm_lt_top))
  have heq : (fun ξ => ∫ η, F (ξ,η)) = ⇑(schwartzMultiplication s a g) := by
    ext ξ
    simp only [schwartzMultiplication, ContinuousLinearMap.comp_apply,
      SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth s), smul_eq_mul,
      SchwartzMap.convolution_apply, MeasureTheory.convolution,
      ContinuousLinearMap.mul_apply', F]
    rw [← integral_const_mul]
    congr 1
    ext η
    rw [SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth (-s)), smul_eq_mul]
  rw [heq] at hbound
  have h := ENNReal.toReal_mono (ne_of_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (K.memLp 1).eLpNorm_lt_top)
    (g.memLp 2).eLpNorm_lt_top)) (hbound.trans hR)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ← SchwartzMap.norm_toLp] using h

/-- The realization, with the native pointwise topology on tempered distributions. -/
def realizationCLM (d : ℕ) (s : ℝ) :
    Hs d s →L[ℂ] TemperedDistribution (Euclidean d) ℂ :=
  (FourierTransform.fourierInvCLM ℂ (TemperedDistribution (Euclidean d) ℂ)).comp
    ((TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))).comp
      ((Lp.toTemperedDistributionCLM ℂ volume 2).comp
        (coordinates d s).toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] lemma realizationCLM_apply {d : ℕ} {s : ℝ} (u : Hs d s) :
    realizationCLM d s u = (realization u : TemperedDistribution (Euclidean d) ℂ) := rfl

lemma realization_schwartz_coordinates {d : ℕ} (s : ℝ) (g : Schwartz ℂ d) :
    realization (s := s) ((coordinates d s).symm (g.toLp 2)) =
      schwartzRegularDistribution (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (complexWeight (-s)) g)) := by
  let f : Schwartz ℂ d := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (complexWeight (-s)) g)
  obtain ⟨u, hu⟩ := schwartz_inclusion d s f
  have hcoord := coordinates_of_schwartz u f hu
  have hcancel : SchwartzMap.smulLeftCLM ℂ (complexWeight s) (schwartzFourier f) = g := by
    change SchwartzMap.smulLeftCLM ℂ (complexWeight s)
      (𝓕 (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (complexWeight (-s)) g))) = g
    rw [FourierTransform.fourier_fourierInv_eq]
    ext ξ
    simp only [SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth s),
      SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth (-s)), smul_eq_mul,
      complexWeight, ← mul_assoc, ← Complex.ofReal_mul, mul_comm (weight s ξ), weight_neg_mul,
      Complex.ofReal_one, one_mul]
  rw [hcancel] at hcoord
  have heq : u = (coordinates d s).symm (g.toLp 2) := by
    apply (coordinates d s).injective
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hcoord
  rw [← heq]
  exact hu

lemma inverse_fourier_convolution {d : ℕ} (f g : Schwartz ℂ d) :
    𝓕⁻ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ f) (𝓕⁻ g) := by
  ext x
  change (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g)) (-x) = _
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    SchwartzMap.pairing_apply_apply]
  rfl

lemma schwartzMultiplication_realization {d : ℕ} (s : ℝ) (a g : Schwartz ℂ d) :
    realization (s := s) ((coordinates d s).symm ((schwartzMultiplication s a g).toLp 2)) =
      TemperedDistribution.smulLeftCLM ℂ (⇑a)
        (realization (s := s) ((coordinates d s).symm (g.toLp 2))) := by
  rw [realization_schwartz_coordinates, realization_schwartz_coordinates]
  have hw (f : Schwartz ℂ d) : SchwartzMap.smulLeftCLM ℂ (complexWeight (-s))
      (SchwartzMap.smulLeftCLM ℂ (complexWeight s) f) = f := by
    ext ξ
    simp only [SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth s),
      SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth (-s)), smul_eq_mul,
      complexWeight, ← mul_assoc, ← Complex.ofReal_mul, weight_neg_mul, Complex.ofReal_one, one_mul]
  change schwartzRegularDistribution (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (complexWeight (-s))
    (SchwartzMap.smulLeftCLM ℂ (complexWeight s)
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 a)
        (SchwartzMap.smulLeftCLM ℂ (complexWeight (-s)) g))))) = _
  rw [hw, inverse_fourier_convolution, FourierTransform.fourierInv_fourier_eq]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    Inversion.regular_distribution_pairing, Inversion.regular_distribution_pairing]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply',
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop : (⇑a).HasTemperateGrowth), smul_eq_mul]
  ring

def multiplicationCoordinates {d : ℕ} (s : ℝ) (a : Schwartz ℂ d) : L2 d →L[ℂ] L2 d :=
  (((SchwartzMap.toLpCLM ℂ ℂ 2).comp (schwartzMultiplication s a)).toLinearMap).extendOfNorm
    (SchwartzMap.toLpCLM ℂ ℂ 2).toLinearMap

lemma multiplicationCoordinates_schwartz {d : ℕ} (s : ℝ) (a g : Schwartz ℂ d) :
    multiplicationCoordinates s a (g.toLp 2) = (schwartzMultiplication s a g).toLp 2 := by
  let e : Schwartz ℂ d →ₗ[ℂ] L2 d := (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
  let f : Schwartz ℂ d →ₗ[ℂ] L2 d :=
    ((SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp (schwartzMultiplication s a)).toLinearMap
  have hdense : DenseRange e := by
    change DenseRange (fun g : Schwartz ℂ d => g.toLp 2)
    exact SchwartzMap.denseRange_toLpCLM (p := 2) (μ := volume) (by norm_num)
  change f.extendOfNorm e (e g) = f g
  apply LinearMap.extendOfNorm_eq (f := f) (e := e) hdense
  exact ⟨_, schwartzMultiplication_norm_le (d := d) s a⟩


def multiplicationMap {d : ℕ} (s : ℝ) (a : Schwartz ℂ d) : Hs d s →L[ℂ] Hs d s :=
  (coordinates d s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((multiplicationCoordinates s a).comp (coordinates d s).toContinuousLinearEquiv.toContinuousLinearMap)

set_option maxHeartbeats 800000 in
lemma multiplicationMap_realization {d : ℕ} (s : ℝ) (a : Schwartz ℂ d) (u : Hs d s) :
    realization (s := s) (multiplicationMap s a u) =
      TemperedDistribution.smulLeftCLM ℂ (⇑a) (realization u) := by
  let R := realizationCLM d s
  let e : L2 d →L[ℂ] Hs d s := (coordinates d s).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let F := R.comp (e.comp (multiplicationCoordinates s a))
  let G := (TemperedDistribution.smulLeftCLM ℂ (⇑a)).comp (R.comp e)
  have hOn (g : Schwartz ℂ d) : F (g.toLp 2) = G (g.toLp 2) := by
    dsimp only [F, G, ContinuousLinearMap.comp_apply, R]
    rw [realizationCLM_apply, realizationCLM_apply]
    rw [multiplicationCoordinates_schwartz (d := d)]
    exact schwartzMultiplication_realization (d := d) s a g
  have hdense : DenseRange (fun g : Schwartz ℂ d => g.toLp 2) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (μ := volume) (by norm_num)
  have h := hdense.equalizer F.continuous G.continuous (funext hOn)
  have hu := congrFun h (coordinates d s u)
  dsimp only [F, G, ContinuousLinearMap.comp_apply, R] at hu
  rw [realizationCLM_apply, realizationCLM_apply] at hu
  change realization (s := s) (multiplicationMap s a u) =
    TemperedDistribution.smulLeftCLM ℂ (⇑a)
      (realization (s := s) ((coordinates d s).symm (coordinates d s u))) at hu
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hu

/-- In fact every Schwartz function is a bounded spatial multiplier, so the
compact-support condition of the manuscript is covered as a special case. -/
theorem multiplication : Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.multiplicationType := by
  intro d s a ha hc
  let f : Schwartz ℂ d := hc.toSchwartzMap ha
  refine ⟨multiplicationMap s f, ‖multiplicationMap s f‖, norm_nonneg _, fun u =>
    ⟨multiplicationMap_realization s f u, ContinuousLinearMap.le_opNorm _ _⟩⟩

end ExpandedFA.Sobolev.LocalOperations

namespace ExpandedFA.Sobolev.LocalOperations
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale
lemma complexifySchwartz_lineDeriv {d : ℕ} (v : Euclidean d) (φ : Schwartz ℝ d) :
  complexifySchwartz (LineDeriv.lineDerivOpCLM ℝ (Schwartz ℝ d) v φ) =
    LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) v (complexifySchwartz φ) := by
  ext x
  change (fderiv ℝ (⇑φ) x v : ℂ) = fderiv ℝ (Complex.ofRealCLM ∘ φ) x v
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x (φ.hasFDerivAt x)).fderiv]
  rfl

lemma restrictTempered_partial {d : ℕ} (i : Fin d) (T : Tempered ℂ d) :
    restrictTempered (temperedPartial i T) = realTemperedPartial i (restrictTempered T) := by
  ext φ
  change (-T (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)
    (complexifySchwartz φ))).re = -(T (complexifySchwartz
      (LineDeriv.lineDerivOpCLM ℝ (Schwartz ℝ d) (basisVector i) φ))).re
  rw [complexifySchwartz_lineDeriv]
  rfl

lemma restrictTempered_wordDerivative {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d) :
    restrictTempered (wordDerivative w T) = realWordDerivative w (restrictTempered T) := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih =>
    simpa only [wordDerivative, realWordDerivative, restrictTempered_partial] using
      ih (temperedPartial i T)

lemma wordDerivative_real {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d)
    (hT : ∀ φ : Schwartz ℝ d, (T (complexifySchwartz φ)).im = 0) :
    ∀ φ : Schwartz ℝ d, (wordDerivative w T (complexifySchwartz φ)).im = 0 := by
  induction w generalizing T with
  | nil => exact hT
  | cons i w ih =>
    apply ih (temperedPartial i T)
    intro φ
    change (-T (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)
      (complexifySchwartz φ))).im = 0
    rw [← complexifySchwartz_lineDeriv]
    simp only [Complex.neg_im, hT, neg_zero]

lemma complexifySchwartz_smulLeft {d : ℕ} (a φ : Schwartz ℝ d) :
    complexifySchwartz (SchwartzMap.smulLeftCLM ℝ (⇑a) φ) =
      SchwartzMap.smulLeftCLM ℂ (⇑(complexifySchwartz a)) (complexifySchwartz φ) := by
  ext x
  change ((SchwartzMap.smulLeftCLM ℝ (⇑a) φ) x : ℂ) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (complexifySchwartz a).hasTemperateGrowth]
  simp [complexifySchwartz, smul_eq_mul]


lemma restrictTempered_multiply {d : ℕ} (a : Schwartz ℝ d) (T : Tempered ℂ d) :
    restrictTempered (TemperedDistribution.smulLeftCLM ℂ (⇑(complexifySchwartz a)) T) =
      realTemperedMultiply (⇑a) (restrictTempered T) := by
  ext φ
  change (T (SchwartzMap.smulLeftCLM ℂ (⇑(complexifySchwartz a))
    (complexifySchwartz φ))).re = (T (complexifySchwartz
      (SchwartzMap.smulLeftCLM ℝ (⇑a) φ))).re
  rw [complexifySchwartz_smulLeft]

lemma multiply_real {d : ℕ} (a : Schwartz ℝ d) (T : Tempered ℂ d)
    (hT : ∀ φ : Schwartz ℝ d, (T (complexifySchwartz φ)).im = 0) :
    ∀ φ : Schwartz ℝ d,
      (TemperedDistribution.smulLeftCLM ℂ (⇑(complexifySchwartz a)) T
        (complexifySchwartz φ)).im = 0 := by
  intro φ
  change (T (SchwartzMap.smulLeftCLM ℂ (⇑(complexifySchwartz a))
    (complexifySchwartz φ))).im = 0
  rw [← complexifySchwartz_smulLeft]
  exact hT _


lemma derivativeMap_mem_real {d : ℕ} (s : ℝ) (α : Fin d → ℕ) (u : RealHs d s) :
    derivativeMap s α (realCoordinates d s u) ∈ hermitianL2 d := by
  apply (realization_real_iff _).mpr
  rw [derivativeMap_realization]
  exact wordDerivative_real _ _ ((realization_real_iff (realCoordinates d s u)).mp u.property)

def realDerivativeMap {d : ℕ} (s : ℝ) (α : Fin d → ℕ) :
    RealHs d s →L[ℝ] RealHs d (s - (∑ i, α i : ℕ)) :=
  (((derivativeMap s α).restrictScalars ℝ).comp
    (realCoordinates d s).toContinuousLinearMap).codRestrict
      (hermitianL2 d) (derivativeMap_mem_real s α)

lemma realDerivativeMap_realization {d : ℕ} (s : ℝ) (α : Fin d → ℕ) (u : RealHs d s) :
    realRealization (realDerivativeMap s α u) = realMultiDerivative α (realRealization u) := by
  change restrictTempered (realization (derivativeMap s α (realCoordinates d s u))) = _
  rw [derivativeMap_realization]
  exact restrictTempered_wordDerivative _ _

lemma realDerivativeMap_norm_le {d : ℕ} (s : ℝ) (α : Fin d → ℕ) (u : RealHs d s) :
    ‖realDerivativeMap s α u‖ ≤ ‖u‖ := by
  change ‖derivativeMap s α (realCoordinates d s u)‖ ≤ ‖u‖
  simpa only [(realCoordinates d s).norm_map] using
    derivativeMap_norm_le s α (realCoordinates d s u)

lemma multiplicationMap_mem_real {d : ℕ} (s : ℝ) (a : Schwartz ℝ d) (u : RealHs d s) :
    multiplicationMap s (complexifySchwartz a) (realCoordinates d s u) ∈ hermitianL2 d := by
  apply (realization_real_iff _).mpr
  rw [multiplicationMap_realization]
  exact multiply_real a _ ((realization_real_iff (realCoordinates d s u)).mp u.property)

def realMultiplicationMap {d : ℕ} (s : ℝ) (a : Schwartz ℝ d) :
    RealHs d s →L[ℝ] RealHs d s :=
  (((multiplicationMap s (complexifySchwartz a)).restrictScalars ℝ).comp
    (realCoordinates d s).toContinuousLinearMap).codRestrict
      (hermitianL2 d) (multiplicationMap_mem_real s a)

lemma realMultiplicationMap_realization {d : ℕ} (s : ℝ) (a : Schwartz ℝ d) (u : RealHs d s) :
    realRealization (realMultiplicationMap s a u) =
      realTemperedMultiply (⇑a) (realRealization u) := by
  change restrictTempered (realization (multiplicationMap s (complexifySchwartz a)
    (realCoordinates d s u))) = _
  rw [multiplicationMap_realization]
  exact restrictTempered_multiply a _

theorem real_derivatives :
    Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.realDerivativesType := by
  intro d s α
  exact ⟨realDerivativeMap s α, fun u =>
    ⟨realDerivativeMap_realization s α u, realDerivativeMap_norm_le s α u⟩⟩

theorem real_multiplication :
    Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.realMultiplicationType := by
  intro d s a ha hc
  let f : Schwartz ℝ d := hc.toSchwartzMap ha
  refine ⟨realMultiplicationMap s f, ‖realMultiplicationMap s f‖, norm_nonneg _, fun u =>
    ⟨realMultiplicationMap_realization s f u, ContinuousLinearMap.le_opNorm _ _⟩⟩

end ExpandedFA.Sobolev.LocalOperations

namespace ExpandedFA.Sobolev.LocalOperations
open Set TopologicalSpace ExpandedFA.Distributions ExpandedFA.Fourier
  ExpandedFA.Sobolev.FourierScale

lemma reTest_smul {d : ℕ} {Ω : Opens (Domain d)} (c : ℂ) (φ : Tests ℂ Ω) :
    TestFunction.postcompCLM Complex.reCLM (c • φ) =
      c.re • TestFunction.postcompCLM Complex.reCLM φ -
      c.im • TestFunction.postcompCLM Complex.imCLM φ := by
  ext x
  simp [Complex.mul_re, smul_eq_mul]

lemma imTest_smul {d : ℕ} {Ω : Opens (Domain d)} (c : ℂ) (φ : Tests ℂ Ω) :
    TestFunction.postcompCLM Complex.imCLM (c • φ) =
      c.re • TestFunction.postcompCLM Complex.imCLM φ +
      c.im • TestFunction.postcompCLM Complex.reCLM φ := by
  ext x
  simp [Complex.mul_im, smul_eq_mul]

def complexifyDistribution {d : ℕ} {Ω : Opens (Domain d)}
    (T : ScalarDistribution ℝ Ω) : ScalarDistribution ℂ Ω where
  toFun φ := (T (TestFunction.postcompCLM Complex.reCLM φ) : ℂ) +
    Complex.I * (T (TestFunction.postcompCLM Complex.imCLM φ) : ℂ)
  map_add' φ ψ := by simp [map_add, mul_add]; ring
  map_smul' c φ := by
    rw [reTest_smul, imTest_smul]
    simp only [map_sub, map_add, map_smul, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, smul_eq_mul, RingHom.id_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  cont := by
    exact ((Complex.ofRealCLM.comp
      (T.comp (TestFunction.postcompCLM Complex.reCLM))).continuous).add
      (continuous_const.mul (Complex.ofRealCLM.comp
        (T.comp (TestFunction.postcompCLM Complex.imCLM))).continuous)

@[simp] lemma complexifyDistribution_apply_real {d : ℕ} {Ω : Opens (Domain d)}
    (T : ScalarDistribution ℝ Ω) (φ : Tests ℝ Ω) :
    complexifyDistribution T (TestFunction.postcompCLM Complex.ofRealCLM φ) =
      (T φ : ℂ) := by
  have hr : TestFunction.postcompCLM Complex.reCLM
      (TestFunction.postcompCLM Complex.ofRealCLM φ) = φ := by ext x; simp
  have hi : TestFunction.postcompCLM Complex.imCLM
      (TestFunction.postcompCLM Complex.ofRealCLM φ) = 0 := by ext x; simp
  change (T (TestFunction.postcompCLM Complex.reCLM
      (TestFunction.postcompCLM Complex.ofRealCLM φ)) : ℂ) +
    Complex.I * (T (TestFunction.postcompCLM Complex.imCLM
      (TestFunction.postcompCLM Complex.ofRealCLM φ)) : ℂ) = _
  rw [hr, hi, map_zero]
  simp

lemma distributionSupport_complexify_subset {d : ℕ} {Ω : Opens (Domain d)}
    (T : ScalarDistribution ℝ Ω) :
    distributionSupport (complexifyDistribution T) ⊆ distributionSupport T := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hv
  obtain ⟨V, hV, hxV⟩ := hv
  apply hx.2
  refine mem_sUnion.mpr ⟨V, ⟨hV.1, hV.2.1, ?_⟩, hxV⟩
  intro φ hφ
  have hre := hV.2.2 (TestFunction.postcompCLM Complex.reCLM φ)
    ((tsupport_comp_subset (map_zero Complex.reCLM) φ).trans hφ)
  have him := hV.2.2 (TestFunction.postcompCLM Complex.imCLM φ)
    ((tsupport_comp_subset (map_zero Complex.imCLM) φ).trans hφ)
  change (T _ : ℂ) + Complex.I * (T _ : ℂ) = 0
  rw [hre, him]
  simp

lemma isCompact_support_complexify {d : ℕ}
    (T : ScalarDistribution ℝ (⊤ : Opens (Domain d)))
    (hT : IsCompact (distributionSupport T)) :
    IsCompact (distributionSupport (complexifyDistribution T)) := by
  apply hT.of_isClosed_subset _ (distributionSupport_complexify_subset T)
  change IsClosed ((⊤ : Opens (Domain d)) \ vanishingRegion (complexifyDistribution T))
  change IsClosed (univ \ vanishingRegion (complexifyDistribution T))
  rw [show (Set.univ \ vanishingRegion (complexifyDistribution T)) =
    (vanishingRegion (complexifyDistribution T))ᶜ by ext x; simp]
  apply IsOpen.isClosed_compl
  exact isOpen_sUnion fun V hV => hV.1

lemma realRealization_hermitianProjection {d : ℕ} {s : ℝ} (u : Hs d s)
    (φ : Schwartz ℝ d) :
    realRealization (hermitianProjection d s u) φ =
      (realization u (complexifySchwartz φ)).re := by
  change (realization (show Hs d s from
    (2 : ℝ)⁻¹ • (u + (show Hs d s from realConjugateReflectionL2 d u))) (complexifySchwartz φ)).re = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
    (realization_linear d s).2, (realization_linear d s).1]
  have hc : conjSchwartz (complexifySchwartz φ) = complexifySchwartz φ := by
    ext x
    simp [complexifySchwartz]
  rw [smul_apply, add_apply,
    realization_conjugateReflection, hc]
  simp [Complex.mul_re]
  ring

lemma complexify_testSchwartz {d : ℕ}
    (φ : Tests ℝ (⊤ : Opens (Domain d))) :
    complexifySchwartz (Examples.testSchwartz ℝ φ) =
      Examples.testSchwartz ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ) := by
  ext x
  rfl

theorem real_compact_support :
    Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.realCompactSupportType := by
  intro d T hT
  obtain ⟨N, u, hu⟩ := compact_support d (complexifyDistribution T)
    (isCompact_support_complexify T hT)
  refine ⟨N, hermitianProjection d (-(N : ℝ)) u, ?_⟩
  intro φ
  rw [realRealization_hermitianProjection, complexify_testSchwartz, hu,
    complexifyDistribution_apply_real, Complex.ofReal_re]

end ExpandedFA.Sobolev.LocalOperations


namespace ExpandedFA.Sobolev.LocalOperations
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

/-- Taking the real part preserves the actual distribution pairing on real tests. -/
lemma real_representative_pairing {d : ℕ} {s : ℝ} (u : RealHs d s)
    (f : Euclidean d → ℂ)
    (hf : ∀ φ : Schwartz ℂ d, Integrable (fun x => φ x * f x) ∧
      @realization d s (realCoordinates d s u) φ = ∫ x, φ x * f x)
    (φ : Schwartz ℝ d) :
    Integrable (fun x => φ x * (f x).re) ∧
      realRealization u φ = ∫ x, φ x * (f x).re := by
  obtain ⟨hi, he⟩ := hf (complexifySchwartz φ)
  constructor
  · simpa [complexifySchwartz, Complex.mul_re] using hi.re
  · change (@realization d s (realCoordinates d s u) (complexifySchwartz φ)).re = _
    rw [he]
    change RCLike.re (∫ x, (complexifySchwartz φ) x * f x) = _
    rw [← integral_re hi]
    simp [complexifySchwartz]

/-- The real representative and all its derivatives retain the complex bound. -/
theorem real_embedding :
    Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations.realEmbeddingType := by
  intro d k s hs
  obtain ⟨C, hC, h⟩ := embedding d k s hs
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨f, hf, hpair, hbound⟩ := h (realCoordinates d s u)
  refine ⟨fun x => (f x).re, hf.continuousLinearMap_comp Complex.reCLM,
    real_representative_pairing u f hpair, fun j hj x => ?_⟩
  have hcomp := Complex.reCLM.iteratedFDeriv_comp_left (hf.contDiffAt (x := x))
    (i := j) (by exact_mod_cast hj)
  have hnorm : ‖iteratedFDeriv ℝ j (fun x => (f x).re) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ := by
    change ‖iteratedFDeriv ℝ j (Complex.reCLM ∘ f) x‖ ≤ _
    rw [hcomp]
    simpa only [Complex.reCLM_norm, one_mul] using
      Complex.reCLM.norm_compContinuousMultilinearMap_le (iteratedFDeriv ℝ j f x)
  have hb := hbound j hj x
  change ‖iteratedFDeriv ℝ j f x‖ ≤ C * ‖realCoordinates d s u‖ at hb
  rw [(realCoordinates d s).norm_map u] at hb
  exact hnorm.trans hb

end ExpandedFA.Sobolev.LocalOperations
