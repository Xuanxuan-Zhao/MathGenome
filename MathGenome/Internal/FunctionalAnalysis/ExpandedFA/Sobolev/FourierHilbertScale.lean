import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.Plancherel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Algebra.Order.Chebyshev

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

lemma frequencyWeight_pos {d : ℕ} (ξ : Euclidean d) : 0 < frequencyWeight ξ := by
  unfold frequencyWeight
  positivity

lemma weight_pos {d : ℕ} (s : ℝ) (ξ : Euclidean d) : 0 < weight s ξ :=
  Real.rpow_pos_of_pos (frequencyWeight_pos ξ) _

lemma weight_add {d : ℕ} (s t : ℝ) (ξ : Euclidean d) :
    weight (s + t) ξ = weight s ξ * weight t ξ := by
  simp only [weight, add_div]
  exact Real.rpow_add (frequencyWeight_pos ξ) _ _

@[simp] lemma weight_zero {d : ℕ} (ξ : Euclidean d) : weight 0 ξ = 1 := by
  simp [weight]

lemma weight_neg_mul {d : ℕ} (s : ℝ) (ξ : Euclidean d) :
    weight (-s) ξ * weight s ξ = 1 := by
  rw [← weight_add]
  simp

lemma complexWeight_add {d : ℕ} (s t : ℝ) :
    complexWeight (d := d) (s + t) = complexWeight s * complexWeight t := by
  ext ξ
  simp [complexWeight, weight_add]

@[simp] lemma complexWeight_zero {d : ℕ} : complexWeight (d := d) 0 = fun _ => 1 := by
  ext ξ
  simp [complexWeight]

lemma weight_hasTemperateGrowth {d : ℕ} (s : ℝ) :
    (weight (d := d) s).HasTemperateGrowth := by
  have h : (fun ξ : Euclidean d =>
      (1 + ‖(2 * Real.pi) • ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euclidean d) (s / 2)).comp
      (by fun_prop)
  convert h using 1
  ext ξ
  unfold weight
  congr 1
  simp only [frequencyWeight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma complexWeight_hasTemperateGrowth {d : ℕ} (s : ℝ) :
    (complexWeight (d := d) s).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (weight_hasTemperateGrowth s)

lemma complexWeight_mul_neg {d : ℕ} (s : ℝ) :
    complexWeight (d := d) (-s) * complexWeight s = fun _ => 1 := by
  rw [← complexWeight_add]
  simp

/-- Multiplying by reciprocal weights really cancels on all tempered distributions. -/
lemma cancel_weights {d : ℕ} (s : ℝ) (T : TemperedDistribution (Euclidean d) ℂ) :
    TemperedDistribution.smulLeftCLM ℂ (complexWeight s)
      (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s)) T) = T := by
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (complexWeight_hasTemperateGrowth (-s)) (complexWeight_hasTemperateGrowth s)]
  simp [complexWeight_mul_neg]

lemma fourier_realization {d : ℕ} {s : ℝ} (u : Hs d s) :
    temperedFourier (realization u) =
      TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
        (Lp.toTemperedDistribution (coordinates d s u)) := by
  change 𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
    (Lp.toTemperedDistribution (coordinates d s u)))) = _
  exact FourierTransform.fourier_fourierInv_eq _

lemma weighted_fourier_realization {d : ℕ} {s : ℝ} (u : Hs d s) :
    TemperedDistribution.smulLeftCLM ℂ (complexWeight s)
      (temperedFourier (realization u)) =
        Lp.toTemperedDistribution (coordinates d s u) := by
  rw [fourier_realization]
  exact cancel_weights s _

def space : Specs.ExpandedFA.Sobolev.FourierHilbertScale.spaceType := Hs

def realize : Specs.ExpandedFA.Sobolev.FourierHilbertScale.realizationType := @realization

theorem hilbert : Specs.ExpandedFA.Sobolev.FourierHilbertScale.hilbertType := by
  intro d s
  infer_instance

theorem realization_linear :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.realizationLinearType := by
  intro d s
  constructor
  · intro u v
    change (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
      (Lp.toTemperedDistributionCLM ℂ volume 2 (coordinates d s (u + v))))) = _
    simp only [map_add, realization, FourierTransform.fourierInv_add]
    rfl
  · intro c u
    change (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
      (Lp.toTemperedDistributionCLM ℂ volume 2 (coordinates d s (c • u))))) = _
    simp only [map_smul, realization, FourierTransform.fourierInv_smul]
    rfl

theorem realization_injective :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.realizationInjectiveType := by
  intro d s u v huv
  have h := congrArg (fun T => TemperedDistribution.smulLeftCLM ℂ (complexWeight s)
    (temperedFourier T)) huv
  rw [weighted_fourier_realization, weighted_fourier_realization] at h
  apply (coordinates d s).injective
  exact (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure (Euclidean d)))
      (p := 2))) h

theorem bessel : Specs.ExpandedFA.Sobolev.FourierHilbertScale.besselType := by
  intro d s t u
  apply_fun (fun T : Tempered ℂ d => temperedFourier T) using
    (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective
  dsimp only
  rw [fourier_realization]
  change _ = 𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight t)
    (temperedFourier (realization u))))
  rw [FourierTransform.fourier_fourierInv_eq, fourier_realization,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (complexWeight_hasTemperateGrowth (-s)) (complexWeight_hasTemperateGrowth t)]
  rw [← complexWeight_add]
  rw [show -s + t = -(s - t) by ring]
  rfl

/-- The weighted L² density defines a genuine regular tempered distribution. -/
lemma weighted_regular_pair {d : ℕ} (r : ℝ) (f : L2 d) (φ : Schwartz ℂ d) :
    Integrable (fun ξ => φ ξ * (complexWeight r ξ * f ξ)) ∧
    TemperedDistribution.smulLeftCLM ℂ (complexWeight r)
        (Lp.toTemperedDistribution f) φ =
      ∫ ξ, φ ξ * (complexWeight r ξ * f ξ) := by
  let ψ := SchwartzMap.smulLeftCLM ℂ (complexWeight r) φ
  have hi := (ψ.memLp 2).integrable_mul (Lp.memLp f)
  have heq : (fun ξ => ψ ξ * f ξ) =
      (fun ξ => φ ξ * (complexWeight r ξ * f ξ)) := by
    ext ξ
    simp only [ψ, SchwartzMap.smulLeftCLM_apply_apply
      (complexWeight_hasTemperateGrowth r), smul_eq_mul]
    ring
  constructor
  · simpa only [Pi.mul_def, heq] using hi
  · rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ξ => by
      simp only [SchwartzMap.smulLeftCLM_apply_apply
        (complexWeight_hasTemperateGrowth r), smul_eq_mul]
      ring))

theorem density : Specs.ExpandedFA.Sobolev.FourierHilbertScale.densityType := by
  intro d s u
  constructor
  · exact ((Lp.memLp (coordinates d s u)).locallyIntegrable (by norm_num)).continuous_mul
      (complexWeight_hasTemperateGrowth (-s)).1.continuous
  · intro φ
    rw [fourier_realization]
    exact weighted_regular_pair (-s) (coordinates d s u) φ

lemma weighted_density_eq_coordinates {d : ℕ} {s : ℝ} (u : Hs d s)
    (ξ : Euclidean d) :
    complexWeight s ξ * fourierDensity u ξ = coordinates d s u ξ := by
  simp only [fourierDensity, complexWeight, ← mul_assoc, ← Complex.ofReal_mul]
  rw [mul_comm (weight s ξ), weight_neg_mul, Complex.ofReal_one, one_mul]

lemma weighted_fourier_injective (d : ℕ) (s : ℝ) :
    Function.Injective (fun T : Tempered ℂ d =>
      TemperedDistribution.smulLeftCLM ℂ (complexWeight s) (temperedFourier T)) := by
  intro T U h
  have h' := congrArg (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))) h
  dsimp only at h'
  have he := cancel_weights (d := d) (-s)
  simp only [neg_neg] at he
  rw [he, he] at h'
  exact (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective h'

theorem realization_image :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.realizationImageType := by
  intro d s T
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fourierDensity u, density d s u, ?_⟩
    simpa only [weighted_density_eq_coordinates] using Lp.memLp (coordinates d s u)
  · rintro ⟨f, hf, hmem⟩
    let g : L2 d := hmem.toLp (fun ξ => complexWeight s ξ * f ξ)
    refine ⟨(coordinates d s).symm g, ?_⟩
    apply weighted_fourier_injective d s
    dsimp only
    rw [weighted_fourier_realization, LinearIsometryEquiv.apply_symm_apply]
    ext φ
    rw [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply,
      (hf.2 (SchwartzMap.smulLeftCLM ℂ (complexWeight s) φ)).2]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with ξ hξ
    simp only [g, hξ, SchwartzMap.smulLeftCLM_apply_apply
      (complexWeight_hasTemperateGrowth s), smul_eq_mul]
    ring

lemma weight_sq {d : ℕ} (s : ℝ) (ξ : Euclidean d) :
    weight s ξ ^ 2 = frequencyWeight ξ ^ s := by
  rw [weight, ← Real.rpow_mul_natCast (frequencyWeight_pos ξ).le]
  congr 1
  ring

lemma norm_integrand {d : ℕ} {s : ℝ} (u : Hs d s) (ξ : Euclidean d) :
    frequencyWeight ξ ^ s * ‖fourierDensity u ξ‖ ^ 2 =
      ‖coordinates d s u ξ‖ ^ 2 := by
  rw [fourierDensity, norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos (-s) ξ), mul_pow, ← weight_sq s ξ]
  rw [← mul_assoc, ← mul_pow, mul_comm (weight s ξ), weight_neg_mul]
  simp

lemma l2_norm_sq (d : ℕ) (f : L2 d) : ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  have hi := L2.integrable_inner (𝕜 := ℂ) f f
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := f)
  have hr := congrArg Complex.re h
  change RCLike.re (inner ℂ f f) = RCLike.re ((‖f‖ : ℂ) ^ 2) at hr
  rw [L2.inner_def, ← integral_re (𝕜 := ℂ) hi] at hr
  rw [← Complex.ofReal_pow] at hr
  change (∫ ξ, RCLike.re (inner ℂ (f ξ) (f ξ))) = ‖f‖ ^ 2 at hr
  simpa only [inner_self_eq_norm_sq] using hr.symm

theorem norm_formula : Specs.ExpandedFA.Sobolev.FourierHilbertScale.normType := by
  intro d s u
  simp only [norm_integrand]
  exact ⟨(Lp.memLp _).integrable_norm_pow (by decide),
    ((coordinates d s).norm_map u).symm ▸ l2_norm_sq d (coordinates d s u)⟩

theorem schwartz_inclusion :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.schwartzInclusionType := by
  intro d s f
  apply (realization_image d s (schwartzRegularDistribution f)).mpr
  refine ⟨schwartzFourier f, ?_, ?_⟩
  · constructor
    · exact (schwartzFourier f).continuous.locallyIntegrable
    · intro φ
      constructor
      · exact (φ.memLp 2).integrable_mul ((schwartzFourier f).memLp 2)
      · rw [Inversion.fourier_regular_distribution,
          Inversion.regular_distribution_pairing]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ξ => mul_comm _ _
  · have h := (SchwartzMap.smulLeftCLM ℂ (complexWeight s) (schwartzFourier f)).memLp 2
    simpa only [SchwartzMap.smulLeftCLM_apply (complexWeight_hasTemperateGrowth s),
      smul_eq_mul] using h

@[simp] lemma complexWeight_neg_argument {d : ℕ} (s : ℝ) (ξ : Euclidean d) :
    complexWeight s (-ξ) = complexWeight s ξ := by
  simp [complexWeight, weight, frequencyWeight]

lemma pairing_integrand {d : ℕ} {s : ℝ} (u : Hs d s) (v : Hs d (-s))
    (ξ : Euclidean d) :
    fourierDensity u ξ * fourierDensity v (-ξ) =
      coordinates d s u ξ * coordinates d (-s) v (-ξ) := by
  simp only [fourierDensity, neg_neg, complexWeight_neg_argument]
  calc
    _ = (complexWeight (-s) ξ * complexWeight s ξ) *
        (coordinates d s u ξ * coordinates d (-s) v (-ξ)) := by ring
    _ = _ := by
      rw [← Pi.mul_apply, complexWeight_mul_neg]
      simp

/-- Reflection preserves Euclidean volume, including dimension zero. -/
def reflectionL2 (d : ℕ) : L2 d →ₗᵢ[ℂ] L2 d :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun ξ : Euclidean d => -ξ)
    (Measure.measurePreserving_neg volume)

lemma reflectionL2_coe (d : ℕ) (f : L2 d) :
    reflectionL2 d f =ᵐ[volume] fun ξ => f (-ξ) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

lemma reflectionL2_involutive (d : ℕ) : Function.Involutive (reflectionL2 d) := by
  intro f
  apply Lp.ext
  filter_upwards [reflectionL2_coe d (reflectionL2 d f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae
      (reflectionL2_coe d f)] with ξ h₁ h₂
  simpa only [h₁, neg_neg] using h₂

theorem pairing_integrable :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.pairingIntegrableType := by
  intro d s u v
  simp only [pairing_integrand]
  have hi := (Lp.memLp (coordinates d s u)).integrable_mul
    (Lp.memLp (reflectionL2 d (coordinates d (-s) v)))
  exact hi.congr ((reflectionL2_coe d (coordinates d (-s) v)).mono fun ξ h => congrArg (coordinates d s u ξ * ·) h)

/-- Conjugation on L², kept conjugate-linear until it is composed with Riesz. -/
def conjugationL2 (d : ℕ) : L2 d →ₗ⋆[ℂ] L2 d :=
  (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.compLpₗ 2 volume

lemma conjugationL2_coe (d : ℕ) (f : L2 d) :
    conjugationL2 d f =ᵐ[volume] fun ξ => star (f ξ) :=
  ContinuousLinearMap.coeFn_compLp (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap f

lemma conjugationL2_involutive (d : ℕ) : Function.Involutive (conjugationL2 d) := by
  intro f
  apply Lp.ext
  filter_upwards [conjugationL2_coe d (conjugationL2 d f),
    conjugationL2_coe d f] with ξ h₁ h₂
  simp only [h₁, h₂, star_star]

lemma conjugationL2_norm (d : ℕ) (f : L2 d) : ‖conjugationL2 d f‖ = ‖f‖ := by
  have h : ‖conjugationL2 d f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [conjugationL2_coe d f] with ξ hξ
    simp [hξ]
  nlinarith [norm_nonneg f, norm_nonneg (conjugationL2 d f)]

/-- The two conjugate-linear maps compose to the scalar-linear bilinear dual. -/
def bilinearL2Dual (d : ℕ) : L2 d →ₗᵢ[ℂ] (L2 d →L[ℂ] ℂ) where
  toFun f := InnerProductSpace.toDual ℂ (L2 d) (conjugationL2 d f)
  map_add' f g := by simp
  map_smul' c f := by
    simp only [map_smulₛₗ]
    congr 1
    exact star_star c
  norm_map' f := by simp [conjugationL2_norm]

lemma bilinearL2Dual_apply (d : ℕ) (f g : L2 d) :
    bilinearL2Dual d f g = ∫ ξ, g ξ * f ξ := by
  change inner ℂ (conjugationL2 d f) g = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [conjugationL2_coe d f] with ξ hξ
  simp [hξ, RCLike.inner_apply, mul_comm]

lemma bilinearL2Dual_surjective (d : ℕ) : Function.Surjective (bilinearL2Dual d) := by
  intro F
  obtain ⟨f, hf⟩ := (InnerProductSpace.toDual ℂ (L2 d)).surjective F
  exact ⟨conjugationL2 d f, by
    change InnerProductSpace.toDual ℂ (L2 d) _ = F
    rw [conjugationL2_involutive, hf]⟩

theorem duality : Specs.ExpandedFA.Sobolev.FourierHilbertScale.dualType := by
  intro d s
  let e₁ : L2 d ≃ₗᵢ[ℂ] L2 d := LinearIsometryEquiv.ofSurjective
    (reflectionL2 d) (reflectionL2_involutive d).surjective
  let e₂ := LinearIsometryEquiv.ofSurjective (bilinearL2Dual d)
    (bilinearL2Dual_surjective d)
  refine ⟨e₁.trans e₂, ?_⟩
  intro u v
  change bilinearL2Dual d (reflectionL2 d v) u = dualPairing u v
  rw [bilinearL2Dual_apply]
  unfold dualPairing
  simp only [pairing_integrand]
  apply integral_congr_ae
  filter_upwards [reflectionL2_coe d v] with ξ hξ
  exact congrArg (coordinates d s u ξ * ·) hξ

/-- A regular Schwartz distribution fixes its weighted L² coordinate uniquely. -/
lemma coordinates_of_schwartz {d : ℕ} {s : ℝ} (u : Hs d s)
    (f : Schwartz ℂ d) (hu : realization u = schwartzRegularDistribution f) :
    coordinates d s u =
      (SchwartzMap.smulLeftCLM ℂ (complexWeight s) (schwartzFourier f)).toLp 2 := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
      (μ := (volume : Measure (Euclidean d))) (p := 2)))
  change Lp.toTemperedDistribution _ = Lp.toTemperedDistribution _
  rw [← weighted_fourier_realization, hu, Inversion.fourier_regular_distribution]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    Inversion.regular_distribution_pairing, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (complexWeight s)
    (schwartzFourier f)).coeFn_toLp 2] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply_apply
    (complexWeight_hasTemperateGrowth s), smul_eq_mul]
  ring

lemma fourierDensity_of_schwartz {d : ℕ} {s : ℝ} (u : Hs d s)
    (f : Schwartz ℂ d) (hu : realization u = schwartzRegularDistribution f) :
    fourierDensity u =ᵐ[volume] schwartzFourier f := by
  unfold fourierDensity
  rw [coordinates_of_schwartz u f hu]
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (complexWeight s)
    (schwartzFourier f)).coeFn_toLp 2] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply_apply
    (complexWeight_hasTemperateGrowth s), smul_eq_mul, ← mul_assoc]
  rw [← Pi.mul_apply, complexWeight_mul_neg]
  simp

theorem pairing_test :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.pairingTestType := by
  intro d s u g v hv
  have hv' := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae
    (fourierDensity_of_schwartz v g hv)
  calc
    dualPairing u v = ∫ ξ, (𝓕⁻ g : Schwartz ℂ d) ξ * fourierDensity u ξ := by
      unfold dualPairing
      apply integral_congr_ae
      filter_upwards [hv'] with ξ hξ
      rw [hξ, mul_comm]
      rfl
    _ = temperedFourier (realization u) (𝓕⁻ g) :=
      ((density d s u).2 (𝓕⁻ g)).2.symm
    _ = realization u g := by
      change realization u (𝓕 (𝓕⁻ g)) = _
      rw [FourierTransform.fourier_fourierInv_eq]

theorem pairing_extends :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.pairingExtendsType := by
  intro d s f g u v hu hv
  rw [pairing_test d s u g v hv, hu, Inversion.regular_distribution_pairing]

/-- The two Euclidean norm conventions have the same Lebesgue measure.
The explicit maps record the change of analytic instances. -/
def euclideanToDomainL2 (d : ℕ) :
    L2 d →ₗᵢ[ℂ] DomainLp ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) 2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.toLp 2 (Fin d → ℝ))
    (by simpa using PiLp.volume_preserving_toLp (Fin d))

def domainToEuclideanL2 (d : ℕ) :
    DomainLp ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) 2 →ₗᵢ[ℂ] L2 d :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.ofLp 2 (Fin d → ℝ))
    (by simpa using PiLp.volume_preserving_ofLp (Fin d))

lemma euclideanToDomainL2_coe (d : ℕ) (f : L2 d) :
    euclideanToDomainL2 d f =ᵐ[volume] fun x => f (WithLp.toLp 2 x) := by
  have h : euclideanToDomainL2 d f =ᵐ[volume.restrict
      (⊤ : TopologicalSpace.Opens (Distributions.Domain d))]
        (fun x => f (WithLp.toLp 2 x)) := Lp.coeFn_compMeasurePreserving f _
  simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using h

lemma domainToEuclideanL2_coe (d : ℕ)
    (f : DomainLp ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) 2) :
    domainToEuclideanL2 d f =ᵐ[volume] fun x => f (WithLp.ofLp x) :=
  Lp.coeFn_compMeasurePreserving f _

lemma euclideanToDomainL2_rightInverse (d : ℕ) :
    Function.RightInverse (domainToEuclideanL2 d) (euclideanToDomainL2 d) := by
  intro f
  apply Lp.ext
  have h := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae
    (domainToEuclideanL2_coe d f)
  simpa using (euclideanToDomainL2_coe d (domainToEuclideanL2 d f)).trans h

/-- An isometric identification of the L² spaces for the two norm conventions. -/
def euclideanDomainL2Equiv (d : ℕ) :
    L2 d ≃ₗᵢ[ℂ] DomainLp ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) 2 :=
  LinearIsometryEquiv.ofSurjective (euclideanToDomainL2 d)
    (euclideanToDomainL2_rightInverse d).surjective

lemma orderZeroIndex_unique (d : ℕ) (α : DerivativeIndex d 0) :
    α = zeroIndex d 0 := by
  apply Subtype.ext
  funext i
  exact Fin.eq_zero _

/-- The order-zero derivative graph has just its underlying L² coordinate. -/
def orderZeroGraph (d : ℕ) :
    DomainLp ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) 2 →ₗᵢ[ℂ]
      IntegerSobolev d 0 where
  toFun f := ⟨WithLp.toLp 1 (fun _ => f), by
    intro α
    change lpDistribution f =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        ℂ d ⊤ (natIndex α) (lpDistribution f)
    have hα : natIndex α = fun _ => 0 := by
      funext i
      exact congrArg Fin.val (Fin.eq_zero (α.val i))
    rw [hα, derivative_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    change ‖WithLp.toLp 1 (fun _ : DerivativeIndex d 0 => f)‖ = ‖f‖
    rw [PiLp.norm_eq_of_L1]
    let : Unique (DerivativeIndex d 0) :=
      ⟨⟨zeroIndex d 0⟩, orderZeroIndex_unique d⟩
    simp

lemma orderZeroGraph_surjective (d : ℕ) : Function.Surjective (orderZeroGraph d) := by
  intro u
  refine ⟨u.val (zeroIndex d 0), ?_⟩
  apply Subtype.ext
  apply PiLp.ext
  intro α
  exact congrArg u.val (orderZeroIndex_unique d α).symm

def orderZeroGraphEquiv (d : ℕ) :
    DomainLp ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) 2 ≃ₗᵢ[ℂ]
      IntegerSobolev d 0 :=
  LinearIsometryEquiv.ofSurjective (orderZeroGraph d) (orderZeroGraph_surjective d)

lemma realization_zero {d : ℕ} (u : Hs d 0) :
    realization u = Lp.toTemperedDistribution
      ((l2Fourier d).symm (coordinates d 0 u)) := by
  simp only [realization, neg_zero, complexWeight_zero,
    TemperedDistribution.smulLeftCLM_const, one_smul]
  exact Lp.fourierInv_toTemperedDistribution_eq _

/-- Order zero identifies the actual weak-derivative graph, with exact norm. -/
theorem integer_zero :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.integerZeroType := by
  intro d
  let e := (coordinates d 0).trans ((l2Fourier d).symm.trans
    ((euclideanDomainL2Equiv d).trans (orderZeroGraphEquiv d)))
  refine ⟨e, ?_⟩
  intro u φ
  rw [realization_zero, Lp.toTemperedDistribution_apply]
  change (∫ x, φ x * (l2Fourier d).symm (coordinates d 0 u) x) =
    ∫ x, φ x * euclideanToDomainL2 d ((l2Fourier d).symm (coordinates d 0 u)) x
  apply integral_congr_ae
  have h := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae
    (euclideanToDomainL2_coe d ((l2Fourier d).symm (coordinates d 0 u)))
  filter_upwards [h] with x hx
  exact congrArg (φ x * ·) hx.symm

set_option maxHeartbeats 600000 in
/-- Weighted Schwartz Fourier coordinates are dense in each Hs model. -/
theorem schwartz_dense :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.schwartzDenseType := by
  intro d s
  have hdense : Dense (Set.range (fun f : Schwartz ℂ d =>
      (coordinates d s).symm (f.toLp 2))) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (μ := (volume : Measure (Euclidean d)))
      (by norm_num)
  refine Dense.mono ?_ hdense
  rintro u ⟨f, rfl⟩
  let g := SchwartzMap.smulLeftCLM ℂ (complexWeight (-s)) f
  refine ⟨𝓕⁻ g, ?_⟩
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective
  change temperedFourier _ = temperedFourier _
  rw [fourier_realization, Inversion.fourier_regular_distribution]
  simp only [LinearIsometryEquiv.apply_symm_apply, schwartzFourier,
    FourierTransform.fourierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, Inversion.regular_distribution_pairing]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2] with ξ hξ
  simp only [hξ, g, SchwartzMap.smulLeftCLM_apply_apply
    (complexWeight_hasTemperateGrowth (-s)), smul_eq_mul]
  ring

lemma frequencyWeight_one_le {d : ℕ} (ξ : Euclidean d) : 1 ≤ frequencyWeight ξ := by
  unfold frequencyWeight
  have h : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  linarith

lemma complexWeight_neg_norm_le_one {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (ξ : Euclidean d) :
    ‖complexWeight (-s) ξ‖ ≤ 1 := by
  rw [complexWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos (-s) ξ)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (frequencyWeight_one_le ξ)
    (show -s / 2 ≤ 0 by linarith)

lemma fourierDensity_norm_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s)
    (ξ : Euclidean d) : ‖fourierDensity u ξ‖ ≤ ‖coordinates d s u ξ‖ := by
  rw [fourierDensity, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (complexWeight_neg_norm_le_one hs ξ)

lemma fourierDensity_memLp {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) :
    MemLp (fourierDensity u) 2 volume := by
  apply (Lp.memLp (coordinates d s u)).of_le_mul
    ((complexWeight_hasTemperateGrowth (-s)).1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)) (c := 1)
  exact Filter.Eventually.of_forall fun ξ => by simpa [fourierDensity, norm_mul] using fourierDensity_norm_le hs u ξ

lemma realization_regular_of_memLp {d : ℕ} {s : ℝ} (u : Hs d s)
    (hu : MemLp (fourierDensity u) 2 volume) :
    realization u = Lp.toTemperedDistribution ((l2Fourier d).symm (hu.toLp (fourierDensity u))) := by
  have heq :
      TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
          (Lp.toTemperedDistribution (coordinates d s u)) =
        Lp.toTemperedDistribution (hu.toLp (fourierDensity u)) := by
    ext φ
    rw [(weighted_regular_pair (-s) (coordinates d s u) φ).2,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with ξ hξ
    rw [hξ]
    rfl
  change 𝓕⁻ _ = _
  rw [heq]
  exact Lp.fourierInv_toTemperedDistribution_eq _

lemma realization_regular_nonneg {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) :
    ∃ f : L2 d, realization u = Lp.toTemperedDistribution f :=
  ⟨_, realization_regular_of_memLp u (fourierDensity_memLp hs u)⟩


/-- The unweighted Fourier density belongs to L² for nonnegative orders. -/
def fourierDensityL2 {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) : L2 d :=
  (fourierDensity_memLp hs u).toLp (fourierDensity u)

lemma fourierDensityL2_coe {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) :
    fourierDensityL2 hs u =ᵐ[volume] fourierDensity u :=
  (fourierDensity_memLp hs u).coeFn_toLp

lemma fourierDensityL2_add {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u v : Hs d s) :
    fourierDensityL2 hs (u + v) = fourierDensityL2 hs u + fourierDensityL2 hs v := by
  apply Lp.ext
  filter_upwards [fourierDensityL2_coe hs (u+v), fourierDensityL2_coe hs u,
    fourierDensityL2_coe hs v, Lp.coeFn_add (fourierDensityL2 hs u) (fourierDensityL2 hs v),
    Lp.coeFn_add (coordinates d s u) (coordinates d s v)] with ξ h₀ h₁ h₂ h₃ h₄
  rw [h₀, h₃]
  dsimp only [Pi.add_apply]
  rw [h₁, h₂]
  dsimp only [fourierDensity]
  rw [map_add, h₄]
  simp only [Pi.add_apply, mul_add]

lemma fourierDensityL2_smul {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (c : ℂ) (u : Hs d s) :
    fourierDensityL2 hs (c • u) = c • fourierDensityL2 hs u := by
  apply Lp.ext
  filter_upwards [fourierDensityL2_coe hs (c • u), fourierDensityL2_coe hs u,
    Lp.coeFn_smul c (fourierDensityL2 hs u),
    Lp.coeFn_smul c (coordinates d s u)] with ξ h₀ h₁ h₂ h₃
  rw [h₀, h₂]
  dsimp only [Pi.smul_apply]
  rw [h₁]
  dsimp only [fourierDensity]
  rw [map_smul, h₃]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma fourierDensityL2_norm_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) :
    ‖fourierDensityL2 hs u‖ ≤ ‖u‖ := by
  rw [← (coordinates d s).norm_map u]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fourierDensityL2_coe hs u] with ξ hξ
  rw [hξ]
  exact fourierDensity_norm_le hs u ξ

/-- Forgetting nonnegative-order Fourier weights is a contraction into L². -/
def fourierDensityL2CLM (d : ℕ) (s : ℝ) (hs : 0 ≤ s) : Hs d s →L[ℂ] L2 d :=
  LinearMap.mkContinuous
    { toFun := fourierDensityL2 hs
      map_add' := fourierDensityL2_add hs
      map_smul' := fourierDensityL2_smul hs }
    1 (by
      intro u
      change ‖fourierDensityL2 hs u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using fourierDensityL2_norm_le hs u)

/-- The actual underlying L² function of an Hs element of nonnegative order. -/
def underlyingL2 (d : ℕ) (s : ℝ) (hs : 0 ≤ s) : Hs d s →L[ℂ] L2 d :=
  (l2Fourier d).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fourierDensityL2CLM d s hs)

lemma underlyingL2_norm_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) :
    ‖underlyingL2 d s hs u‖ ≤ ‖u‖ := by
  change ‖(l2Fourier d).symm (fourierDensityL2 hs u)‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact fourierDensityL2_norm_le hs u

lemma realization_underlyingL2 {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s) :
    realization u = Lp.toTemperedDistribution (underlyingL2 d s hs u) :=
  realization_regular_of_memLp u (fourierDensity_memLp hs u)



def derivativeSymbol {d : ℕ} (α : Fin d → ℕ) (ξ : Euclidean d) : ℂ :=
  ∏ i, ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ α i

lemma coordinate_symbol_norm_sq {d : ℕ} (ξ : Euclidean d) (i : Fin d) :
    ‖(2 * Real.pi * Complex.I) * (ξ i : ℂ)‖ ^ 2 ≤ frequencyWeight ξ := by
  have hx : ‖ξ i‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖ξ j‖) (Finset.mem_univ i)
  norm_num only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs]
  simp only [Real.norm_eq_abs, sq_abs] at hx
  unfold frequencyWeight
  nlinarith [sq_nonneg Real.pi]

lemma derivativeSymbol_norm_sq_le {d m : ℕ} (α : Fin d → ℕ)
    (hα : (∑ i, α i) ≤ m) (ξ : Euclidean d) :
    ‖derivativeSymbol α ξ‖ ^ 2 ≤ frequencyWeight ξ ^ m := by
  unfold derivativeSymbol
  rw [norm_prod, ← Finset.prod_pow]
  calc
    ∏ i, ‖((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ α i‖ ^ 2 =
        ∏ i, (‖(2 * Real.pi * Complex.I) * (ξ i : ℂ)‖ ^ 2) ^ α i := by
      congr 1
      funext i
      rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ∏ i : Fin d, frequencyWeight ξ ^ α i := by
      exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (sq_nonneg _) _) fun i _ =>
        pow_le_pow_left₀ (sq_nonneg _) (coordinate_symbol_norm_sq ξ i) _
    _ = frequencyWeight ξ ^ (∑ i, α i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ frequencyWeight ξ ^ m := by
      apply pow_le_pow_right₀
      · unfold frequencyWeight
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg Real.pi)) (sq_nonneg ‖ξ‖)]
      · exact hα

lemma derivativeSymbol_hasTemperateGrowth {d : ℕ} (α : Fin d → ℕ) :
    (derivativeSymbol α).HasTemperateGrowth := by
  have h : ∀ s : Finset (Fin d),
      (fun ξ : Euclidean d => ∏ i ∈ s, ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ α i).HasTemperateGrowth := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Function.hasTemperateGrowth_const (1 : ℂ))
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      apply Function.HasTemperateGrowth.mul ?_ ih
      have hp : (fun ξ : Euclidean d => (ξ i : ℂ)).HasTemperateGrowth :=
        Complex.ofRealCLM.hasTemperateGrowth.comp (EuclideanSpace.proj i).hasTemperateGrowth
      fun_prop
  exact h Finset.univ

lemma derivativeSymbol_weight_norm_le {d m : ℕ} (α : Fin d → ℕ)
    (hα : (∑ i, α i) ≤ m) (ξ : Euclidean d) :
    ‖derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ‖ ≤ 1 := by
  have hs : ‖derivativeSymbol α ξ‖ ^ 2 ≤ weight (m : ℝ) ξ ^ 2 := by
    rw [weight_sq, Real.rpow_natCast]
    exact derivativeSymbol_norm_sq_le α hα ξ
  have h := (sq_le_sq₀ (norm_nonneg _) (weight_pos (m : ℝ) ξ).le).mp hs
  rw [norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos (-(m : ℝ)) ξ)]
  calc
    _ ≤ weight (m : ℝ) ξ * weight (-(m : ℝ)) ξ :=
      mul_le_mul_of_nonneg_right h (weight_pos _ _).le
    _ = 1 := by rw [mul_comm, weight_neg_mul]

lemma derivativeDensity_memLp {d m : ℕ} (α : Fin d → ℕ)
    (hα : (∑ i, α i) ≤ m) (u : Hs d (m : ℝ)) :
    MemLp (fun ξ => derivativeSymbol α ξ * fourierDensity u ξ) 2 volume := by
  apply (Lp.memLp (coordinates d (m : ℝ) u)).of_le
  · exact (derivativeSymbol_hasTemperateGrowth α).1.continuous.aestronglyMeasurable.mul
      ((complexWeight_hasTemperateGrowth (-(m : ℝ))).1.continuous.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (coordinates d (m : ℝ) u)))
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [fourierDensity, ← mul_assoc, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (derivativeSymbol_weight_norm_le α hα ξ)


open ExpandedFA.Distributions
open scoped _root_.Distributions

def euclideanDomainEquiv (d : ℕ) : Euclidean d ≃L[ℝ] Domain d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

def domainTestSchwartz {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (φ : Tests ℂ Ω) : Schwartz ℂ d :=
  (φ.hasCompactSupport.comp_homeomorph (euclideanDomainEquiv d).toHomeomorph).toSchwartzMap
    (φ.contDiff.comp (euclideanDomainEquiv d).contDiff)

@[simp] lemma domainTestSchwartz_apply {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (φ : Tests ℂ Ω) (x : Euclidean d) :
    domainTestSchwartz φ x = φ (WithLp.ofLp x) := rfl

lemma domainTestSchwartz_partial {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (φ : Tests ℂ Ω) (i : Fin d) :
    LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) (domainTestSchwartz φ) = domainTestSchwartz (testPartialCLM [i] φ) := by
  ext x
  rw [Inversion.partial_apply, domainTestSchwartz_apply, testPartial_single_apply]
  change fderiv ℝ (φ ∘ euclideanDomainEquiv d) x (basisVector i) = _
  rw [fderiv_comp (f := (euclideanDomainEquiv d : Euclidean d → Domain d)) (g := (φ : Domain d → ℂ)) x
    (φ.contDiff.differentiable (by simp) _) (euclideanDomainEquiv d).differentiableAt,
    ContinuousLinearEquiv.fderiv]
  rfl

lemma lpDistribution_euclideanToDomainL2 (d : ℕ) (f : L2 d)
    (φ : Tests ℂ (⊤ : TopologicalSpace.Opens (Domain d))) :
    lpDistribution (euclideanToDomainL2 d f) φ =
      Lp.toTemperedDistribution f (domainTestSchwartz φ) := by
  rw [lpDistribution_apply, Lp.toTemperedDistribution_apply]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  calc
    (∫ x, φ x * euclideanToDomainL2 d f x) =
        ∫ x, φ x * f (WithLp.toLp 2 x) := by
      apply integral_congr_ae
      filter_upwards [euclideanToDomainL2_coe d f] with x hx
      rw [hx]
    _ = _ := by
      simpa only [domainTestSchwartz_apply, WithLp.ofLp_toLp, smul_eq_mul] using
        (PiLp.volume_preserving_toLp (Fin d)).integral_comp
          (euclideanDomainEquiv d).symm.toHomeomorph.measurableEmbedding
          (fun x => domainTestSchwartz φ x * f x)

lemma regular_tempered_partial_to_weak {d : ℕ} (f g : L2 d) (i : Fin d)
    (h : Lp.toTemperedDistribution g = temperedPartial i (Lp.toTemperedDistribution f)) :
    lpDistribution (euclideanToDomainL2 d g) =
      -(lpDistribution (euclideanToDomainL2 d f)).comp (testPartialCLM [i]) := by
  ext φ
  simp only [neg_apply, ContinuousLinearMap.comp_apply]
  rw [lpDistribution_euclideanToDomainL2, lpDistribution_euclideanToDomainL2, h]
  change -Lp.toTemperedDistribution f
      (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) (domainTestSchwartz φ)) = _
  rw [domainTestSchwartz_partial]



def schwartzTestPartial {d : ℕ} : List (Fin d) → Schwartz ℂ d →L[ℂ] Schwartz ℂ d
  | [] => ContinuousLinearMap.id ℂ _
  | i :: w => (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)).comp
      (schwartzTestPartial w)

lemma domainTestSchwartz_word {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (w : List (Fin d)) (φ : Tests ℂ Ω) :
    schwartzTestPartial w (domainTestSchwartz φ) = domainTestSchwartz (testPartialCLM w φ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)
      (schwartzTestPartial w (domainTestSchwartz φ)) = _
    rw [ih, domainTestSchwartz_partial]
    rfl


lemma frequencyWeight_sum {d : ℕ} (ξ : Euclidean d) :
    frequencyWeight ξ = 1 + ∑ i, (2 * Real.pi * ξ i) ^ 2 := by
  unfold frequencyWeight
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma frequencyWeight_pow_bound_succ {d : ℕ} (m : ℕ) (ξ : Euclidean d) :
    frequencyWeight ξ ^ (m + 1) ≤ (d + 1 : ℝ) ^ m *
      (1 + ∑ i, ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) ^ (m + 1)‖ ^ 2) := by
  let f : Option (Fin d) → ℝ := fun o => match o with
    | none => 1
    | some i => (2 * Real.pi * ξ i) ^ 2
  have h := pow_sum_le_card_mul_sum_pow
    (s := Finset.univ) (f := f) (by intro i _; cases i <;> simp [f]; positivity) m
  have hp (i : Fin d) :
      ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) ^ (m + 1)‖ ^ 2 =
        ((2 * Real.pi * ξ i) ^ 2) ^ (m + 1) := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm (m + 1) 2, pow_mul]
    congr 1
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, mul_pow, sq_abs]
  simp only [Fintype.sum_option, f, one_pow, Fintype.card_option,
    Fintype.card_fin, Finset.card_univ, Nat.cast_add, Nat.cast_one] at h
  simpa only [frequencyWeight_sum, hp] using h


lemma derivativeSymbol_zero {d : ℕ} (ξ : Euclidean d) :
    derivativeSymbol (fun _ => 0) ξ = 1 := by
  simp [derivativeSymbol]

lemma derivativeSymbol_single {d : ℕ} (i : Fin d) (m : ℕ) (ξ : Euclidean d) :
    derivativeSymbol (Pi.single i m) ξ =
      ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ m := by
  classical
  simp [derivativeSymbol, Pi.single_apply]

lemma frequencyWeight_pow_le_symbol_sum {d : ℕ} (m : ℕ) (ξ : Euclidean d) :
    frequencyWeight ξ ^ m ≤ (d + 1 : ℝ) ^ (m + 1) *
      ∑ α : DerivativeIndex d m, ‖derivativeSymbol (natIndex α) ξ‖ ^ 2 := by
  classical
  let A := ∑ α : DerivativeIndex d m, ‖derivativeSymbol (natIndex α) ξ‖ ^ 2
  have hzero : 1 ≤ A := by
    have h := Finset.single_le_sum
      (fun (a : DerivativeIndex d m) _ => sq_nonneg ‖derivativeSymbol (natIndex a) ξ‖)
      (Finset.mem_univ (zeroIndex d m))
    simpa [natIndex, zeroIndex, derivativeSymbol, A] using h
  have hpure (i : Fin d) : ‖((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ m‖ ^ 2 ≤ A := by
    let α : DerivativeIndex d m := boundedIndex (Pi.single i m) (by simp)
    have h := Finset.single_le_sum
      (fun (a : DerivativeIndex d m) _ => sq_nonneg ‖derivativeSymbol (natIndex a) ξ‖)
      (Finset.mem_univ α)
    simpa only [α, natIndex_boundedIndex, derivativeSymbol_single, A] using h
  have hsum : 1 + ∑ i : Fin d, ‖((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ m‖ ^ 2 ≤
      (d + 1 : ℝ) * A := by
    calc
      _ ≤ A + ∑ _ : Fin d, A := add_le_add hzero (Finset.sum_le_sum fun i _ => hpure i)
      _ = _ := by simp; ring
  have hd : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  cases m with
  | zero =>
    simp only [pow_zero, zero_add, pow_one]
    exact hzero.trans (le_mul_of_one_le_left (le_trans (by norm_num) hzero) hd)
  | succ m =>
    have hpow := frequencyWeight_pow_bound_succ m ξ
    calc
      _ ≤ (d + 1 : ℝ) ^ m *
          (1 + ∑ i, ‖((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ (m + 1)‖ ^ 2) := hpow
      _ ≤ (d + 1 : ℝ) ^ m * ((d + 1 : ℝ) * A) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (d + 1 : ℝ) ^ (m + 1 + 1) * A := by
        rw [← mul_assoc, ← pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd (by omega))
          (le_trans (by norm_num) hzero)

lemma boundedMultiplier_memLp {d : ℕ} (g : Euclidean d → ℂ)
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (f : L2 d) :
    MemLp (fun ξ => g ξ * f ξ) 2 volume := by
  apply (Lp.memLp f).of_le_mul
    (hg.1.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) (c := C)
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖g ξ * f ξ‖ ≤ C * ‖f ξ‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

/-- Bounded multiplication on ordinary L². -/
def multiplierL2 {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (f : L2 d) : L2 d :=
  (boundedMultiplier_memLp g hg hC f).toLp (fun ξ => g ξ * f ξ)

lemma multiplierL2_coe {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (f : L2 d) :
    multiplierL2 g hg hC f =ᵐ[volume] fun ξ => g ξ * f ξ :=
  (boundedMultiplier_memLp g hg hC f).coeFn_toLp

lemma multiplierL2_add {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (f h : L2 d) :
    multiplierL2 g hg hC (f+h) = multiplierL2 g hg hC f + multiplierL2 g hg hC h := by
  apply Lp.ext
  filter_upwards [multiplierL2_coe g hg hC (f+h), multiplierL2_coe g hg hC f,
    multiplierL2_coe g hg hC h, Lp.coeFn_add (multiplierL2 g hg hC f) (multiplierL2 g hg hC h),
    Lp.coeFn_add f h] with ξ h₀ h₁ h₂ h₃ h₄
  rw [h₀, h₃]
  dsimp only [Pi.add_apply]
  rw [h₁, h₂, h₄]
  simp only [Pi.add_apply, mul_add]

lemma multiplierL2_smul {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (c : ℂ) (f : L2 d) :
    multiplierL2 g hg hC (c • f) = c • multiplierL2 g hg hC f := by
  apply Lp.ext
  filter_upwards [multiplierL2_coe g hg hC (c • f), multiplierL2_coe g hg hC f,
    Lp.coeFn_smul c (multiplierL2 g hg hC f), Lp.coeFn_smul c f] with ξ h₀ h₁ h₂ h₃
  rw [h₀, h₂]
  dsimp only [Pi.smul_apply]
  rw [h₁, h₃]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma multiplierL2_norm_le {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (f : L2 d) :
    ‖multiplierL2 g hg hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplierL2_coe g hg hC f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

/-- A bounded multiplier is a continuous scalar-linear map on L². -/
def multiplierL2CLM {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) : L2 d →L[ℂ] L2 d :=
  LinearMap.mkContinuous
    { toFun := multiplierL2 g hg hC
      map_add' := multiplierL2_add g hg hC
      map_smul' := multiplierL2_smul g hg hC }
    C (by
      intro f
      change ‖multiplierL2 g hg hC f‖ ≤ C * ‖f‖
      exact multiplierL2_norm_le g hg hC f)

lemma multiplierL2_distribution {d : ℕ} (g : Euclidean d → ℂ) (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ, ‖g ξ‖ ≤ C) (f : L2 d) :
    Lp.toTemperedDistribution (multiplierL2CLM g hg hC f) =
      TemperedDistribution.smulLeftCLM ℂ g (Lp.toTemperedDistribution f) := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [multiplierL2_coe g hg hC f] with ξ hξ
  change φ ξ * multiplierL2 g hg hC f ξ = _
  rw [hξ]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  ring


/-- The L² weak-derivative candidate represented by its exact Fourier symbol. -/
def derivativeL2CLM {d m : ℕ} (α : Fin d → ℕ) (hα : (∑ i, α i) ≤ m) :
    Hs d (m : ℝ) →L[ℂ] L2 d :=
  (l2Fourier d).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((multiplierL2CLM (fun ξ => derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ)
      ((derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _))
      (derivativeSymbol_weight_norm_le α hα)).comp
      (coordinates d (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)

lemma derivativeL2CLM_norm_le {d m : ℕ} (α : Fin d → ℕ) (hα : (∑ i, α i) ≤ m)
    (u : Hs d (m : ℝ)) : ‖derivativeL2CLM α hα u‖ ≤ ‖u‖ := by
  let g := fun ξ => derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ
  have hg : g.HasTemperateGrowth :=
    (derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _)
  have hC : ∀ ξ, ‖g ξ‖ ≤ 1 := derivativeSymbol_weight_norm_le α hα
  change ‖(l2Fourier d).symm (multiplierL2 g hg hC (coordinates d (m : ℝ) u))‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map, ← (coordinates d (m : ℝ)).norm_map u]
  simpa only [one_mul] using multiplierL2_norm_le
    (fun ξ => derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ)
    ((derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _))
    (derivativeSymbol_weight_norm_le α hα) (coordinates d (m : ℝ) u)

lemma derivativeL2CLM_distribution {d m : ℕ} (α : Fin d → ℕ) (hα : (∑ i, α i) ≤ m)
    (u : Hs d (m : ℝ)) :
    Lp.toTemperedDistribution (derivativeL2CLM α hα u) =
      TemperedDistribution.fourierMultiplierCLM ℂ (derivativeSymbol α) (realization u) := by
  let g := fun ξ => derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ
  have hg : g.HasTemperateGrowth :=
    (derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _)
  have hC : ∀ ξ, ‖g ξ‖ ≤ 1 := derivativeSymbol_weight_norm_le α hα
  change Lp.toTemperedDistribution ((l2Fourier d).symm
    (multiplierL2CLM g hg hC (coordinates d (m : ℝ) u))) = _
  have hinv : Lp.toTemperedDistribution ((l2Fourier d).symm
      (multiplierL2CLM g hg hC (coordinates d (m : ℝ) u))) =
      (𝓕⁻ (Lp.toTemperedDistribution
        (multiplierL2CLM g hg hC (coordinates d (m : ℝ) u))) : Tempered ℂ d) :=
    (Lp.fourierInv_toTemperedDistribution_eq _).symm
  rw [hinv, multiplierL2_distribution]
  change 𝓕⁻ _ = 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (derivativeSymbol α)
    (temperedFourier (realization u)))
  rw [fourier_realization,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (complexWeight_hasTemperateGrowth (-(m : ℝ))) (derivativeSymbol_hasTemperateGrowth α)]
  have hgcomm : g = complexWeight (-(m : ℝ)) * derivativeSymbol α := by
    funext ξ
    exact mul_comm _ _
  rw [hgcomm]


lemma derivativeL2CLM_zero {d m : ℕ} (u : Hs d (m : ℝ)) :
    derivativeL2CLM (fun _ : Fin d => 0) (by simp) u =
      underlyingL2 d (m : ℝ) (Nat.cast_nonneg m) u := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
      (μ := (volume : Measure (Euclidean d))) (p := 2)))
  change Lp.toTemperedDistribution _ = Lp.toTemperedDistribution _
  rw [derivativeL2CLM_distribution, ← realization_underlyingL2]
  have hsymbol : derivativeSymbol (fun _ : Fin d => 0) = fun _ => 1 := by
    funext ξ
    simp [derivativeSymbol]
  rw [hsymbol, TemperedDistribution.fourierMultiplierCLM_const]
  simp



def temperedWordDerivative {d : ℕ} : List (Fin d) → Tempered ℂ d → Tempered ℂ d
  | [], T => T
  | i :: w, T => temperedWordDerivative w (temperedPartial i T)

lemma temperedWordDerivative_apply {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d)
    (φ : Schwartz ℂ d) :
    temperedWordDerivative w T φ = (-1 : ℂ) ^ w.length * T (schwartzTestPartial w φ) := by
  induction w generalizing T with
  | nil => simp [temperedWordDerivative, schwartzTestPartial]
  | cons i w ih =>
    rw [temperedWordDerivative, ih]
    simp only [temperedPartial, neg_apply, ContinuousLinearMap.comp_apply,
      schwartzTestPartial, List.length_cons, pow_succ]
    ring

lemma regular_tempered_word_to_weak {d : ℕ} (f g : L2 d) (w : List (Fin d))
    (h : Lp.toTemperedDistribution g = temperedWordDerivative w (Lp.toTemperedDistribution f)) :
    lpDistribution (euclideanToDomainL2 d g) =
      distributionDerivative ℂ d ⊤ w (lpDistribution (euclideanToDomainL2 d f)) := by
  ext φ
  rw [distributionDerivative_apply]
  rw [lpDistribution_euclideanToDomainL2, lpDistribution_euclideanToDomainL2, h,
    temperedWordDerivative_apply, domainTestSchwartz_word]



def wordSymbol {d : ℕ} (w : List (Fin d)) (ξ : Euclidean d) : ℂ :=
  (w.map (fun i => (2 * Real.pi * Complex.I) * (ξ i : ℂ))).prod

lemma wordSymbol_hasTemperateGrowth {d : ℕ} (w : List (Fin d)) :
    (wordSymbol w).HasTemperateGrowth := by
  induction w with
  | nil =>
    change (fun _ : Euclidean d => (1 : ℂ)).HasTemperateGrowth
    exact Function.HasTemperateGrowth.const 1
  | cons i w ih =>
    change (fun ξ : Euclidean d => ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) * wordSymbol w ξ).HasTemperateGrowth
    exact ((Function.HasTemperateGrowth.const _).mul (coordinate_growth (𝕜 := ℂ) i)).mul ih

lemma fourier_temperedPartial_symbol {d : ℕ} (i : Fin d) (T : Tempered ℂ d) :
    temperedFourier (temperedPartial i T) =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : Euclidean d => (2 * Real.pi * Complex.I) * (ξ i : ℂ))
        (temperedFourier T) := by
  rw [fourier_partial]
  have hm := TemperedDistribution.smulLeftCLM_smul
    (F := ℂ) (g := fun ξ : Euclidean d => (ξ i : ℂ))
    (coordinate_growth (𝕜 := ℂ) i) (2 * Real.pi * Complex.I)
  have heq := congrArg
    (fun A : TemperedDistribution (Euclidean d) ℂ →L[ℂ]
      TemperedDistribution (Euclidean d) ℂ => A (temperedFourier T)) hm
  exact heq.symm

lemma fourier_temperedWordDerivative {d : ℕ} (w : List (Fin d)) (T : Tempered ℂ d) :
    temperedFourier (temperedWordDerivative w T) =
      TemperedDistribution.smulLeftCLM ℂ (wordSymbol w) (temperedFourier T) := by
  induction w generalizing T with
  | nil =>
    change temperedFourier T = TemperedDistribution.smulLeftCLM ℂ (fun _ : Euclidean d => 1) (temperedFourier T)
    simpa only [one_smul] using (TemperedDistribution.smulLeftCLM_const (F := ℂ) 1 (temperedFourier T)).symm
  | cons i w ih =>
    rw [temperedWordDerivative, ih, fourier_temperedPartial_symbol,
      TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
        (show (fun ξ : Euclidean d => (2 * Real.pi * Complex.I) * (ξ i : ℂ)).HasTemperateGrowth by
          exact (Function.HasTemperateGrowth.const _).mul (coordinate_growth (𝕜 := ℂ) i))
        (wordSymbol_hasTemperateGrowth w)]
    rfl

lemma wordSymbol_multiIndexWord {d : ℕ} (α : Fin d → ℕ) :
    wordSymbol (Distributions.multiIndexWord α) = derivativeSymbol α := by
  funext ξ
  simp [wordSymbol, Distributions.multiIndexWord, derivativeSymbol,
    List.map_flatMap, List.flatMap, List.map_ofFn, List.prod_ofFn, List.prod_flatten, Function.comp_def]

lemma fourier_temperedMultiIndexDerivative {d : ℕ} (α : Fin d → ℕ)
    (T : Tempered ℂ d) :
    temperedFourier (temperedWordDerivative (Distributions.multiIndexWord α) T) =
      TemperedDistribution.smulLeftCLM ℂ (derivativeSymbol α) (temperedFourier T) := by
  rw [fourier_temperedWordDerivative, wordSymbol_multiIndexWord]

lemma temperedMultiIndexDerivative_eq_multiplier {d : ℕ} (α : Fin d → ℕ)
    (T : Tempered ℂ d) :
    temperedWordDerivative (Distributions.multiIndexWord α) T =
      TemperedDistribution.fourierMultiplierCLM ℂ (derivativeSymbol α) T := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective
  change temperedFourier _ = temperedFourier _
  rw [fourier_temperedMultiIndexDerivative]
  change _ = 𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (derivativeSymbol α) (temperedFourier T)))
  rw [FourierTransform.fourier_fourierInv_eq]


/-- The finite derivative tuple of an element of the Fourier Hilbert model. -/
def derivativeTupleL2LM (d m : ℕ) :
    Hs d (m : ℝ) →ₗ[ℂ]
      DerivativeTuple ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) m 2 where
  toFun u := WithLp.toLp 1 (fun α : DerivativeIndex d m =>
    euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property u))
  map_add' u v := by
    apply PiLp.ext
    intro α
    change euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property (u + v)) =
      euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property u) +
        euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property v)
    rw [map_add, map_add]
  map_smul' c u := by
    apply PiLp.ext
    intro α
    change euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property (c • u)) =
      c • euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property u)
    rw [map_smul, map_smul]

lemma derivativeTupleL2_norm_le (d m : ℕ) (u : Hs d (m : ℝ)) :
    ‖derivativeTupleL2LM d m u‖ ≤ (Fintype.card (DerivativeIndex d m) : ℝ) * ‖u‖ := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _ : DerivativeIndex d m, ‖u‖ := by
      apply Finset.sum_le_sum
      intro α _
      change ‖euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property u)‖ ≤ ‖u‖
      rw [LinearIsometry.norm_map]
      exact derivativeL2CLM_norm_le _ _ u
    _ = _ := by simp

/-- All weak-derivative candidates, with the manuscript's sum norm. -/
def derivativeTupleL2CLM (d m : ℕ) :
    Hs d (m : ℝ) →L[ℂ]
      DerivativeTuple ℂ (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) m 2 :=
  (derivativeTupleL2LM d m).mkContinuous (Fintype.card (DerivativeIndex d m))
    (derivativeTupleL2_norm_le d m)

lemma derivativeTupleL2_zero (d m : ℕ) (u : Hs d (m : ℝ)) :
    derivativeTupleL2CLM d m u (zeroIndex d m) =
      euclideanToDomainL2 d (underlyingL2 d (m : ℝ) (Nat.cast_nonneg m) u) := by
  change euclideanToDomainL2 d
    (derivativeL2CLM (fun _ : Fin d => 0) (by simp) u) = _
  rw [derivativeL2CLM_zero]


lemma underlyingL2_injective {d : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    Function.Injective (underlyingL2 d s hs) := by
  intro u v huv
  apply realization_injective d s
  rw [realization_underlyingL2 hs u, realization_underlyingL2 hs v, huv]

lemma derivativeTupleL2_injective (d m : ℕ) :
    Function.Injective (derivativeTupleL2CLM d m) := by
  intro u v huv
  apply underlyingL2_injective (Nat.cast_nonneg m)
  apply (euclideanToDomainL2 d).injective
  have hzero := congrArg (fun v => v (zeroIndex d m)) huv
  simpa only [derivativeTupleL2_zero] using hzero


lemma derivativeTupleL2_mem_graph (d m : ℕ) (u : Hs d (m : ℝ)) :
    derivativeTupleL2CLM d m u ∈ derivativeGraph ℂ
      (⊤ : TopologicalSpace.Opens (Distributions.Domain d)) m 2 := by
  intro α
  change lpDistribution (euclideanToDomainL2 d
      (derivativeL2CLM (natIndex α) α.property u)) =
    distributionDerivative ℂ d ⊤ (multiIndexWord (natIndex α))
      (lpDistribution (derivativeTupleL2CLM d m u (zeroIndex d m)))
  rw [derivativeTupleL2_zero]
  apply regular_tempered_word_to_weak
  rw [← realization_underlyingL2, derivativeL2CLM_distribution]
  exact (temperedMultiIndexDerivative_eq_multiplier _ _).symm

/-- The actual weak-derivative graph of each nonnegative integer Fourier order. -/
def integerEmbedding (d m : ℕ) : Hs d (m : ℝ) →L[ℂ] IntegerSobolev d m :=
  (derivativeTupleL2CLM d m).codRestrict _ (derivativeTupleL2_mem_graph d m)

lemma integerEmbedding_norm_le (d m : ℕ) (u : Hs d (m : ℝ)) :
    ‖integerEmbedding d m u‖ ≤ (Fintype.card (DerivativeIndex d m) : ℝ) * ‖u‖ :=
  derivativeTupleL2_norm_le d m u

lemma integerEmbedding_injective (d m : ℕ) : Function.Injective (integerEmbedding d m) := by
  intro u v huv
  apply derivativeTupleL2_injective d m
  exact congrArg Subtype.val huv

lemma integerEmbedding_zero (d m : ℕ) (u : Hs d (m : ℝ)) :
    (integerEmbedding d m u).val (zeroIndex d m) =
      euclideanToDomainL2 d (underlyingL2 d (m : ℝ) (Nat.cast_nonneg m) u) :=
  derivativeTupleL2_zero d m u

lemma integerEmbedding_realization (d m : ℕ) (u : Hs d (m : ℝ)) (φ : Schwartz ℂ d) :
    realization u φ = ∫ x, φ x * ((integerEmbedding d m u).val (zeroIndex d m)) x := by
  rw [integerEmbedding_zero, realization_underlyingL2 (Nat.cast_nonneg m) u,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  have h := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae
    (euclideanToDomainL2_coe d (underlyingL2 d (m : ℝ) (Nat.cast_nonneg m) u))
  filter_upwards [h] with x hx
  exact congrArg (φ x * ·) hx.symm



def euclideanCompactTest {d : ℕ} (φ : Schwartz ℂ d) (hc : HasCompactSupport φ) :
    Tests ℂ (⊤ : TopologicalSpace.Opens (Domain d)) :=
  ⟨φ ∘ (euclideanDomainEquiv d).symm,
    by fun_prop,
    hc.comp_homeomorph (euclideanDomainEquiv d).symm.toHomeomorph,
    Set.subset_univ _⟩

lemma domainTestSchwartz_euclideanCompactTest {d : ℕ} (φ : Schwartz ℂ d)
    (hc : HasCompactSupport φ) :
    domainTestSchwartz (euclideanCompactTest φ hc) = φ := by
  ext x
  rfl


open Filter
open scoped Topology

lemma scaled_schwartz_growth {d : ℕ} (χ : Schwartz ℂ d) (R : ℝ) :
    (fun x : Euclidean d => χ (R⁻¹ • x)).HasTemperateGrowth :=
  χ.hasTemperateGrowth.comp (by fun_prop)

def cutoffSchwartz {d : ℕ} (χ ψ : Schwartz ℂ d) (R : ℝ) : Schwartz ℂ d :=
  SchwartzMap.smulLeftCLM ℂ (fun x => χ (R⁻¹ • x)) ψ

@[simp] lemma cutoffSchwartz_apply {d : ℕ} (χ ψ : Schwartz ℂ d) (R : ℝ) (x : Euclidean d) :
    cutoffSchwartz χ ψ R x = χ (R⁻¹ • x) * ψ x := by
  simp only [cutoffSchwartz, SchwartzMap.smulLeftCLM_apply_apply
    (scaled_schwartz_growth χ R), smul_eq_mul]

lemma scaled_schwartz_deriv_bound {d : ℕ} (χ : Schwartz ℂ d) (R : ℝ)
    (hR : 1 ≤ R) (n : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y => χ (R⁻¹ • y)) x‖ ≤
      SchwartzMap.seminorm ℂ 0 n χ := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [iteratedFDeriv_comp_const_smul R⁻¹ (χ.smooth n)]
  change ‖R⁻¹ ^ n • iteratedFDeriv ℝ n χ (R⁻¹ • x)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ R⁻¹ ^ n)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by positivity)
    ((inv_le_one₀ hR0).mpr hR))).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ n _)

lemma cutoffSchwartz_seminorm_bound {d : ℕ} (χ ψ : Schwartz ℂ d) (R : ℝ)
    (hR : 1 ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (cutoffSchwartz χ ψ R) ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℂ 0 i χ * SchwartzMap.seminorm ℂ k (n - i) ψ := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  have heq : (cutoffSchwartz χ ψ R : Euclidean d → ℂ) =
      fun y => χ (R⁻¹ • y) * ψ y := funext (cutoffSchwartz_apply χ ψ R)
  rw [heq]
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => χ (R⁻¹ • y)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) ψ x‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (ContinuousLinearMap.mul ℝ ℂ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
        (by fun_prop) (ψ.smooth ⊤) x (mod_cast le_top) (ContinuousLinearMap.opNorm_mul_le ..)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => χ (R⁻¹ • y)) x‖ *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ψ x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      · exact scaled_schwartz_deriv_bound χ R hR i x
      · exact SchwartzMap.le_seminorm ℂ k (n - i) ψ x

lemma schwartz_tail_seminorm_bound {d : ℕ} (f : Schwartz ℂ d) (R C : ℝ)
    (hR : 0 < R) (k n : ℕ)
    (hvan : ∀ x, ‖x‖ < R → f x = 0)
    (hC : SchwartzMap.seminorm ℂ (k + 1) n f ≤ C) :
    SchwartzMap.seminorm ℂ k n f ≤ C / R := by
  have hC0 : 0 ≤ C := (apply_nonneg _ _).trans hC
  apply SchwartzMap.seminorm_le_bound ℂ k n f (div_nonneg hC0 hR.le)
  intro x
  by_cases hx : ‖x‖ < R
  · have heq : (f : Euclidean d → ℂ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx)] with y hy
      exact hvan y hy
    have hd := (heq.iteratedFDeriv (𝕜 := ℝ) n).self_of_nhds
    simp only [Pi.zero_apply, iteratedFDeriv_zero] at hd
    rw [hd, norm_zero, mul_zero]
    positivity
  · rw [le_div_iff₀ hR]
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ * R ≤
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (le_of_not_gt hx) (by positivity)
      _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f x‖ := by rw [pow_succ]; ring
      _ ≤ C := (SchwartzMap.le_seminorm ℂ (k + 1) n f x).trans hC

lemma schwartz_tendsto_zero_of_tail_bound {d : ℕ} (u : ℝ → Schwartz ℂ d)
    (hvan : ∀ R ≥ 1, ∀ x, ‖x‖ < R → u R x = 0)
    (hbound : ∀ k n, ∃ C : ℝ, ∀ R ≥ 1,
      SchwartzMap.seminorm ℂ k n (u R) ≤ C) :
    Tendsto u atTop (𝓝 0) := by
  apply (schwartz_withSeminorms ℂ (Euclidean d) ℂ).tendsto_nhds u 0 |>.mpr
  intro p ε hε
  obtain ⟨C, hC⟩ := hbound (p.1 + 1) p.2
  have hC0 : 0 ≤ C := (apply_nonneg _ (u 1)).trans (hC 1 le_rfl)
  filter_upwards [eventually_ge_atTop (max 1 (C / ε + 1))] with R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  change SchwartzMap.seminorm ℂ p.1 p.2 (u R - 0) < ε
  rw [sub_zero]
  apply lt_of_le_of_lt (schwartz_tail_seminorm_bound (u R) R C hR0 p.1 p.2
    (hvan R hR1) (hC R hR1))
  rw [div_lt_iff₀ hR0]
  have hR' : C / ε + 1 ≤ R := (le_max_right _ _).trans hR
  have : C / ε < R := lt_of_lt_of_le (lt_add_one _) hR'
  exact (div_lt_iff₀ hε).mp this |>.trans_eq (mul_comm R ε)

lemma cutoffSchwartz_tendsto {d : ℕ} (χ ψ : Schwartz ℂ d)
    (hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1) :
    Tendsto (fun R : ℝ => cutoffSchwartz χ ψ R) atTop (𝓝 ψ) := by
  have hzero : Tendsto (fun R : ℝ => cutoffSchwartz χ ψ R - ψ) atTop (𝓝 0) := by
    apply schwartz_tendsto_zero_of_tail_bound
    · intro R hR x hx
      rw [sub_apply, cutoffSchwartz_apply, hχ, one_mul, sub_self]
      have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
      exact le_of_lt ((inv_mul_lt_iff₀ hR0).mpr (by simpa only [mul_one] using hx))
    · intro k n
      refine ⟨(∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℂ 0 i χ * SchwartzMap.seminorm ℂ k (n - i) ψ) +
          SchwartzMap.seminorm ℂ k n ψ, ?_⟩
      intro R hR
      exact (map_sub_le_add (SchwartzMap.seminorm ℂ k n) _ _).trans
        (add_le_add (cutoffSchwartz_seminorm_bound χ ψ R hR k n) le_rfl)
  simpa only [sub_add_cancel, zero_add] using hzero.add_const ψ

lemma cutoffSchwartz_hasCompactSupport {d : ℕ} (χ ψ : Schwartz ℂ d)
    (hχ : HasCompactSupport (χ : Euclidean d → ℂ)) (R : ℝ) (hR : R ≠ 0) :
    HasCompactSupport (cutoffSchwartz χ ψ R : Euclidean d → ℂ) := by
  have h := (hχ.comp_smul (inv_ne_zero hR)).mul_right (f' := (ψ : Euclidean d → ℂ))
  have heq : (cutoffSchwartz χ ψ R : Euclidean d → ℂ) =
      (fun x => χ (R⁻¹ • x)) * (ψ : Euclidean d → ℂ) := by
    ext x
    exact cutoffSchwartz_apply χ ψ R x
  rw [heq]
  exact h

lemma exists_schwartz_cutoff (d : ℕ) : ∃ χ : Schwartz ℂ d,
    HasCompactSupport (χ : Euclidean d → ℂ) ∧ ∀ x, ‖x‖ ≤ 1 → χ x = 1 := by
  let b : ContDiffBump (0 : Euclidean d) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : HasCompactSupport (fun x => (b x : ℂ)) := by
    exact b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let χ : Schwartz ℂ d := hb.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨χ, hb, ?_⟩
  intro x hx
  change (b x : ℂ) = 1
  rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)]
  norm_num

lemma tempered_eq_zero_of_compact_tests {d : ℕ} (T : Tempered ℂ d)
    (hT : ∀ φ : Schwartz ℂ d, HasCompactSupport (φ : Euclidean d → ℂ) → T φ = 0) :
    T = 0 := by
  obtain ⟨χ, hχsupp, hχone⟩ := exists_schwartz_cutoff d
  ext ψ
  have ht : Tendsto (fun R : ℝ => T (cutoffSchwartz χ ψ R)) atTop (𝓝 (T ψ)) :=
    T.continuous.continuousAt.tendsto.comp (cutoffSchwartz_tendsto χ ψ hχone)
  have heq : (fun R : ℝ => T (cutoffSchwartz χ ψ R)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hT _ (cutoffSchwartz_hasCompactSupport χ ψ hχsupp R
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hR)))
  have hlim : Tendsto (fun R : ℝ => T (cutoffSchwartz χ ψ R)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique ht hlim

lemma regularMultiplier_ae_eq {d : ℕ} (p : Euclidean d → ℂ)
    (hp : p.HasTemperateGrowth) (f g : L2 d)
    (h : Lp.toTemperedDistribution g =
      TemperedDistribution.smulLeftCLM ℂ p (Lp.toTemperedDistribution f)) :
    g =ᵐ[volume] fun x => p x * f x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp g).locallyIntegrable (by norm_num))
    (((Lp.memLp f).locallyIntegrable (by norm_num)).continuous_mul hp.1.continuous)
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hψ' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let φ : Schwartz ℂ d := hc'.toSchwartzMap hψ'
  have he := congrArg (fun T : Tempered ℂ d => T φ) h
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at he
  simp only [SchwartzMap.smulLeftCLM_apply_apply hp, smul_eq_mul] at he
  change (∫ x, (ψ x : ℂ) * g x) = ∫ x, (p x * (ψ x : ℂ)) * f x at he
  simpa only [Complex.real_smul, mul_assoc, mul_left_comm] using he

lemma weak_to_regular_tempered_word {d : ℕ} (f g : L2 d) (w : List (Fin d))
    (h : lpDistribution (euclideanToDomainL2 d g) =
      distributionDerivative ℂ d ⊤ w (lpDistribution (euclideanToDomainL2 d f))) :
    Lp.toTemperedDistribution g = temperedWordDerivative w (Lp.toTemperedDistribution f) := by
  apply sub_eq_zero.mp
  apply tempered_eq_zero_of_compact_tests
  intro φ hc
  have hp := congrArg (fun T : ScalarDistribution ℂ
      (⊤ : TopologicalSpace.Opens (Domain d)) => T (euclideanCompactTest φ hc)) h
  rw [distributionDerivative_apply, lpDistribution_euclideanToDomainL2,
    lpDistribution_euclideanToDomainL2, ← domainTestSchwartz_word,
    domainTestSchwartz_euclideanCompactTest] at hp
  simp only [sub_apply, temperedWordDerivative_apply]
  exact sub_eq_zero.mpr hp

lemma sobolev_fourier_derivative_ae {d m : ℕ} (u : IntegerSobolev d m)
    (α : DerivativeIndex d m) :
    l2Fourier d (domainToEuclideanL2 d (u.val α)) =ᵐ[volume]
      fun ξ => derivativeSymbol (natIndex α) ξ *
        l2Fourier d (domainToEuclideanL2 d (u.val (zeroIndex d m))) ξ := by
  apply regularMultiplier_ae_eq _ (derivativeSymbol_hasTemperateGrowth _) 
  have h := weak_to_regular_tempered_word
    (domainToEuclideanL2 d (u.val (zeroIndex d m)))
    (domainToEuclideanL2 d (u.val α)) (multiIndexWord (natIndex α))
    (by
      rw [euclideanToDomainL2_rightInverse d _, euclideanToDomainL2_rightInverse d _]
      exact u.property α)
  have hf := congrArg (fun T : Tempered ℂ d => temperedFourier T) h
  rw [fourier_temperedMultiIndexDerivative] at hf
  change 𝓕 (Lp.toTemperedDistribution (domainToEuclideanL2 d (u.val α))) =
    TemperedDistribution.smulLeftCLM ℂ (derivativeSymbol (natIndex α))
      (𝓕 (Lp.toTemperedDistribution (domainToEuclideanL2 d (u.val (zeroIndex d m))))) at hf
  rw [Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at hf
  exact hf


lemma complexWeight_nat_norm_sq {d : ℕ} (m : ℕ) (ξ : Euclidean d) :
    ‖complexWeight (m : ℝ) ξ‖ ^ 2 = frequencyWeight ξ ^ m := by
  have hpos : 0 < frequencyWeight ξ := by unfold frequencyWeight; positivity
  rw [complexWeight, Complex.norm_real, Real.norm_eq_abs,
    weight, abs_of_pos (Real.rpow_pos_of_pos hpos _),
    ← Real.rpow_mul_natCast hpos.le]
  have hm : (m : ℝ) / 2 * (2 : ℕ) = m := by push_cast; ring
  rw [hm, Real.rpow_natCast]

lemma weighted_memLp_of_derivatives {d : ℕ} (m : ℕ) (f : Euclidean d → ℂ)
    (hw : AEStronglyMeasurable (complexWeight (d := d) (m : ℝ)) volume)
    (h : ∀ α : DerivativeIndex d m,
      MemLp (fun ξ => derivativeSymbol (natIndex α) ξ * f ξ) 2 volume) :
    MemLp (fun ξ => complexWeight (m : ℝ) ξ * f ξ) 2 volume := by
  have hf : MemLp f 2 volume := by
    simpa [derivativeSymbol, natIndex, zeroIndex] using h (zeroIndex d m)
  have hmeas := hw.mul hf.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hdom : Integrable (fun ξ => (d + 1 : ℝ) ^ (m + 1) *
      ∑ α : DerivativeIndex d m, ‖derivativeSymbol (natIndex α) ξ * f ξ‖ ^ 2) volume :=
    (integrable_finsetSum _ (fun α _ => (h α).integrable_norm_pow (by norm_num))).const_mul _
  apply hdom.mono' (hmeas.norm.pow 2)
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖‖complexWeight (m : ℝ) ξ * f ξ‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow,
      complexWeight_nat_norm_sq]
    calc
      _ ≤ ((d + 1 : ℝ) ^ (m + 1) *
          ∑ α : DerivativeIndex d m, ‖derivativeSymbol (natIndex α) ξ‖ ^ 2) * ‖f ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (frequencyWeight_pow_le_symbol_sum m ξ) (sq_nonneg _)
      _ = _ := by simp_rw [norm_mul, mul_pow, mul_assoc, Finset.sum_mul]

lemma regularL2_hasFourierDensity {d : ℕ} (f : L2 d) :
    HasFourierDensity (Lp.toTemperedDistribution f) (l2Fourier d f) := by
  constructor
  · exact (Lp.memLp (l2Fourier d f)).locallyIntegrable (by norm_num)
  · intro φ
    refine ⟨(φ.memLp 2).integrable_mul (Lp.memLp (l2Fourier d f)), ?_⟩
    change 𝓕 (Lp.toTemperedDistribution f) φ = _
    rw [Lp.fourier_toTemperedDistribution_eq, Lp.toTemperedDistribution_apply]
    rfl

lemma integerEmbedding_surjective (d m : ℕ) : Function.Surjective (integerEmbedding d m) := by
  intro v
  let f := domainToEuclideanL2 d (v.val (zeroIndex d m))
  have hw : MemLp (fun ξ => complexWeight (m : ℝ) ξ * l2Fourier d f ξ) 2 volume := by
    apply weighted_memLp_of_derivatives m _
      (complexWeight_hasTemperateGrowth (m : ℝ)).1.continuous.aestronglyMeasurable
    intro α
    exact (memLp_congr_ae (sobolev_fourier_derivative_ae v α)).mp (Lp.memLp _)
  obtain ⟨u, hu⟩ := (realization_image d (m : ℝ) (Lp.toTemperedDistribution f)).mpr
    ⟨l2Fourier d f, regularL2_hasFourierDensity f, hw⟩
  refine ⟨u, ?_⟩
  apply sobolev_underlying_injective ℂ d ⊤ m 2
  change (integerEmbedding d m u).val (zeroIndex d m) = v.val (zeroIndex d m)
  rw [integerEmbedding_zero]
  have heq : underlyingL2 d (m : ℝ) (Nat.cast_nonneg m) u = f := by
    apply (LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
        (μ := (volume : Measure (Euclidean d))) (p := 2)))
    change Lp.toTemperedDistribution _ = Lp.toTemperedDistribution _
    rw [← realization_underlyingL2]
    exact hu
  rw [heq]
  exact euclideanToDomainL2_rightInverse d _



lemma weighted_norm_sq_eq {d : ℕ} (m : ℕ) (F : L2 d) (ξ : Euclidean d) :
    ‖complexWeight (m : ℝ) ξ * F ξ‖ ^ 2 = frequencyWeight ξ ^ m * ‖F ξ‖ ^ 2 := by
  rw [norm_mul, complexWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos (m : ℝ) ξ), mul_pow, weight_sq, Real.rpow_natCast]

lemma weighted_density_norm_bound {d m : ℕ} (F : L2 d)
    (g : DerivativeIndex d m → L2 d) (ξ : Euclidean d)
    (hg : ∀ α, g α ξ = derivativeSymbol (natIndex α) ξ * F ξ) :
    ‖complexWeight (m : ℝ) ξ * F ξ‖ ≤
      (d + 1 : ℝ) ^ (m + 1) * ∑ α, ‖g α ξ‖ := by
  let C : ℝ := (d + 1 : ℝ) ^ (m + 1)
  have hC : 1 ≤ C := one_le_pow₀ (by have hd := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun α => ‖g α ξ‖) (by intro i _; positivity)
  have hbound := mul_le_mul_of_nonneg_right (frequencyWeight_pow_le_symbol_sum m ξ)
    (sq_nonneg ‖F ξ‖)
  rw [mul_assoc, Finset.sum_mul] at hbound
  have heq : (∑ α : DerivativeIndex d m, ‖derivativeSymbol (natIndex α) ξ‖ ^ 2 * ‖F ξ‖ ^ 2) =
      ∑ α, ‖g α ξ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro α _
    rw [hg, norm_mul, mul_pow]
  rw [heq] at hbound
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (by positivity))).mp
  rw [weighted_norm_sq_eq, mul_pow]
  calc
    _ ≤ C * ∑ α, ‖g α ξ‖ ^ 2 := hbound
    _ ≤ C * (∑ α, ‖g α ξ‖) ^ 2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C ^ 2 * (∑ α, ‖g α ξ‖) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)

lemma weighted_density_memLp {d m : ℕ} (F : L2 d)
    (g : DerivativeIndex d m → L2 d)
    (hg : ∀ α, g α =ᵐ[volume] fun ξ => derivativeSymbol (natIndex α) ξ * F ξ) :
    MemLp (fun ξ => complexWeight (m : ℝ) ξ * F ξ) 2 volume := by
  have hsum : MemLp (fun ξ => ∑ α, ‖g α ξ‖) 2 volume := by
    convert memLp_finsetSum' Finset.univ (fun α _ => (Lp.memLp (g α)).norm) using 1
    funext ξ
    simp
  apply hsum.of_le_mul
  · exact (complexWeight_hasTemperateGrowth (m : ℝ)).1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable F)
  · filter_upwards [ae_all_iff.mpr hg] with ξ hξ
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun α _ => norm_nonneg _))] using
      weighted_density_norm_bound F g ξ hξ



lemma norm_sum_norms_toLp_le {d : ℕ} {ι : Type} [Fintype ι] (g : ι → L2 d)
    (hG : MemLp (fun ξ => ∑ i, ‖g i ξ‖) 2 volume) :
    ‖hG.toLp (fun ξ => ∑ i, ‖g i ξ‖)‖ ≤ ∑ i, ‖g i‖ := by
  rw [Lp.norm_toLp]
  have he : eLpNorm (fun ξ => ∑ i, ‖g i ξ‖) 2 volume ≤ ∑ i, eLpNorm (g i) 2 volume := by
    have heq : (fun ξ => ∑ i, ‖g i ξ‖) = ∑ i, (fun ξ => ‖g i ξ‖) := by
      funext ξ
      simp
    rw [heq]
    calc
      _ ≤ ∑ i, eLpNorm (fun ξ => ‖g i ξ‖) 2 volume := eLpNorm_sum_le (by norm_num)
      _ = _ := by simp only [eLpNorm_norm _ (Lp.aestronglyMeasurable _)]
  have hfin : (∑ i, eLpNorm (g i) 2 volume) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => Lp.eLpNorm_ne_top (g i))
  calc
    _ ≤ (∑ i, eLpNorm (g i) 2 volume).toReal := ENNReal.toReal_mono hfin he
    _ = ∑ i, ‖g i‖ := by
      rw [ENNReal.toReal_sum (fun i _ => Lp.eLpNorm_ne_top (g i))]
      simp only [Lp.norm_def]

lemma weighted_density_norm_toLp_le {d m : ℕ} (F : L2 d)
    (g : DerivativeIndex d m → L2 d)
    (hg : ∀ α, g α =ᵐ[volume] fun ξ => derivativeSymbol (natIndex α) ξ * F ξ) :
    ‖(weighted_density_memLp F g hg).toLp
      (fun ξ => complexWeight (m : ℝ) ξ * F ξ)‖ ≤
      (d + 1 : ℝ) ^ (m + 1) * ∑ α, ‖g α‖ := by
  have hsum : MemLp (fun ξ => ∑ α, ‖g α ξ‖) 2 volume := by
    convert memLp_finsetSum' Finset.univ (fun α _ => (Lp.memLp (g α)).norm) using 1
    funext ξ
    simp
  have hb : ‖(weighted_density_memLp F g hg).toLp
      (fun ξ => complexWeight (m : ℝ) ξ * F ξ)‖ ≤
      (d + 1 : ℝ) ^ (m + 1) * ‖hsum.toLp (fun ξ => ∑ α, ‖g α ξ‖)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(weighted_density_memLp F g hg).coeFn_toLp, hsum.coeFn_toLp,
      ae_all_iff.mpr hg] with ξ hξ hsumξ hgξ
    rw [hξ, hsumξ, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun α _ => norm_nonneg _))]
    exact weighted_density_norm_bound F g ξ hgξ
  exact hb.trans (mul_le_mul_of_nonneg_left (norm_sum_norms_toLp_le g hsum) (by positivity))


lemma derivativeL2CLM_fourier_coe {d m : ℕ} (α : Fin d → ℕ)
    (hα : (∑ i, α i) ≤ m) (u : Hs d (m : ℝ)) :
    l2Fourier d (derivativeL2CLM α hα u) =ᵐ[volume]
      fun ξ => derivativeSymbol α ξ * fourierDensity u ξ := by
  let g := fun ξ => derivativeSymbol α ξ * complexWeight (-(m : ℝ)) ξ
  have hg : g.HasTemperateGrowth :=
    (derivativeSymbol_hasTemperateGrowth α).mul (complexWeight_hasTemperateGrowth _)
  have hC : ∀ ξ, ‖g ξ‖ ≤ 1 := derivativeSymbol_weight_norm_le α hα
  have heq : l2Fourier d (derivativeL2CLM α hα u) =
      multiplierL2CLM g hg hC (coordinates d (m : ℝ) u) := by
    change l2Fourier d ((l2Fourier d).symm _) = _
    exact LinearIsometryEquiv.apply_symm_apply _ _
  rw [heq]
  filter_upwards [multiplierL2_coe g hg hC (coordinates d (m : ℝ) u)] with ξ hξ
  change multiplierL2 g hg hC (coordinates d (m : ℝ) u) ξ = _
  rw [hξ]
  simp only [g, fourierDensity]
  ring

lemma integerEmbedding_coordinate_norm {d m : ℕ} (α : DerivativeIndex d m)
    (u : Hs d (m : ℝ)) :
    ‖l2Fourier d (derivativeL2CLM (natIndex α) α.property u)‖ =
      ‖(integerEmbedding d m u).val α‖ := by
  rw [LinearIsometryEquiv.norm_map]
  change ‖derivativeL2CLM (natIndex α) α.property u‖ =
    ‖euclideanToDomainL2 d (derivativeL2CLM (natIndex α) α.property u)‖
  rw [LinearIsometry.norm_map]

lemma integerEmbedding_fourier_norm_sum (d m : ℕ) (u : Hs d (m : ℝ)) :
    (∑ α : DerivativeIndex d m,
      ‖l2Fourier d (derivativeL2CLM (natIndex α) α.property u)‖) =
      ‖integerEmbedding d m u‖ := by
  simp only [integerEmbedding_coordinate_norm]
  exact (sobolev_norm_formula ℂ d ⊤ m 2 (integerEmbedding d m u)).symm

/-- Explicit inverse bounds suffice; no completeness assumption on the graph is needed. -/
lemma integerEquiv_of_surjective_bound (d m : ℕ)
    (hsurj : Function.Surjective (integerEmbedding d m)) (C : ℝ)
    (hbound : ∀ u : Hs d (m : ℝ), ‖u‖ ≤ C * ‖integerEmbedding d m u‖) :
    ∃ e : Hs d (m : ℝ) ≃L[ℂ] IntegerSobolev d m,
      ∀ (u : Hs d (m : ℝ)) (φ : Schwartz ℂ d),
        realization u φ = ∫ x, φ x * ((e u).val (zeroIndex d m)) x := by
  let e := LinearEquiv.ofBijective (integerEmbedding d m).toLinearMap
    ⟨integerEmbedding_injective d m, hsurj⟩
  have hinv : ∀ v : IntegerSobolev d m, ‖e.symm v‖ ≤ C * ‖v‖ := by
    intro v
    have h := hbound (e.symm v)
    change ‖e.symm v‖ ≤ C * ‖e (e.symm v)‖ at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  let eL : Hs d (m : ℝ) ≃L[ℂ] IntegerSobolev d m :=
    { e with
      continuous_toFun := (integerEmbedding d m).continuous
      continuous_invFun := (e.symm.toLinearMap.mkContinuous C hinv).continuous }
  exact ⟨eL, integerEmbedding_realization d m⟩


lemma weighted_fourierDensityL2_eq_coordinates {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (u : Hs d s) :
    (fun ξ => complexWeight s ξ * fourierDensityL2 hs u ξ) =ᵐ[volume]
      coordinates d s u := by
  filter_upwards [fourierDensityL2_coe hs u] with ξ hξ
  rw [hξ, weighted_density_eq_coordinates]

lemma weighted_fourierDensityL2_toLp {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : Hs d s)
    (h : MemLp (fun ξ => complexWeight s ξ * fourierDensityL2 hs u ξ) 2 volume) :
    h.toLp (fun ξ => complexWeight s ξ * fourierDensityL2 hs u ξ) = coordinates d s u := by
  apply Lp.ext
  exact h.coeFn_toLp.trans (weighted_fourierDensityL2_eq_coordinates hs u)

lemma integerEmbedding_fourier_family (d m : ℕ) (u : Hs d (m : ℝ))
    (α : DerivativeIndex d m) :
    l2Fourier d (derivativeL2CLM (natIndex α) α.property u) =ᵐ[volume]
      fun ξ => derivativeSymbol (natIndex α) ξ *
        fourierDensityL2 (Nat.cast_nonneg m) u ξ := by
  filter_upwards [derivativeL2CLM_fourier_coe (natIndex α) α.property u,
    fourierDensityL2_coe (Nat.cast_nonneg m) u] with ξ h₁ h₂
  rw [h₁, h₂]


lemma integerEmbedding_lower_bound (d m : ℕ) (u : Hs d (m : ℝ)) :
    ‖u‖ ≤ (d + 1 : ℝ) ^ (m + 1) * ‖integerEmbedding d m u‖ := by
  let F := fourierDensityL2 (Nat.cast_nonneg m) u
  let g := fun α : DerivativeIndex d m =>
    l2Fourier d (derivativeL2CLM (natIndex α) α.property u)
  have hg : ∀ α, g α =ᵐ[volume] fun ξ => derivativeSymbol (natIndex α) ξ * F ξ :=
    integerEmbedding_fourier_family d m u
  have hb := weighted_density_norm_toLp_le F g hg
  dsimp only [F, g] at hb
  rw [weighted_fourierDensityL2_toLp] at hb
  change ‖u‖ ≤ (d + 1 : ℝ) ^ (m + 1) *
    (∑ α : DerivativeIndex d m, ‖l2Fourier d (derivativeL2CLM (natIndex α) α.property u)‖) at hb
  rw [integerEmbedding_fourier_norm_sum] at hb
  exact hb


/-- Integer Fourier orders are the actual weak-derivative Sobolev graph,
with equivalent norms under the identity on regular distributions. -/
theorem integer : Specs.ExpandedFA.Sobolev.FourierHilbertScale.integerType := by
  intro d m
  exact integerEquiv_of_surjective_bound d m (integerEmbedding_surjective d m)
    ((d + 1 : ℝ) ^ (m + 1)) (integerEmbedding_lower_bound d m)

end ExpandedFA.Sobolev.FourierScale

namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

lemma conj_fourier {d : ℕ} (φ : Schwartz ℂ d) (ξ : Euclidean d) :
    star (schwartzFourier φ ξ) = schwartzFourier (conjSchwartz φ) (-ξ) := by
  rw [ExpandedFA.Fourier.schwartz_integral, ExpandedFA.Fourier.schwartz_integral]
  unfold integralFourier
  change (starRingEnd ℂ) (∫ x, _) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [starRingEnd_apply, map_mul, conjSchwartz_apply, inner_neg_right,
    Complex.ofReal_neg]
  congr 1
  calc
    star (Complex.exp _) = Complex.exp (star _) := (Complex.exp_conj _).symm
    _ = _ := by congr 1; simp

lemma conj_fourierInv {d : ℕ} (φ : Schwartz ℂ d) (ξ : Euclidean d) :
    star ((𝓕⁻ φ : Schwartz ℂ d) ξ) = (𝓕⁻ (conjSchwartz φ) : Schwartz ℂ d) (-ξ) := by
  change star (schwartzFourier φ (-ξ)) = schwartzFourier (conjSchwartz φ) (-(-ξ))
  exact conj_fourier φ (-ξ)

lemma realConjugationL2_coe (d : ℕ) (f : L2 d) :
    realConjugationL2 d f =ᵐ[volume] fun ξ => star (f ξ) :=
  ContinuousLinearMap.coeFn_compLp Complex.conjCLE.toContinuousLinearMap f

lemma realConjugateReflectionL2_coe (d : ℕ) (f : L2 d) :
    realConjugateReflectionL2 d f =ᵐ[volume] fun ξ => star (f (-ξ)) := by
  unfold realConjugateReflectionL2
  change realConjugationL2 d _ =ᵐ[volume] _
  filter_upwards [realConjugationL2_coe d
    (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : Euclidean d => -ξ)
      (Measure.measurePreserving_neg volume) f),
    Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)] with ξ h₁ h₂
  change (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : Euclidean d => -ξ)
    (Measure.measurePreserving_neg volume) f) ξ = f (-ξ) at h₂
  change (realConjugationL2 d (Lp.compMeasurePreservingₗᵢ ℝ
    (fun ξ : Euclidean d => -ξ) (Measure.measurePreserving_neg volume) f)) ξ = _
  exact h₁.trans (congrArg star h₂)

lemma realConjugationL2_involutive (d : ℕ) :
    Function.Involutive (realConjugationL2 d) := by
  intro f
  apply Lp.ext
  filter_upwards [realConjugationL2_coe d (realConjugationL2 d f),
    realConjugationL2_coe d f] with ξ h₁ h₂
  simp only [h₁, h₂, star_star]

lemma realConjugateReflectionL2_involutive (d : ℕ) :
    Function.Involutive (realConjugateReflectionL2 d) := by
  intro f
  apply Lp.ext
  filter_upwards [realConjugateReflectionL2_coe d (realConjugateReflectionL2 d f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae
      (realConjugateReflectionL2_coe d f)] with ξ h₁ h₂
  simpa only [h₁, h₂, neg_neg, star_star]

@[simp] lemma realConjugateReflectionL2_norm (d : ℕ) (f : L2 d) :
    ‖realConjugateReflectionL2 d f‖ = ‖f‖ :=
  (realConjugateReflectionL2 d).norm_map f

lemma hermitianL2_mem_iff (d : ℕ) (f : L2 d) :
    f ∈ hermitianL2 d ↔ realConjugateReflectionL2 d f = f := by
  simp [hermitianL2, sub_eq_zero]

lemma hermitianL2_mem_iff_ae (d : ℕ) (f : L2 d) :
    f ∈ hermitianL2 d ↔ ∀ᵐ ξ ∂volume, f (-ξ) = star (f ξ) := by
  rw [hermitianL2_mem_iff]
  constructor
  · intro h
    filter_upwards [realConjugateReflectionL2_coe d f] with ξ hξ
    rw [h] at hξ
    simpa only [star_star] using congrArg star hξ.symm
  · intro h
    apply Lp.ext
    filter_upwards [realConjugateReflectionL2_coe d f, h] with ξ h₁ h₂
    simp only [h₁, h₂, star_star]

lemma realCoordinates_hermitian {d : ℕ} {s : ℝ} (u : RealHs d s) :
    ∀ᵐ ξ ∂volume, realCoordinates d s u (-ξ) = star (realCoordinates d s u ξ) :=
  (hermitianL2_mem_iff_ae d _).mp u.property

lemma realCoordinates_fixed {d : ℕ} {s : ℝ} (u : RealHs d s) :
    realConjugateReflectionL2 d (realCoordinates d s u) = realCoordinates d s u :=
  (hermitianL2_mem_iff d _).mp u.property

/-- A Hermitian L² coordinate defines a real Sobolev element of every order. -/
def realHsOfHermitian {d : ℕ} (s : ℝ) (f : L2 d)
    (hf : ∀ᵐ ξ ∂volume, f (-ξ) = star (f ξ)) : RealHs d s :=
  ⟨f, (hermitianL2_mem_iff_ae d f).mpr hf⟩

@[simp] lemma realCoordinates_realHsOfHermitian {d : ℕ} (s : ℝ) (f : L2 d)
    (hf : ∀ᵐ ξ ∂volume, f (-ξ) = star (f ξ)) :
    realCoordinates d s (realHsOfHermitian s f hf) = f := rfl

@[simp] lemma realCoordinates_bessel {d : ℕ} (s t : ℝ) (u : RealHs d s) :
    realCoordinates d (s-t) (realBesselIsometry d s t u) = realCoordinates d s u := rfl

lemma realCoordinates_injective (d : ℕ) (s : ℝ) :
    Function.Injective (realCoordinates d s) :=
  (realCoordinates d s).injective


lemma realization_integral {d : ℕ} {s : ℝ} (u : Hs d s) (φ : Schwartz ℂ d) :
    realization u φ = ∫ ξ, (𝓕⁻ φ : Schwartz ℂ d) ξ * (complexWeight (-s) ξ * coordinates d s u ξ) := by
  change TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
    (Lp.toTemperedDistribution (coordinates d s u)) (𝓕⁻ φ) = _
  exact (weighted_regular_pair (-s) (coordinates d s u) (𝓕⁻ φ)).2

lemma realization_conjugateReflection {d : ℕ} {s : ℝ} (f : Hs d s)
    (φ : Schwartz ℂ d) :
    @realization d s (realConjugateReflectionL2 d f) φ = star (realization f (conjSchwartz φ)) := by
  rw [realization_integral, realization_integral]
  change _ = (starRingEnd ℂ) (∫ ξ, _)
  rw [← integral_conj]
  calc
    _ = ∫ ξ, star ((𝓕⁻ (conjSchwartz φ) : Schwartz ℂ d) (-ξ) *
        (complexWeight (-s) (-ξ) * coordinates d s f (-ξ))) := by
      apply integral_congr_ae
      filter_upwards [realConjugateReflectionL2_coe d f] with ξ hξ
      change (𝓕⁻ φ : Schwartz ℂ d) ξ *
        (complexWeight (-s) ξ * realConjugateReflectionL2 d f ξ) = _
      rw [hξ]
      simp only [star_mul, complexWeight_neg_argument]
      have hp := conj_fourierInv φ ξ
      rw [← hp]
      simp only [show coordinates d s f = f from rfl]
      simp [complexWeight, mul_comm, mul_left_comm, mul_assoc]
    _ = _ := integral_neg_eq_self (fun ξ : Euclidean d =>
      star ((𝓕⁻ (conjSchwartz φ) : Schwartz ℂ d) ξ *
        (complexWeight (-s) ξ * coordinates d s f ξ))) volume

lemma realization_real_iff {d : ℕ} {s : ℝ} (f : Hs d s) :
    f ∈ hermitianL2 d ↔
      ∀ φ : Schwartz ℝ d, (realization f (complexifySchwartz φ)).im = 0 := by
  rw [hermitianL2_mem_iff]
  constructor
  · intro hf φ
    have h := realization_conjugateReflection f (complexifySchwartz φ)
    have hc : conjSchwartz (complexifySchwartz φ) = complexifySchwartz φ := by
      ext x; simp [complexifySchwartz]
    rw [hf, hc] at h
    have := congrArg Complex.im h
    change (realization f (complexifySchwartz φ)).im =
      -(realization f (complexifySchwartz φ)).im at this
    linarith
  · intro hf
    apply realization_injective d s
    ext φ
    rw [realization_conjugateReflection]
    rw [schwartz_decompose φ]
    simp only [map_add, map_smul]
    have hre (ψ : Schwartz ℝ d) : star (realization f (complexifySchwartz ψ)) =
        realization f (complexifySchwartz ψ) := by
      apply Complex.ext <;> simp [hf ψ]
    have hc (ψ : Schwartz ℝ d) : conjSchwartz (complexifySchwartz ψ) = complexifySchwartz ψ := by
      ext x; simp [complexifySchwartz]
    have hci (ψ : Schwartz ℝ d) : conjSchwartz (Complex.I • complexifySchwartz ψ) =
        -Complex.I • complexifySchwartz ψ := by
      ext x
      simp [complexifySchwartz, star_mul, mul_comm]
    rw [hci, hc]
    simp only [map_smul, star_add, star_smul, hre]
    simp


lemma complexify_realRealization {d : ℕ} {s : ℝ} (u : RealHs d s) :
    complexifyTempered (realRealization u) = @realization d s (realCoordinates d s u) := by
  apply complexify_restrict_of_real
  exact (realization_real_iff (realCoordinates d s u)).mp u.property

lemma conjugationL2_inner (d : ℕ) (f g : L2 d) :
    inner ℂ (conjugationL2 d f) (conjugationL2 d g) =
      star (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [conjugationL2_coe d f, conjugationL2_coe d g] with ξ hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

lemma hermitian_reflection_eq_conjugation (d : ℕ) (f : L2 d)
    (hf : conjugationL2 d (reflectionL2 d f) = f) :
    reflectionL2 d f = conjugationL2 d f := by
  have h := congrArg (conjugationL2 d) hf
  rw [conjugationL2_involutive] at h
  exact h

lemma hermitian_inner_real (d : ℕ) (f g : L2 d)
    (hf : conjugationL2 d (reflectionL2 d f) = f)
    (hg : conjugationL2 d (reflectionL2 d g) = g) :
    (inner ℂ f g).im = 0 := by
  have h : inner ℂ f g = star (inner ℂ f g) := by
    calc
      inner ℂ f g = inner ℂ (reflectionL2 d f) (reflectionL2 d g) :=
        (LinearIsometry.inner_map_map _ _ _).symm
      _ = inner ℂ (conjugationL2 d f) (conjugationL2 d g) := by
        rw [hermitian_reflection_eq_conjugation d f hf,
          hermitian_reflection_eq_conjugation d g hg]
      _ = _ := conjugationL2_inner d f g
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

lemma dualPairing_eq_inner_of_hermitian {d : ℕ} {s : ℝ}
    (u : Hs d s) (v : Hs d (-s))
    (hv : conjugationL2 d (reflectionL2 d (coordinates d (-s) v)) =
      coordinates d (-s) v) :
    dualPairing u v = inner ℂ (coordinates d (-s) v) (coordinates d s u) := by
  unfold dualPairing
  simp only [pairing_integrand]
  rw [L2.inner_def]
  apply integral_congr_ae
  have hr := hermitian_reflection_eq_conjugation d (coordinates d (-s) v) hv
  filter_upwards [reflectionL2_coe d (coordinates d (-s) v),
    conjugationL2_coe d (coordinates d (-s) v)] with ξ href hconj
  have hh := congrArg (fun f : L2 d => f ξ) hr
  rw [href, hconj] at hh
  simp only [hh, RCLike.inner_apply]
  rfl

lemma realConjugationL2_eq_conjugationL2 (d : ℕ) (f : L2 d) :
    realConjugationL2 d f = conjugationL2 d f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp Complex.conjCLE.toContinuousLinearMap f,
    conjugationL2_coe d f] with ξ hr hc
  exact hr.trans hc.symm

lemma realConjugateReflectionL2_eq (d : ℕ) (f : L2 d) :
    realConjugateReflectionL2 d f = conjugationL2 d (reflectionL2 d f) := by
  change realConjugationL2 d (reflectionL2 d f) = _
  exact realConjugationL2_eq_conjugationL2 d _

lemma realCoordinates_conjugation_reflection_fixed {d : ℕ} {s : ℝ} (u : RealHs d s) :
    conjugationL2 d (reflectionL2 d (realCoordinates d s u)) =
      realCoordinates d s u := by
  have hu := u.property
  change realConjugateReflectionL2 d u.val - u.val = 0 at hu
  rw [realConjugateReflectionL2_eq] at hu
  exact sub_eq_zero.mp hu

lemma real_pairing_eq_inner {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    @dualPairing d s (realCoordinates d s u) (realCoordinates d (-s) v) =
      inner ℂ (realCoordinates d (-s) v) (realCoordinates d s u) := by
  exact dualPairing_eq_inner_of_hermitian _ _ (realCoordinates_conjugation_reflection_fixed v)

lemma real_pairing_im_zero {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    (@dualPairing d s (realCoordinates d s u) (realCoordinates d (-s) v)).im = 0 := by
  rw [real_pairing_eq_inner]
  exact hermitian_inner_real _ _ _ (realCoordinates_conjugation_reflection_fixed v) (realCoordinates_conjugation_reflection_fixed u)

lemma real_pairing_eq_real_inner {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    realDualPairing u v = inner ℝ (show RealHs d s from v) u := by
  unfold realDualPairing
  rw [real_pairing_eq_inner]
  change (inner ℂ (realCoordinates d (-s) v) (realCoordinates d s u)).re =
    inner ℝ (realCoordinates d (-s) v) (realCoordinates d s u)
  rw [L2.inner_def, L2.inner_def]
  simpa using (integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ)
    (realCoordinates d (-s) v) (realCoordinates d s u))).symm

theorem real_pairing_reality {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    (realDualPairing u v : ℂ) =
      @dualPairing d s (realCoordinates d s u) (realCoordinates d (-s) v) := by
  apply Complex.ext
  · rfl
  · exact (real_pairing_im_zero u v).symm

def realDualityIsometry (d : ℕ) (s : ℝ) :
    RealHs d (-s) ≃ₗᵢ[ℝ] (RealHs d s →L[ℝ] ℝ) :=
  (LinearIsometryEquiv.refl ℝ _).trans (InnerProductSpace.toDual ℝ (RealHs d s))

theorem real_duality (d : ℕ) (s : ℝ) :
    ∃ e : RealHs d (-s) ≃ₗᵢ[ℝ] (RealHs d s →L[ℝ] ℝ),
      ∀ u v, e v u = realDualPairing u v := by
  refine ⟨realDualityIsometry d s, ?_⟩
  intro u v
  exact (real_pairing_eq_real_inner u v).symm

theorem real_pairing_integrable {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    Integrable (fun ξ =>
      fourierDensity (s := s) (realCoordinates d s u) ξ *
        fourierDensity (s := -s) (realCoordinates d (-s) v) (-ξ)) :=
  pairing_integrable d s _ _

lemma complexify_realSchwartzRegularDistribution {d : ℕ} (f : Schwartz ℝ d) :
    complexifyTempered (realSchwartzRegularDistribution f) =
      schwartzRegularDistribution (complexifySchwartz f) := by
  have h (φ : Schwartz ℝ d) :
      complexifyTempered (realSchwartzRegularDistribution f) (complexifySchwartz φ) =
        schwartzRegularDistribution (complexifySchwartz f) (complexifySchwartz φ) := by
    rw [complexifyTempered_apply_complexifySchwartz]
    change ((∫ x, f x * φ x : ℝ) : ℂ) =
      ∫ x, (complexifySchwartz f) x * (complexifySchwartz φ) x
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [complexifySchwartz]
  ext φ
  rw [schwartz_decompose φ]
  simp only [map_add, map_smul]
  rw [h, h]

lemma real_pairing_integral {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    realDualPairing u v =
      ∫ ξ, (realFourierDensity u ξ * realFourierDensity v (-ξ)).re := by
  exact (integral_re (𝕜 := ℂ) (real_pairing_integrable u v)).symm

lemma real_pairing_bound {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    |realDualPairing u v| ≤ ‖u‖ * ‖v‖ := by
  rw [real_pairing_eq_real_inner]
  exact (abs_real_inner_le_norm (show RealHs d s from v) u).trans_eq (mul_comm _ _)

lemma real_pairing_test_of_complexify
    (hc : ∀ {d : ℕ} {s : ℝ} (u : RealHs d s),
      complexifyTempered (realRealization u) = @realization d s (realCoordinates d s u))
    {d : ℕ} {s : ℝ} (u : RealHs d s) (g : Schwartz ℝ d) (v : RealHs d (-s))
    (hv : realRealization v = realSchwartzRegularDistribution g) :
    realDualPairing u v = realRealization u g := by
  have hvC : @realization d (-s) (realCoordinates d (-s) v) =
      schwartzRegularDistribution (complexifySchwartz g) := by
    rw [← hc v, hv, complexify_realSchwartzRegularDistribution]
  unfold realDualPairing
  rw [pairing_test d s _ (complexifySchwartz g) _ hvC]
  rfl

lemma real_pairing_extends_of_complexify
    (hc : ∀ {d : ℕ} {s : ℝ} (u : RealHs d s),
      complexifyTempered (realRealization u) = @realization d s (realCoordinates d s u))
    {d : ℕ} {s : ℝ} (f g : Schwartz ℝ d) (u : RealHs d s) (v : RealHs d (-s))
    (hu : realRealization u = realSchwartzRegularDistribution f)
    (hv : realRealization v = realSchwartzRegularDistribution g) :
    realDualPairing u v = ∫ x, f x * g x := by
  rw [real_pairing_test_of_complexify hc u g v hv, hu]
  rfl

lemma real_norm_formula {d : ℕ} {s : ℝ} (u : RealHs d s) :
    Integrable (fun ξ => frequencyWeight ξ ^ s * ‖realFourierDensity u ξ‖ ^ 2) ∧
      ‖u‖ ^ 2 = ∫ ξ, frequencyWeight ξ ^ s * ‖realFourierDensity u ξ‖ ^ 2 := by
  exact norm_formula d s (realCoordinates d s u)


end ExpandedFA.Sobolev.FourierScale

namespace ExpandedFA.Sobolev.FourierScale

def real_space : Specs.ExpandedFA.Sobolev.FourierHilbertScale.realSpaceType := RealHs

def real_realize : Specs.ExpandedFA.Sobolev.FourierHilbertScale.realRealizationType :=
  @realRealization

theorem real_hilbert : Specs.ExpandedFA.Sobolev.FourierHilbertScale.realHilbertType := by
  intro d s
  infer_instance

end ExpandedFA.Sobolev.FourierScale

set_option maxHeartbeats 800000
namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

/-- Averaging a coordinate with its conjugate reflection projects onto the real form. -/
def hermitianProjection (d : ℕ) (s : ℝ) : L2 d →L[ℝ] RealHs d s :=
  (((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (L2 d) +
    (realConjugateReflectionL2 d).toContinuousLinearMap)).codRestrict
    (hermitianL2 d) (by
      intro f
      rw [hermitianL2_mem_iff]
      change realConjugateReflectionL2 d ((2 : ℝ)⁻¹ • (f + realConjugateReflectionL2 d f)) = (2 : ℝ)⁻¹ • (f + realConjugateReflectionL2 d f)
      rw [map_smul, map_add, realConjugateReflectionL2_involutive d f, add_comm])

@[simp] lemma hermitianProjection_coe (d : ℕ) (s : ℝ) (f : L2 d) :
    realCoordinates d s (hermitianProjection d s f) =
      (2 : ℝ)⁻¹ • (f + realConjugateReflectionL2 d f) := rfl

lemma hermitianProjection_surjective (d : ℕ) (s : ℝ) :
    Function.Surjective (hermitianProjection d s) := by
  intro f
  refine ⟨realCoordinates d s f, ?_⟩
  apply realCoordinates_injective
  rw [hermitianProjection_coe, realCoordinates_fixed]
  module

/-- A dense set can be averaged continuously into the fixed-point Hilbert space. -/
lemma hermitianProjection_dense {d : ℕ} {s : ℝ} (S : Set (L2 d)) (hS : Dense S) :
    Dense (hermitianProjection d s '' S) :=
  (hermitianProjection_surjective d s).denseRange.dense_image
    (hermitianProjection d s).continuous hS

lemma hermitianProjection_schwartz_dense (d : ℕ) (s : ℝ) :
    DenseRange (fun f : Schwartz ℂ d => hermitianProjection d s (f.toLp 2)) := by
  exact (hermitianProjection_surjective d s).denseRange.comp
    (SchwartzMap.denseRange_toLpCLM (p := 2)
      (μ := (volume : Measure (Euclidean d))) (by norm_num))
    (hermitianProjection d s).continuous

end ExpandedFA.Sobolev.FourierScale

namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

lemma regular_conjSchwartz {d : ℕ} (g φ : Schwartz ℂ d) :
    star (schwartzRegularDistribution g (conjSchwartz φ)) =
      schwartzRegularDistribution (conjSchwartz g) φ := by
  rw [Inversion.regular_distribution_pairing, Inversion.regular_distribution_pairing]
  change (starRingEnd ℂ) (∫ x, _) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [conjSchwartz, map_mul]

lemma hermitianProjection_regular {d : ℕ} {s : ℝ}
    (u : Hs d s) (g : Schwartz ℂ d)
    (hu : realization u = schwartzRegularDistribution g) :
    realization (show Hs d s from realCoordinates d s (hermitianProjection d s u)) =
      schwartzRegularDistribution (complexifySchwartz (reSchwartz g)) := by
  ext φ
  change realization ((2 : ℝ)⁻¹ • (u + (show Hs d s from realConjugateReflectionL2 d u))) φ = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [(realization_linear d s).2, (realization_linear d s).1]
  change (↑((2 : ℝ)⁻¹) : ℂ) *
    (realization u φ + realization (realConjugateReflectionL2 d u) φ) = _
  rw [realization_conjugateReflection, hu, regular_conjSchwartz]
  rw [Inversion.regular_distribution_pairing, Inversion.regular_distribution_pairing,
    Inversion.regular_distribution_pairing]
  have hi₁ : Integrable (fun x => g x * φ x) := (g.memLp 2).integrable_mul (φ.memLp 2)
  have hi₂ : Integrable (fun x => conjSchwartz g x * φ x) :=
    ((conjSchwartz g).memLp 2).integrable_mul (φ.memLp 2)
  rw [← integral_add hi₁ hi₂, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [conjSchwartz_apply, complexifySchwartz, reSchwartz,
    SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma real_schwartz_coordinates_dense (d : ℕ) (s : ℝ)
    :
    Dense {u : RealHs d s | ∃ f : Schwartz ℝ d,
      realization (show Hs d s from realCoordinates d s u) =
        schwartzRegularDistribution (complexifySchwartz f)} := by
  have hdense : Dense {u : L2 d | ∃ f : Schwartz ℂ d,
      realization (show Hs d s from u) = schwartzRegularDistribution f} :=
    schwartz_dense d s
  apply (hermitianProjection_dense _ hdense).mono
  rintro u ⟨v, ⟨g, hg⟩, rfl⟩
  exact ⟨reSchwartz g, hermitianProjection_regular v g hg⟩

lemma real_schwartz_coordinates_inclusion (d : ℕ) (s : ℝ) (f : Schwartz ℝ d)
    :
    ∃ u : RealHs d s,
      realization (show Hs d s from realCoordinates d s u) =
        schwartzRegularDistribution (complexifySchwartz f) := by
  obtain ⟨u, hu⟩ := schwartz_inclusion d s (complexifySchwartz f)
  refine ⟨hermitianProjection d s u, ?_⟩
  have h := hermitianProjection_regular u (complexifySchwartz f) hu
  have hre : reSchwartz (complexifySchwartz f) = f := by
    ext x
    simp [reSchwartz, complexifySchwartz]
  simpa only [hre] using h


theorem real_schwartz_dense (d : ℕ) (s : ℝ) :
    Dense {u : RealHs d s | ∃ f : Schwartz ℝ d,
      realRealization u = realSchwartzRegularDistribution f} := by
  apply (real_schwartz_coordinates_dense d s).mono
  rintro u ⟨f, hf⟩
  refine ⟨f, ?_⟩
  apply complexifyTempered_injective d
  rw [complexify_realRealization, complexify_realSchwartzRegularDistribution]
  exact hf

theorem real_schwartz_inclusion (d : ℕ) (s : ℝ) (f : Schwartz ℝ d) :
    ∃ u : RealHs d s, realRealization u = realSchwartzRegularDistribution f := by
  obtain ⟨u, hu⟩ := real_schwartz_coordinates_inclusion d s f
  refine ⟨u, ?_⟩
  apply complexifyTempered_injective d
  rw [complexify_realRealization, complexify_realSchwartzRegularDistribution]
  exact hu

end ExpandedFA.Sobolev.FourierScale

open scoped Distributions ContDiff ENNReal
namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Distributions

variable {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}

lemma testPartial_postcomp {𝕜₁ 𝕜₂ : Type} [RCLike 𝕜₁] [RCLike 𝕜₂]
    (L : 𝕜₁ →L[ℝ] 𝕜₂) (w : List (Fin d)) (φ : Tests 𝕜₁ Ω) :
    testPartialCLM w (TestFunction.postcompCLM L φ) =
      TestFunction.postcompCLM L (testPartialCLM w φ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change TestFunction.lineDerivCLM 𝕜₂ (coordinateVector i)
      (testPartialCLM w (TestFunction.postcompCLM L φ)) = _
    rw [ih]
    ext x
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    change fderiv ℝ (L ∘ (testPartialCLM w φ)) x (coordinateVector i) =
      L (TestFunction.lineDerivCLM 𝕜₁ (coordinateVector i) (testPartialCLM w φ) x)
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rw [fderiv_comp x L.differentiableAt
      ((testPartialCLM w φ).contDiff.differentiable (by simp) x), L.fderiv]
    rfl


variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lpRealPart : DomainLp ℂ Ω p →L[ℝ] DomainLp ℝ Ω p :=
  Complex.reCLM.compLpL p _

def lpComplexify : DomainLp ℝ Ω p →L[ℝ] DomainLp ℂ Ω p :=
  Complex.ofRealCLM.compLpL p _

lemma lpDistribution_realPart (f : DomainLp ℂ Ω p) (φ : Tests ℝ Ω) :
    lpDistribution (lpRealPart f) φ =
      (lpDistribution f (TestFunction.postcompCLM Complex.ofRealCLM φ)).re := by
  rw [lpDistribution_apply, lpDistribution_apply]
  have hi := Complex.reCLM.integral_comp_comm
    ((TestFunction.postcompCLM Complex.ofRealCLM φ).integrable_bilin
      (ContinuousLinearMap.mul ℂ ℂ) (domainLp_locallyIntegrable f))
  change (∫ x, (((TestFunction.postcompCLM Complex.ofRealCLM φ) x) * f x).re
    ∂(volume.restrict (Ω : Set (Domain d)))) =
    (∫ x, (((TestFunction.postcompCLM Complex.ofRealCLM φ) x) * f x)
      ∂(volume.restrict (Ω : Set (Domain d)))).re at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [Complex.reCLM.coeFn_compLp f] with x hx
  change φ x * Complex.reCLM.compLp f x = _
  rw [hx]
  simp

lemma lpDistribution_complexify_re (f : DomainLp ℝ Ω p) (φ : Tests ℂ Ω) :
    (lpDistribution (lpComplexify f) φ).re =
      lpDistribution f (TestFunction.postcompCLM Complex.reCLM φ) := by
  rw [lpDistribution_apply, lpDistribution_apply]
  have hi := Complex.reCLM.integral_comp_comm
    (φ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
      (domainLp_locallyIntegrable (lpComplexify f)))
  change (∫ x, (φ x * lpComplexify f x).re
    ∂(volume.restrict (Ω : Set (Domain d)))) =
    (∫ x, (φ x * lpComplexify f x)
      ∂(volume.restrict (Ω : Set (Domain d)))).re at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  change (φ x * Complex.ofRealCLM.compLp f x).re = _
  rw [hx]
  simp

lemma lpDistribution_complexify_im (f : DomainLp ℝ Ω p) (φ : Tests ℂ Ω) :
    (lpDistribution (lpComplexify f) φ).im =
      lpDistribution f (TestFunction.postcompCLM Complex.imCLM φ) := by
  rw [lpDistribution_apply, lpDistribution_apply]
  have hi := Complex.imCLM.integral_comp_comm
    (φ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
      (domainLp_locallyIntegrable (lpComplexify f)))
  change (∫ x, (φ x * lpComplexify f x).im
    ∂(volume.restrict (Ω : Set (Domain d)))) =
    (∫ x, (φ x * lpComplexify f x)
      ∂(volume.restrict (Ω : Set (Domain d)))).im at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  change (φ x * Complex.ofRealCLM.compLp f x).im = _
  rw [hx]
  simp

lemma complex_sign (n : ℕ) : (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
  push_cast
  rfl

lemma derivativeGraph_realPart {m : ℕ} (v : DerivativeTuple ℂ Ω m p)
    (hv : v ∈ derivativeGraph ℂ Ω m p) :
    (WithLp.toLp 1 (fun α => lpRealPart (v α))) ∈ derivativeGraph ℝ Ω m p := by
  intro α
  ext φ
  change lpDistribution (lpRealPart (v α)) φ =
    distributionDerivative ℝ d Ω (multiIndexWord (natIndex α))
      (lpDistribution (lpRealPart (v (zeroIndex d m)))) φ
  rw [lpDistribution_realPart, distributionDerivative_apply, lpDistribution_realPart]
  have h := congrArg (fun T : ScalarDistribution ℂ Ω =>
    (T (TestFunction.postcompCLM Complex.ofRealCLM φ)).re) (hv α)
  change (lpDistribution (v α) (TestFunction.postcompCLM Complex.ofRealCLM φ)).re =
    (distributionDerivative ℂ d Ω (multiIndexWord (natIndex α))
      (lpDistribution (v (zeroIndex d m)))
      (TestFunction.postcompCLM Complex.ofRealCLM φ)).re at h
  rw [distributionDerivative_apply, testPartial_postcomp, complex_sign] at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

lemma derivativeGraph_complexify {m : ℕ} (v : DerivativeTuple ℝ Ω m p)
    (hv : v ∈ derivativeGraph ℝ Ω m p) :
    (WithLp.toLp 1 (fun α => lpComplexify (v α))) ∈ derivativeGraph ℂ Ω m p := by
  intro α
  ext φ
  change lpDistribution (lpComplexify (v α)) φ =
    distributionDerivative ℂ d Ω (multiIndexWord (natIndex α))
      (lpDistribution (lpComplexify (v (zeroIndex d m)))) φ
  apply Complex.ext
  · rw [distributionDerivative_apply, complex_sign]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [lpDistribution_complexify_re, lpDistribution_complexify_re]
    have h := congrArg (fun T : ScalarDistribution ℝ Ω =>
      T (TestFunction.postcompCLM Complex.reCLM φ)) (hv α)
    change lpDistribution (v α) (TestFunction.postcompCLM Complex.reCLM φ) =
      distributionDerivative ℝ d Ω (multiIndexWord (natIndex α))
        (lpDistribution (v (zeroIndex d m)))
        (TestFunction.postcompCLM Complex.reCLM φ) at h
    rw [distributionDerivative_apply, testPartial_postcomp] at h
    exact h
  · rw [distributionDerivative_apply, complex_sign]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [lpDistribution_complexify_im, lpDistribution_complexify_im]
    have h := congrArg (fun T : ScalarDistribution ℝ Ω =>
      T (TestFunction.postcompCLM Complex.imCLM φ)) (hv α)
    change lpDistribution (v α) (TestFunction.postcompCLM Complex.imCLM φ) =
      distributionDerivative ℝ d Ω (multiIndexWord (natIndex α))
        (lpDistribution (v (zeroIndex d m)))
        (TestFunction.postcompCLM Complex.imCLM φ) at h
    rw [distributionDerivative_apply, testPartial_postcomp] at h
    exact h



def sobolevRealPartLM (m : ℕ) :
    SobolevSpace ℂ d Ω m p →ₗ[ℝ] SobolevSpace ℝ d Ω m p where
  toFun v := ⟨WithLp.toLp 1 (fun α => lpRealPart (v.val α)),
    derivativeGraph_realPart v.val v.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply PiLp.ext
    intro α
    exact (lpRealPart (Ω := Ω) (p := p)).map_add (u.val α) (v.val α)
  map_smul' c u := by
    apply Subtype.ext
    apply PiLp.ext
    intro α
    exact (lpRealPart (Ω := Ω) (p := p)).map_smul c (u.val α)

def sobolevComplexifyLM (m : ℕ) :
    SobolevSpace ℝ d Ω m p →ₗ[ℝ] SobolevSpace ℂ d Ω m p where
  toFun v := ⟨WithLp.toLp 1 (fun α => lpComplexify (v.val α)),
    derivativeGraph_complexify v.val v.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply PiLp.ext
    intro α
    exact (lpComplexify (Ω := Ω) (p := p)).map_add (u.val α) (v.val α)
  map_smul' c u := by
    apply Subtype.ext
    apply PiLp.ext
    intro α
    exact (lpComplexify (Ω := Ω) (p := p)).map_smul c (u.val α)

lemma sobolevRealPart_norm_le (m : ℕ) (u : SobolevSpace ℂ d Ω m p) :
    ‖sobolevRealPartLM m u‖ ≤ ‖Complex.reCLM‖ * ‖u‖ := by
  rw [sobolev_norm_formula, sobolev_norm_formula]
  unfold Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.NormValue
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun α _ => Complex.reCLM.norm_compLp_le (u.val α))

lemma sobolevComplexify_norm_le (m : ℕ) (u : SobolevSpace ℝ d Ω m p) :
    ‖sobolevComplexifyLM m u‖ ≤ ‖Complex.ofRealCLM‖ * ‖u‖ := by
  rw [sobolev_norm_formula, sobolev_norm_formula]
  unfold Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.NormValue
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun α _ => Complex.ofRealCLM.norm_compLp_le (u.val α))

def sobolevRealPart (m : ℕ) :
    SobolevSpace ℂ d Ω m p →L[ℝ] SobolevSpace ℝ d Ω m p :=
  (sobolevRealPartLM (Ω := Ω) (p := p) m).mkContinuous ‖Complex.reCLM‖
    (sobolevRealPart_norm_le m)

def sobolevComplexify (m : ℕ) :
    SobolevSpace ℝ d Ω m p →L[ℝ] SobolevSpace ℂ d Ω m p :=
  (sobolevComplexifyLM (Ω := Ω) (p := p) m).mkContinuous ‖Complex.ofRealCLM‖
    (sobolevComplexify_norm_le m)

@[simp] lemma sobolevRealPart_apply {m : ℕ} (u : SobolevSpace ℂ d Ω m p)
    (α : DerivativeIndex d m) :
    (sobolevRealPart m u).val α = lpRealPart (u.val α) := rfl

@[simp] lemma sobolevComplexify_apply {m : ℕ} (u : SobolevSpace ℝ d Ω m p)
    (α : DerivativeIndex d m) :
    (sobolevComplexify m u).val α = lpComplexify (u.val α) := rfl

@[simp] lemma lpRealPart_complexify (f : DomainLp ℝ Ω p) :
    lpRealPart (lpComplexify f) = f := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (lpComplexify f),
    Complex.ofRealCLM.coeFn_compLp f] with x hx hy
  change Complex.reCLM.compLp (lpComplexify f) x = f x
  rw [hx]
  change (Complex.ofRealCLM.compLp f x).re = f x
  rw [hy]
  rfl

lemma lpComplexify_realPart_iff (f : DomainLp ℂ Ω p) :
    lpComplexify (lpRealPart f) = f ↔
      ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), (f x).im = 0 := by
  constructor
  · intro h
    have hae := Lp.ext_iff.mp h
    filter_upwards [hae, Complex.ofRealCLM.coeFn_compLp (lpRealPart f)] with x hx hy
    change Complex.ofRealCLM.compLp (lpRealPart f) x = f x at hx
    rw [hy] at hx
    exact (congrArg Complex.im hx).symm
  · intro h
    apply Lp.ext
    filter_upwards [h, Complex.ofRealCLM.coeFn_compLp (lpRealPart f),
      Complex.reCLM.coeFn_compLp f] with x hx hy hz
    change Complex.ofRealCLM.compLp (lpRealPart f) x = f x
    rw [hy]
    change ((Complex.reCLM.compLp f x : ℝ) : ℂ) = f x
    rw [hz]
    exact Complex.ext rfl (by simpa using hx.symm)

@[simp] lemma sobolevRealPart_complexify {m : ℕ} (u : SobolevSpace ℝ d Ω m p) :
    sobolevRealPart m (sobolevComplexify m u) = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  exact lpRealPart_complexify (u.val α)

lemma sobolevComplexify_realPart_iff {m : ℕ} (u : SobolevSpace ℂ d Ω m p) :
    sobolevComplexify m (sobolevRealPart m u) = u ↔
      ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
        (u.val (zeroIndex d m) x).im = 0 := by
  constructor
  · intro h
    have hz := congrArg (fun v : SobolevSpace ℂ d Ω m p => v.val (zeroIndex d m)) h
    exact (lpComplexify_realPart_iff _).mp hz
  · intro h
    apply sobolev_underlying_injective ℂ d Ω m p
    exact (lpComplexify_realPart_iff _).mpr h




def lpImagPart : DomainLp ℂ Ω p →L[ℝ] DomainLp ℝ Ω p :=
  Complex.imCLM.compLpL p _

lemma lpDistribution_imagPart (f : DomainLp ℂ Ω p) (φ : Tests ℝ Ω) :
    lpDistribution (lpImagPart f) φ =
      (lpDistribution f (TestFunction.postcompCLM Complex.ofRealCLM φ)).im := by
  rw [lpDistribution_apply, lpDistribution_apply]
  have hi := Complex.imCLM.integral_comp_comm
    ((TestFunction.postcompCLM Complex.ofRealCLM φ).integrable_bilin
      (ContinuousLinearMap.mul ℂ ℂ) (domainLp_locallyIntegrable f))
  change (∫ x, (((TestFunction.postcompCLM Complex.ofRealCLM φ) x) * f x).im
    ∂(volume.restrict (Ω : Set (Domain d)))) =
    (∫ x, (((TestFunction.postcompCLM Complex.ofRealCLM φ) x) * f x)
      ∂(volume.restrict (Ω : Set (Domain d)))).im at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [Complex.imCLM.coeFn_compLp f] with x hx
  change φ x * Complex.imCLM.compLp f x = _
  rw [hx]
  simp

lemma lp_aeReal_iff_tests (f : DomainLp ℂ Ω p) :
    (∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), (f x).im = 0) ↔
      ∀ φ : Tests ℝ Ω,
        (lpDistribution f (TestFunction.postcompCLM Complex.ofRealCLM φ)).im = 0 := by
  constructor
  · intro h φ
    rw [← lpDistribution_imagPart]
    have hf : lpImagPart f = 0 := by
      apply Lp.ext
      filter_upwards [h, Complex.imCLM.coeFn_compLp f,
        Lp.coeFn_zero ℝ p (volume.restrict (Ω : Set (Domain d)))] with x hx hy hz
      change Complex.imCLM.compLp f x = _
      rw [hy, hz]
      exact hx
    rw [hf]
    change lpDistributionLM (0 : DomainLp ℝ Ω p) φ = 0
    rw [map_zero]
    rfl
  · intro h
    have hf : lpImagPart f = 0 := by
      apply lpDistribution_injective
      ext φ
      rw [lpDistribution_imagPart, h φ]
      change (0 : ℝ) = lpDistributionLM (0 : DomainLp ℝ Ω p) φ
      rw [map_zero]
      rfl
    have hae := Lp.ext_iff.mp hf
    filter_upwards [hae, Complex.imCLM.coeFn_compLp f,
      Lp.coeFn_zero ℝ p (volume.restrict (Ω : Set (Domain d)))] with x hx hy hz
    change Complex.imCLM.compLp f x = _ at hx
    rw [hy, hz] at hx
    exact hx

open ExpandedFA.Fourier

/-- The real-valued version of the test-to-Schwartz coordinate conversion. -/
def realDomainTestSchwartz {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (φ : Tests ℝ Ω) : Schwartz ℝ d :=
  (φ.hasCompactSupport.comp_homeomorph (euclideanDomainEquiv d).toHomeomorph).toSchwartzMap
    (φ.contDiff.comp (euclideanDomainEquiv d).contDiff)

lemma lpDistribution_domainTest_integral {d : ℕ}
    (f : DomainLp ℂ (⊤ : TopologicalSpace.Opens (Domain d)) 2)
    (φ : Tests ℂ (⊤ : TopologicalSpace.Opens (Domain d))) :
    lpDistribution f φ = ∫ x : Euclidean d, domainTestSchwartz φ x * f x := by
  rw [lpDistribution_apply]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  simpa only [domainTestSchwartz_apply, WithLp.ofLp_toLp] using
    (PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (euclideanDomainEquiv d).symm.toHomeomorph.measurableEmbedding
      (fun x => domainTestSchwartz φ x * f x)

lemma integral_complexify_real {d : ℕ}
    (f : DomainLp ℝ (⊤ : TopologicalSpace.Opens (Domain d)) 2)
    (φ : Euclidean d → ℝ) :
    (∫ x : Euclidean d, (φ x : ℂ) * lpComplexify f x) =
      ((∫ x : Euclidean d, φ x * f x : ℝ) : ℂ) := by
  have hf := Complex.ofRealCLM.coeFn_compLp f
  have hf' : ∀ᵐ (x : Euclidean d) ∂(volume : Measure (Euclidean d)),
      lpComplexify f x = (f x : ℂ) := by
    have hf'' : ∀ᵐ x ∂(volume : Measure (Domain d)),
        lpComplexify f x = (f x : ℂ) := by
      change ∀ᵐ x ∂(volume.restrict (⊤ : TopologicalSpace.Opens (Domain d))),
        lpComplexify f x = (f x : ℂ) at hf
      simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using hf
    exact (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae hf''
  have heq : (∫ x : Euclidean d, (φ x : ℂ) * lpComplexify f x) =
      ∫ x : Euclidean d, ((φ x * f x : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hf'] with x hx
    rw [hx, Complex.ofReal_mul]
  rw [heq, integral_complex_ofReal]




lemma complexify_realDomainTestSchwartz {d : ℕ}
    (φ : Tests ℝ (⊤ : TopologicalSpace.Opens (Domain d))) :
    complexifySchwartz (realDomainTestSchwartz φ) =
      domainTestSchwartz (TestFunction.postcompCLM Complex.ofRealCLM φ) := by
  ext x
  rfl

lemma integerEmbedding_real_iff (d m : ℕ) (u : Hs d (m : ℝ)) :
    u ∈ hermitianL2 d ↔
      ∀ᵐ x ∂(volume.restrict (⊤ : TopologicalSpace.Opens (Domain d))),
        ((integerEmbedding d m u).val (zeroIndex d m) x).im = 0 := by
  rw [realization_real_iff]
  constructor
  · intro h
    apply (lp_aeReal_iff_tests _).mpr
    intro φ
    rw [lpDistribution_domainTest_integral,
      ← complexify_realDomainTestSchwartz, ← integerEmbedding_realization]
    exact h (realDomainTestSchwartz φ)
  · intro h φ
    have heq := (sobolevComplexify_realPart_iff (integerEmbedding d m u)).mpr h
    rw [integerEmbedding_realization, ← heq]
    change (∫ x : Euclidean d, (φ x : ℂ) *
      lpComplexify ((sobolevRealPart m (integerEmbedding d m u)).val (zeroIndex d m)) x).im = 0
    rw [integral_complexify_real]
    rfl


def realIntegerEmbedding (d m : ℕ) :
    RealHs d (m : ℝ) →L[ℝ] RealIntegerSobolev d m :=
  (sobolevRealPart m).comp (((integerEmbedding d m).restrictScalars ℝ).comp
    (realCoordinates d (m : ℝ)).toContinuousLinearMap)

lemma realIntegerEmbedding_complexify (d m : ℕ) (u : RealHs d (m : ℝ)) :
    sobolevComplexify m (realIntegerEmbedding d m u) =
      integerEmbedding d m (realCoordinates d (m : ℝ) u) := by
  apply (sobolevComplexify_realPart_iff _).mpr
  exact (integerEmbedding_real_iff d m _).mp u.property

lemma realIntegerEmbedding_injective (d m : ℕ) :
    Function.Injective (realIntegerEmbedding d m) := by
  intro u v h
  apply (realCoordinates d (m : ℝ)).injective
  apply integerEmbedding_injective d m
  rw [← realIntegerEmbedding_complexify, ← realIntegerEmbedding_complexify, h]

lemma realIntegerEmbedding_surjective (d m : ℕ) :
    Function.Surjective (realIntegerEmbedding d m) := by
  intro v
  obtain ⟨u, hu⟩ := integerEmbedding_surjective d m (sobolevComplexify m v)
  have hreal : u ∈ hermitianL2 d := by
    apply (integerEmbedding_real_iff d m u).mpr
    rw [hu]
    apply (sobolevComplexify_realPart_iff _).mp
    rw [sobolevRealPart_complexify]
  refine ⟨⟨u, hreal⟩, ?_⟩
  change sobolevRealPart m (integerEmbedding d m u) = v
  rw [hu, sobolevRealPart_complexify]

lemma realIntegerEmbedding_lower_bound (d m : ℕ) (u : RealHs d (m : ℝ)) :
    ‖u‖ ≤ ((d + 1 : ℝ) ^ (m + 1) * ‖Complex.ofRealCLM‖) *
      ‖realIntegerEmbedding d m u‖ := by
  calc
    ‖u‖ = ‖realCoordinates d (m : ℝ) u‖ := ((realCoordinates d (m : ℝ)).norm_map u).symm
    _ ≤ (d + 1 : ℝ) ^ (m + 1) *
        ‖integerEmbedding d m (realCoordinates d (m : ℝ) u)‖ :=
      integerEmbedding_lower_bound d m _
    _ = (d + 1 : ℝ) ^ (m + 1) *
        ‖sobolevComplexify m (realIntegerEmbedding d m u)‖ := by
      rw [realIntegerEmbedding_complexify]
    _ ≤ (d + 1 : ℝ) ^ (m + 1) *
        (‖Complex.ofRealCLM‖ * ‖realIntegerEmbedding d m u‖) :=
      mul_le_mul_of_nonneg_left (sobolevComplexify_norm_le m _) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

lemma realIntegerEmbedding_realization (d m : ℕ) (u : RealHs d (m : ℝ))
    (φ : Schwartz ℝ d) :
    realRealization u φ = ∫ x : Euclidean d, φ x *
      ((realIntegerEmbedding d m u).val (zeroIndex d m)) x := by
  change (realization (realCoordinates d (m : ℝ) u) (complexifySchwartz φ)).re = _
  rw [integerEmbedding_realization, ← realIntegerEmbedding_complexify]
  change (∫ x : Euclidean d, (φ x : ℂ) *
    lpComplexify ((realIntegerEmbedding d m u).val (zeroIndex d m)) x).re = _
  rw [integral_complexify_real]
  rfl


theorem real_integer : ∀ (d m : ℕ),
    ∃ e : RealHs d (m : ℝ) ≃L[ℝ] RealIntegerSobolev d m,
      ∀ (u : RealHs d (m : ℝ)) (φ : Schwartz ℝ d),
        realRealization u φ = ∫ x : Euclidean d, φ x *
          ((e u).val (zeroIndex d m)) x := by
  intro d m
  let e := LinearEquiv.ofBijective (realIntegerEmbedding d m).toLinearMap
    ⟨realIntegerEmbedding_injective d m, realIntegerEmbedding_surjective d m⟩
  let C := (d + 1 : ℝ) ^ (m + 1) * ‖Complex.ofRealCLM‖
  have hinv : ∀ v : RealIntegerSobolev d m, ‖e.symm v‖ ≤ C * ‖v‖ := by
    intro v
    have h := realIntegerEmbedding_lower_bound d m (e.symm v)
    change ‖e.symm v‖ ≤ C * ‖e (e.symm v)‖ at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  let eL : RealHs d (m : ℝ) ≃L[ℝ] RealIntegerSobolev d m :=
    { e with
      continuous_toFun := (realIntegerEmbedding d m).continuous
      continuous_invFun := (e.symm.toLinearMap.mkContinuous C hinv).continuous }
  exact ⟨eL, realIntegerEmbedding_realization d m⟩
end ExpandedFA.Sobolev.FourierScale

namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

lemma real_realization_add {d : ℕ} {s : ℝ} (u v : RealHs d s) :
    realRealization (u + v) = realRealization u + realRealization v := by
  change restrictTempered (@realization d s (realCoordinates d s (u + v))) = _
  rw [map_add, (realization_linear d s).1]
  ext φ
  simp [realRealization, restrictTempered]

lemma real_realization_smul {d : ℕ} {s : ℝ} (c : ℝ) (u : RealHs d s) :
    realRealization (c • u) = c • realRealization u := by
  change restrictTempered (@realization d s (realCoordinates d s (c • u))) = _
  rw [map_smul]
  ext φ
  change (@realization d s (c • realCoordinates d s u) (complexifySchwartz φ)).re =
    c * (@realization d s (realCoordinates d s u) (complexifySchwartz φ)).re
  have h := congrArg (fun T : Tempered ℂ d => T (complexifySchwartz φ))
    ((realization_linear d s).2 (algebraMap ℝ ℂ c) (realCoordinates d s u))
  simp only [smul_apply, algebraMap_smul] at h
  rw [h]
  simp

lemma real_realization_linear (d : ℕ) (s : ℝ) :
    (∀ u v : RealHs d s, realRealization (u + v) = realRealization u + realRealization v) ∧
    (∀ (c : ℝ) (u : RealHs d s), realRealization (c • u) = c • realRealization u) :=
  ⟨real_realization_add, real_realization_smul⟩

lemma real_realization_injective (d : ℕ) (s : ℝ) :
    Function.Injective (@realRealization d s) := by
  intro u v huv
  apply (realCoordinates d s).injective
  apply realization_injective d s
  simpa only [complexify_realRealization] using congrArg complexifyTempered huv

lemma real_realization_image (d : ℕ) (s : ℝ) (T : Tempered ℝ d) :
    (∃ u : RealHs d s, realRealization u = T) ↔ realMemHs s T := by
  constructor
  · rintro ⟨u, rfl⟩
    unfold realMemHs
    rw [complexify_realRealization]
    exact (realization_image d s _).mp ⟨realCoordinates d s u, rfl⟩
  · intro hT
    obtain ⟨f, hf⟩ := (realization_image d s (complexifyTempered T)).mpr hT
    have hr : f ∈ hermitianL2 d := (realization_real_iff f).mpr (by
      intro φ
      rw [hf]
      simp)
    let u : RealHs d s := ⟨f, hr⟩
    refine ⟨u, ?_⟩
    apply complexifyTempered_injective d
    rw [complexify_realRealization]
    exact hf

lemma real_density {d : ℕ} {s : ℝ} (u : RealHs d s) :
    HasFourierDensity (complexifyTempered (realRealization u)) (realFourierDensity u) := by
  rw [complexify_realRealization]
  exact density d s (realCoordinates d s u)

lemma real_bessel {d : ℕ} {s : ℝ} (t : ℝ) (u : RealHs d s) :
    realRealization (realBesselIsometry d s t u) =
      realBesselOperator t (realRealization u) := by
  unfold realBesselOperator
  rw [complexify_realRealization]
  exact congrArg restrictTempered (bessel d s t (realCoordinates d s u))

lemma real_pairing_test {d : ℕ} {s : ℝ} (u : RealHs d s)
    (g : Schwartz ℝ d) (v : RealHs d (-s))
    (hv : realRealization v = realSchwartzRegularDistribution g) :
    realDualPairing u v = realRealization u g :=
  real_pairing_test_of_complexify @complexify_realRealization u g v hv

lemma real_pairing_extends {d : ℕ} {s : ℝ} (f g : Schwartz ℝ d)
    (u : RealHs d s) (v : RealHs d (-s))
    (hu : realRealization u = realSchwartzRegularDistribution f)
    (hv : realRealization v = realSchwartzRegularDistribution g) :
    realDualPairing u v = ∫ x, f x * g x :=
  real_pairing_extends_of_complexify @complexify_realRealization f g u v hu hv

lemma real_fourierDensity_hermitian {d : ℕ} {s : ℝ} (u : RealHs d s) :
    ∀ᵐ ξ ∂volume, realFourierDensity u (-ξ) = star (realFourierDensity u ξ) := by
  filter_upwards [realCoordinates_hermitian u] with ξ hξ
  change complexWeight (-s) (-ξ) * realCoordinates d s u (-ξ) =
    star (complexWeight (-s) ξ * realCoordinates d s u ξ)
  rw [complexWeight_neg_argument, hξ]
  simp [complexWeight]

end ExpandedFA.Sobolev.FourierScale

namespace ExpandedFA.Sobolev.FourierScale

theorem real_bessel_complexification :
    Specs.ExpandedFA.Sobolev.FourierHilbertScale.realBesselComplexificationType := by
  intro d s t u
  rw [← real_bessel t u, complexify_realRealization, complexify_realRealization]
  exact bessel d s t (realCoordinates d s u)

end ExpandedFA.Sobolev.FourierScale
