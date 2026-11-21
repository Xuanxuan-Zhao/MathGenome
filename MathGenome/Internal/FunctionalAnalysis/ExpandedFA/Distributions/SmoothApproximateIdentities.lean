import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.SmoothApproximateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.LpTranslationContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Set Metric Function
open scoped ENNReal Topology

namespace ExpandedFA.Distributions
open SmoothApproximateIdentitiesSpec

def scaledKernel : ScaledKernelType := ScaledKernelValue

def mollify : MollifyType := MollifyValue

theorem smooth_compactSupport_dense : SmoothCompactSupportDense := by
  intro d 𝕜 _ p _ hp
  exact Lp.dense_hasCompactSupport_contDiff (E := Space d) (F := 𝕜) (μ := volume) hp

lemma scaledKernel_integral {d : ℕ} (ρ : Space d → ℝ) (hρ : ∫ x, ρ x = 1)
    {ε : ℝ} (hε : 0 < ε) : ∫ x, ScaledKernelValue ρ ε x = 1 := by
  simp only [ScaledKernelValue, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume ρ hε.le]
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul, hρ, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')

theorem scaledKernel_properties : ScaledKernelProperties := by
  intro d ρ hρ ε hε
  refine ⟨?_, ?_, ?_, scaledKernel_integral ρ hρ.2.2.2 hε⟩
  · exact contDiff_const.mul (hρ.1.comp (contDiff_id.const_smul ε⁻¹))
  · exact (hρ.2.1.comp_isClosedEmbedding
      (Homeomorph.smul (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne'))).isClosedEmbedding).mul_left
  · intro x
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (hρ.2.2.1 _)

lemma scaledKernel_support_eventually {d : ℕ} (ρ : Space d → ℝ)
    (hρ : HasCompactSupport ρ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), support (ScaledKernelValue ρ ε) ⊆ ball 0 r := by
  obtain ⟨R, hR, hbound⟩ := hρ.isBounded.exists_pos_norm_le
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < r / R :=
    (eventually_lt_nhds (div_pos hr hR)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hεr y hy
  have hy' : ε⁻¹ • y ∈ tsupport ρ := by
    apply subset_tsupport
    exact (mul_ne_zero_iff.mp hy).2
  have hnorm : ‖y‖ ≤ ε * R := by
    calc
      ‖y‖ = ‖ε • (ε⁻¹ • y)‖ := by rw [smul_inv_smul₀ (ne_of_gt hε)]
      _ = ε * ‖ε⁻¹ • y‖ := by rw [norm_smul, Real.norm_of_nonneg (le_of_lt hε)]
      _ ≤ ε * R := mul_le_mul_of_nonneg_left (hbound _ hy') (le_of_lt hε)
  rw [mem_ball_zero_iff]
  exact hnorm.trans_lt ((lt_div_iff₀ hR).mp hεr)

/-- A single estimate gives both continuous versions. -/
lemma mollify_uniformlyOn_of_translation_control {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : Space d → ℝ) (hρ : IsMollifier ρ) (f : Space d → 𝕜)
    (hf : AEStronglyMeasurable f volume) (K : Set (Space d))
    (hcontrol : ∀ η > 0, ∃ r > 0, ∀ x ∈ K, ∀ y ∈ ball x r,
      dist (f y) (f x) ≤ η) :
    TendstoUniformlyOn (fun ε => MollifyValue ρ ε f) f (𝓝[>] (0 : ℝ)) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  obtain ⟨r, hr, hmod⟩ := hcontrol (η / 2) (half_pos hη)
  filter_upwards [scaledKernel_support_eventually ρ hρ.2.1 hr,
    self_mem_nhdsWithin] with ε hs hε x hx
  have hk := scaledKernel_properties ρ hρ ε hε
  simpa only [MollifyValue, dist_comm] using
    (dist_convolution_le (le_of_lt (half_pos hη)) hs hk.2.2.1 hk.2.2.2 hf
      (hmod x hx)).trans_lt (half_lt_self hη)

theorem mollify_uniform : UniformApproximation := by
  intro d 𝕜 _ ρ hρ f hf
  rw [← tendstoUniformlyOn_univ]
  apply mollify_uniformlyOn_of_translation_control ρ hρ f hf.continuous.aestronglyMeasurable
  intro η hη
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuous_iff.mp hf η hη
  exact ⟨r, hr, fun x _ y hy => (hmod (mem_ball.mp hy)).le⟩

theorem mollify_locallyUniform : LocallyUniformApproximation := by
  intro d 𝕜 _ ρ hρ f hf K hK
  apply mollify_uniformlyOn_of_translation_control ρ hρ f hf.aestronglyMeasurable
  intro η hη
  have hu := hK.uniformContinuousAt_of_continuousAt f (fun x _ => hf.continuousAt)
    (Metric.dist_mem_uniformity hη)
  obtain ⟨r, hr, hmod⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨r, hr, fun x hx y hy => ?_⟩
  exact (by simpa only [dist_comm] using (hmod (by simpa [dist_comm] using hy) hx).le)

/-- Minkowski and mass one bound the error by the largest translation error
on the kernel support. The proof also establishes almost everywhere existence
of the convolution integrals used here. -/
lemma convolution_error_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (φ : Space d → ℝ) (hφm : Measurable φ) (hφi : Integrable φ)
    (hφn : ∀ y, 0 ≤ φ y) (hφmass : ∫ y, φ y = 1)
    (f : Space d → 𝕜) (hfm : Measurable f)
    (η : ℝ≥0∞) (hη : η ≠ ∞)
    (hcontrol : ∀ y ∈ support φ,
      eLpNorm (fun x => f (x-y) - f x) p volume ≤ η) :
    eLpNorm (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) p volume ≤ η := by
  let F : Space d × Space d → 𝕜 := fun z => φ z.2 • (f (z.1-z.2) - f z.1)
  have hF : Measurable F := (hφm.comp measurable_snd).smul
    ((hfm.comp (measurable_fst.sub measurable_snd)).sub (hfm.comp measurable_fst))
  have hs (y : Space d) : eLpNorm (fun x => F (x,y)) p volume ≤ ‖φ y‖ₑ * η := by
    change eLpNorm ((φ y) • (fun x => f (x-y) - f x)) p volume ≤ _
    rw [eLpNorm_const_smul]
    by_cases hy : y ∈ support φ
    · gcongr
      exact hcontrol y hy
    · simp [notMem_support.mp hy]
  have hmass : (∫⁻ y, ‖φ y‖ₑ) = 1 := by
    simp_rw [← ofReal_norm, Real.norm_of_nonneg (hφn _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hφi (Eventually.of_forall hφn), hφmass]
    simp
  have hbound : (∫⁻ y, eLpNorm (fun x => F (x,y)) p volume) ≤ η := by
    calc
      _ ≤ ∫⁻ y, ‖φ y‖ₑ * η := lintegral_mono hs
      _ = η := by rw [lintegral_mul_const _ hφm.enorm, hmass, one_mul]
  obtain ⟨hi, hb⟩ := minkowski_integral_eLpNorm volume volume p hp hpt F hF
    (hbound.trans_lt (lt_top_iff_ne_top.mpr hη))
  have heq : (fun x => ∫ y, F (x,y)) =ᵐ[volume]
      convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f := by
    filter_upwards [hi] with x hx
    have hc : Integrable (fun y => φ y • f x) := hφi.smul_const (f x)
    have hconv : Integrable (fun y => φ y • f (x-y)) := by
      convert hx.add hc using 1
      ext y
      simp [F, smul_sub]
    change (∫ y, φ y • (f (x-y) - f x)) = (∫ y, φ y • f (x-y)) - f x
    simp_rw [smul_sub]
    rw [integral_sub hconv hc, integral_smul_const, hφmass, one_smul]
  rw [← eLpNorm_congr_ae heq]
  exact hb.trans hbound

lemma translation_error_tendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : Space d → 𝕜) (hf : MemLp f p volume) :
    Tendsto (fun y => eLpNorm (fun x => f (x-y) - f x) p volume) (𝓝 0) (𝓝 0) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let v := hf.toLp f
  have heq (y : Space d) : eLpNorm (fun x => f (x-y) - f x) p volume =
      ENNReal.ofReal ‖LpTranslationContinuitySpec.LpTranslationValue p y v - v‖ := by
    rw [ofReal_norm, Lp.enorm_def]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (LpTranslationContinuitySpec.LpTranslationValue p y v) v,
      lpTranslation_representative p y v,
      (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae hf.coeFn_toLp,
      hf.coeFn_toLp] with x hsub ht hs hv
    simp only [Pi.sub_apply] at hsub
    rw [hsub, ht, hs, hv]
  have ht : Tendsto (fun y => ENNReal.ofReal
      ‖LpTranslationContinuitySpec.LpTranslationValue p y v - v‖) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp (lpTranslation_norm_tendsto_zero p hpt v)
  exact ht.congr' (Eventually.of_forall fun y => (heq y).symm)

lemma mollify_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : Space d → ℝ) (hρ : IsMollifier ρ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : Space d → 𝕜) (hf : MemLp f p volume)
    {ε : ℝ} (hε : 0 < ε) : MemLp (MollifyValue ρ ε f) p volume := by
  have hk := scaledKernel_properties ρ hρ ε hε
  have hki : Integrable (ScaledKernelValue ρ ε) :=
    hk.1.continuous.integrable_of_hasCompactSupport hk.2.1
  have hb := (young_l1_lp_endpoint p hp (fun y => (ScaledKernelValue ρ ε y : 𝕜)) f
    (memLp_one_iff_integrable.mpr hki).ofReal hf).2.2.1
  change MemLp (fun x => ∫ y, (ScaledKernelValue ρ ε y : 𝕜) * f (x-y)) p volume at hb
  change MemLp (fun x => ∫ y, ScaledKernelValue ρ ε y • f (x-y)) p volume
  simpa only [RCLike.real_smul_eq_coe_mul] using hb

lemma mollify_eLpNorm_tendsto_of_measurable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ρ : Space d → ℝ) (hρ : IsMollifier ρ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : Space d → 𝕜) (hfm : Measurable f) (hf : MemLp f p volume) :
    Tendsto (fun ε => eLpNorm (MollifyValue ρ ε f - f) p volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  by_cases hηt : η = ∞
  · simp [hηt]
  have ht := ENNReal.tendsto_nhds_zero.mp (translation_error_tendsto p hp hpt f hf) η hη
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  filter_upwards [scaledKernel_support_eventually ρ hρ.2.1 hr,
    self_mem_nhdsWithin] with ε hs hε
  have hk := scaledKernel_properties ρ hρ ε hε
  exact convolution_error_bound p hp hpt (ScaledKernelValue ρ ε) hk.1.continuous.measurable
    (hk.1.continuous.integrable_of_hasCompactSupport hk.2.1) hk.2.2.1 hk.2.2.2
    f hfm η hηt (fun y hy => hball (hs hy))

theorem mollify_lp : LpApproximation := by
  intro d 𝕜 _ ρ hρ p hp hpt f hf
  refine ⟨fun ε hε => mollify_memLp ρ hρ p hp f hf hε, ?_⟩
  let : MeasurableSpace 𝕜 := borel 𝕜
  let f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have ht := mollify_eLpNorm_tendsto_of_measurable ρ hρ p hp hpt f' hfm (hf.ae_eq hff)
  convert ht using 1
  ext ε
  apply eLpNorm_congr_ae
  have hc : MollifyValue ρ ε f = MollifyValue ρ ε f' :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hff
  exact (EventuallyEq.of_eq hc).sub hff

end ExpandedFA.Distributions
