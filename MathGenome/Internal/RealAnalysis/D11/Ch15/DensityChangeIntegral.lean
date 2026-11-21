import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.DensityChangeIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch05.DensityMeasureDomains
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries
import MathGenome.Internal.RealAnalysis.D11.Ch14.DensityMeasureVariation
import MathGenome.Internal.RealAnalysis.D11.Ch14.IntegralVariationBound

/-! Change of density, paper.tex:4947–4966. No Radon–Nikodym result is used.
The nonnegative formula is the simple-function/MCT theorem for withDensity.
Scalar integrability is established before transporting any scalar integral.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch15.DensityChangeIntegral
open D11.Ch05.NonnegativeIntegral
open D11.Ch06.ScalarIntegral
open D11.Ch14.ScalarIntegration
open D11.Ch14.DensityMeasureVariation
open D11.Ch14.TotalVariation

variable {X : Type u} [MeasurableSpace X]
variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

theorem nonnegative_change (μ : Measure X) (h g : X → ℝ≥0∞)
    (hh : Measurable h) (hg : Measurable g) :
    nonnegativeIntegral (D11.Ch05.DensityMeasureDomains.densityMeasure μ h) g =
      nonnegativeIntegral μ (fun x => g x * h x) := by
  change nonnegativeIntegral (μ.withDensity h) g = nonnegativeIntegral μ _
  simp_rw [integral_eq_lintegral]
  simpa only [Pi.mul_apply, mul_comm] using lintegral_withDensity_eq_lintegral_mul μ hh hg

theorem positive_scalar_integrable_iff (μ : Measure X) (h : X → ℝ≥0∞)
    (g : X → 𝕜) (hh : Measurable h) (_hfin : ∀ᵐ x ∂μ, h x < ∞)
    (hg : Measurable g) :
    scalarIntegrable (D11.Ch05.DensityMeasureDomains.densityMeasure μ h) g ↔
      nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖g x‖ * h x) < ∞ := by
  change (Measurable g ∧ nonnegativeIntegral
    (D11.Ch05.DensityMeasureDomains.densityMeasure μ h) _ < ∞) ↔ _
  rw [nonnegative_change μ h _ hh hg.norm.ennreal_ofReal]
  exact and_iff_right hg

theorem positive_scalar_change :
    Specs.D11.Ch15.DensityChangeIntegral.positive_scalar_change := by
  intro X _ 𝕜 _ _ _ μ h g hh hfin hgm hw
  have hg := (positive_scalar_integrable_iff μ h g hh hfin hgm).mpr hw
  have hgi : Integrable g (μ.withDensity h) := ((scalarIntegrable_iff _ _).mp hg).2
  have hgh : scalarIntegrable μ (fun x => (h x).toReal • g x) :=
    (scalarIntegrable_iff _ _).mpr ⟨hh.ennreal_toReal.smul hgm,
      (integrable_withDensity_iff_integrable_smul' hh hfin).mp hgi⟩
  refine ⟨hg, hgh, ?_⟩
  exact integral_withDensity_eq_integral_toReal_smul hh hfin g

theorem signed_scalar_change (μ : Measure X) (k : X → ℝ)
    (hk : scalarIntegrable μ k) (g : X → 𝕜) (hgm : Measurable g)
    (hw : nonnegativeIntegral μ
      (fun x => ENNReal.ofReal ‖g x‖ * ENNReal.ofReal ‖k x‖) < ∞) :
    ∃ (hg : signedIntegrable (densityMeasure μ k hk) g)
      (hgk : scalarIntegrable μ (fun x => k x • g x)),
      signedIntegral _ g hg = scalarIntegral μ _ hgk := by
  have hkm : Measurable (fun x => ENNReal.ofReal ‖k x‖) := hk.1.norm.ennreal_ofReal
  have hgν : signedIntegrable (densityMeasure μ k hk) g := by
    change scalarIntegrable (totalVariation (densityMeasure μ k hk)) g
    rw [densityMeasure_variation μ k hk]
    change scalarIntegrable (D11.Ch05.DensityMeasureDomains.densityMeasure μ _) g
    exact (positive_scalar_integrable_iff μ _ g hkm
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) hgm).mpr hw
  obtain ⟨hgp, hgn⟩ := signed_parts_integrable _ g hgν
  obtain ⟨hp, hn⟩ := densityMeasure_jordan μ k hk
  rw [hp] at hgp
  rw [hn] at hgn
  let p := D11.Ch06.ScalarIntegral.positivePart k
  let n := D11.Ch06.ScalarIntegral.negativePart k
  have hpm : Measurable p := hk.1.max measurable_const
  have hnm : Measurable n := hk.1.neg.max measurable_const
  have hp0 : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hn0 : ∀ x, 0 ≤ n x := fun x => le_max_right _ _
  have hpg : Integrable (fun x => p x • g x) μ := by
    have H := (integrable_withDensity_iff_integrable_smul' hpm.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hgp
    simpa only [ENNReal.toReal_ofReal (hp0 _)] using H
  have hng : Integrable (fun x => n x • g x) μ := by
    have H := (integrable_withDensity_iff_integrable_smul' hnm.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hgn
    simpa only [ENNReal.toReal_ofReal (hn0 _)] using H
  have hsplit : (fun x => p x • g x - n x • g x) = (fun x => k x • g x) := by
    funext x
    rw [← sub_smul]
    have H : p x - n x = k x := (parts_identities k x).2.2.2.symm
    rw [H]
  have hgk : scalarIntegrable μ (fun x => k x • g x) :=
    (scalarIntegrable_iff _ _).mpr ⟨hk.1.smul hgm, hsplit ▸ hpg.sub hng⟩
  refine ⟨hgν, hgk, ?_⟩
  change (∫ x, g x ∂(D11.Ch14.Jordan.positivePart (densityMeasure μ k hk))) -
    (∫ x, g x ∂(D11.Ch14.Jordan.negativePart (densityMeasure μ k hk))) =
      ∫ x, k x • g x ∂μ
  rw [hp, hn,
    integral_withDensity_eq_integral_toReal_smul hpm.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hnm.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp0 _), ENNReal.toReal_ofReal (hn0 _)]
  rw [← integral_sub hpg hng, hsplit]

/-- Coordinate measures of a scalar density use the same positive reference. -/
theorem densityMeasure_re (μ : Measure X) (k : X → ℂ) (hk : scalarIntegrable μ k)
    (hkr : scalarIntegrable μ (fun x => (k x).re)) :
    ComplexMeasure.re (densityMeasure μ k hk) = densityMeasure μ (fun x => (k x).re) hkr := by
  apply VectorMeasure.ext
  intro E hE
  change (densityMeasure μ k hk E).re = _
  rw [densityMeasure_apply μ k hk E hE, densityMeasure_apply μ _ hkr E hE]
  exact (integral_re (((scalarIntegrable_iff μ k).mp hk).2.restrict)).symm

theorem densityMeasure_im (μ : Measure X) (k : X → ℂ) (hk : scalarIntegrable μ k)
    (hki : scalarIntegrable μ (fun x => (k x).im)) :
    ComplexMeasure.im (densityMeasure μ k hk) = densityMeasure μ (fun x => (k x).im) hki := by
  apply VectorMeasure.ext
  intro E hE
  change (densityMeasure μ k hk E).im = _
  rw [densityMeasure_apply μ k hk E hE, densityMeasure_apply μ _ hki E hE]
  exact (integral_im (((scalarIntegrable_iff μ k).mp hk).2.restrict)).symm

private theorem complex_product_split (a b : ℂ) :
    a * b = b.re • a + Complex.I * (b.im • a) := by
  simp only [Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im b]
  ring

theorem complex_scalar_change (μ : Measure X) (k : X → ℂ)
    (hk : scalarIntegrable μ k) (g : X → ℂ) (hgm : Measurable g)
    (hw : nonnegativeIntegral μ
      (fun x => ENNReal.ofReal ‖g x‖ * ENNReal.ofReal ‖k x‖) < ∞) :
    ∃ (hg : complexIntegrable (densityMeasure μ k hk) g)
      (hgk : scalarIntegrable μ (fun x => g x * k x)),
      complexIntegral _ g hg = scalarIntegral μ _ hgk := by
  have hki := ((scalarIntegrable_iff μ k).mp hk).2
  have hkr : scalarIntegrable μ (fun x => (k x).re) :=
    (scalarIntegrable_iff _ _).mpr ⟨Complex.continuous_re.measurable.comp hk.1, hki.re⟩
  have hkim : scalarIntegrable μ (fun x => (k x).im) :=
    (scalarIntegrable_iff _ _).mpr ⟨Complex.continuous_im.measurable.comp hk.1, hki.im⟩
  have hwcoord (c : ℂ → ℝ) (hc : ∀ z, ‖c z‖ ≤ ‖z‖) :
      nonnegativeIntegral μ
        (fun x => ENNReal.ofReal ‖g x‖ * ENNReal.ofReal ‖c (k x)‖) < ∞ := by
    rw [integral_eq_lintegral] at hw ⊢
    exact lt_of_le_of_lt (lintegral_mono fun x =>
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (hc (k x))) _) hw
  obtain ⟨hgr, hgkr, her⟩ := signed_scalar_change μ _ hkr g hgm
    (hwcoord Complex.re (fun z => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z))
  obtain ⟨hgi, hgki, hei⟩ := signed_scalar_change μ _ hkim g hgm
    (hwcoord Complex.im (fun z => by simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm z))
  have hgν : complexIntegrable (densityMeasure μ k hk) g := by
    change scalarIntegrable (totalVariation (densityMeasure μ k hk)) g
    rw [densityMeasure_variation μ k hk]
    change scalarIntegrable (D11.Ch05.DensityMeasureDomains.densityMeasure μ _) g
    exact (positive_scalar_integrable_iff μ _ g hk.1.norm.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) hgm).mpr hw
  have hpr := ((scalarIntegrable_iff _ _).mp hgkr).2
  have hpi := ((scalarIntegrable_iff _ _).mp hgki).2
  have hsplit : (fun x => g x * k x) =
      (fun x => (k x).re • g x + Complex.I * ((k x).im • g x)) :=
    funext fun x => complex_product_split _ _
  have hgk : scalarIntegrable μ (fun x => g x * k x) :=
    (scalarIntegrable_iff _ _).mpr ⟨hgm.mul hk.1,
      hsplit.symm ▸ hpr.add (hpi.const_mul Complex.I)⟩
  refine ⟨hgν, hgk, ?_⟩
  have hre := densityMeasure_re μ k hk hkr
  have him := densityMeasure_im μ k hk hkim
  change signedIntegral _ g _ = ∫ x, (k x).re • g x ∂μ at her
  change signedIntegral _ g _ = ∫ x, (k x).im • g x ∂μ at hei
  change complexIntegral _ g _ = ∫ x, g x * k x ∂μ
  obtain ⟨hgr', hgi'⟩ := complex_parts_integrable _ g hgν
  rw [complexIntegral_eq_parts _ _ hgν hgr' hgi']
  have her' : signedIntegral (ComplexMeasure.re (densityMeasure μ k hk)) g hgr' =
      ∫ x, (k x).re • g x ∂μ := by
    simpa only [signedIntegral, hre] using her
  have hei' : signedIntegral (ComplexMeasure.im (densityMeasure μ k hk)) g hgi' =
      ∫ x, (k x).im • g x ∂μ := by
    simpa only [signedIntegral, him] using hei
  rw [her', hei', hsplit, integral_add hpr (hpi.const_mul Complex.I), integral_const_mul]

end D11.Ch15.DensityChangeIntegral
