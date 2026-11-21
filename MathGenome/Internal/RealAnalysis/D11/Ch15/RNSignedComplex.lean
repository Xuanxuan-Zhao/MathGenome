import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNSignedComplex
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNPositiveSigmaFinite
import MathGenome.Internal.RealAnalysis.D11.Ch15.AbsoluteContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch14.DensityMeasureVariation

/-! Finite real and complex Radon–Nikodym, paper.tex:4876–4891.
Positive RN is applied to finite Jordan parts. The complex density combines
the real and imaginary densities. Variation and a.e. uniqueness are then
deduced from the canonical vector measure of set integrals. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.RNSignedComplex

open Ch14.Jordan Ch14.TotalVariation

variable {X : Type u} [MeasurableSpace X]

theorem exists_positive_density (μ ρ : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ρ] (hac : ρ ≪ μ) :
    ∃ f : X → ℝ, Measurable f ∧ Integrable f μ ∧
      μ.withDensityᵥ f = ρ.toSignedMeasure := by
  obtain ⟨h, hm, _, hr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere μ ρ hac
  have heq : μ.withDensity h = ρ := by
    ext E hE
    rw [withDensity_apply _ hE, hr E hE]
    exact (Ch05.NonnegativeIntegral.eq_lintegral (μ.restrict E) h hm).symm
  have hfin : (∫⁻ x, h x ∂μ) ≠ ∞ := by
    have hu : (∫⁻ x, h x ∂μ) = ρ univ := by
      rw [← heq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [hu]
    exact measure_ne_top ρ univ
  refine ⟨fun x => (h x).toReal, hm.ennreal_toReal,
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin, ?_⟩
  simpa only [heq] using withDensityᵥ_toReal hm.aemeasurable hfin

theorem exists_signed_density (μ : Measure X) [SigmaFinite μ]
    (ν : SignedMeasure X) (hac : AbsoluteContinuity.scalarAbsolutelyContinuous ν μ) :
    ∃ f : X → ℝ, Measurable f ∧ Integrable f μ ∧ μ.withDensityᵥ f = ν := by
  have hparts : positivePart ν + negativePart ν ≪ μ := by
    rw [← signed_totalVariation_eq_jordan]
    exact hac
  have hp : positivePart ν ≪ μ :=
    (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)).trans hparts
  have hn : negativePart ν ≪ μ :=
    (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)).trans hparts
  obtain ⟨p, hpm, hpi, hpr⟩ := exists_positive_density μ (positivePart ν) hp
  obtain ⟨n, hnm, hni, hnr⟩ := exists_positive_density μ (negativePart ν) hn
  refine ⟨fun x => p x - n x, hpm.sub hnm, hpi.sub hni, ?_⟩
  rw [withDensityᵥ_sub' hpi hni, hpr, hnr]
  exact (signed_eq_of_difference ν _ _ (jordan_decomposition ν).2).symm

theorem exists_complex_density (μ : Measure X) [SigmaFinite μ]
    (ν : ComplexMeasure X) (hac : AbsoluteContinuity.scalarAbsolutelyContinuous ν μ) :
    ∃ f : X → ℂ, Measurable f ∧ Integrable f μ ∧ μ.withDensityᵥ f = ν := by
  have hv := (AbsoluteContinuity.scalar_iff ν μ).mp hac
  have hr : AbsoluteContinuity.scalarAbsolutelyContinuous ν.re μ := by
    apply (AbsoluteContinuity.scalar_iff _ _).mpr
    intro E hE hzero
    change (ν E).re = 0
    rw [hv E hE hzero, Complex.zero_re]
  have hi : AbsoluteContinuity.scalarAbsolutelyContinuous ν.im μ := by
    apply (AbsoluteContinuity.scalar_iff _ _).mpr
    intro E hE hzero
    change (ν E).im = 0
    rw [hv E hE hzero, Complex.zero_im]
  obtain ⟨p, hpm, hpi, hpr⟩ := exists_signed_density μ ν.re hr
  obtain ⟨n, hnm, hni, hnr⟩ := exists_signed_density μ ν.im hi
  let f : X → ℂ := fun x => (p x : ℂ) + (n x : ℂ) * Complex.I
  have hfm : Measurable f := hpm.complex_ofReal.add
    (hnm.complex_ofReal.mul_const Complex.I)
  have hfi : Integrable f μ := hpi.ofReal.add (hni.ofReal.mul_const Complex.I)
  refine ⟨f, hfm, hfi, ?_⟩
  apply VectorMeasure.ext
  intro E hE
  rw [withDensityᵥ_apply hfi hE]
  dsimp only [f]
  have hpI : Integrable (fun x => (p x : ℂ)) (μ.restrict E) := hpi.ofReal.restrict
  have hnI : Integrable (fun x => (n x : ℂ) * Complex.I) (μ.restrict E) :=
    (hni.ofReal.mul_const Complex.I).restrict
  rw [integral_add hpI hnI, integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]
  have hpE : ∫ x in E, p x ∂μ = (ν E).re := by
    rw [← withDensityᵥ_apply hpi hE, hpr]
    rfl
  have hnE : ∫ x in E, n x ∂μ = (ν E).im := by
    rw [← withDensityᵥ_apply hni hE, hnr]
    rfl
  rw [hpE, hnE, Complex.re_add_im]

theorem density_conclusions {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : VectorMeasure X 𝕜) (h : X → 𝕜)
    (hm : Measurable h) (hi : Integrable h μ) (hr : μ.withDensityᵥ h = ν) :
    (∀ E, MeasurableSet E → ν E = ∫ x in E, h x ∂μ) ∧
    (∀ E, MeasurableSet E → totalVariation ν E =
      ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ) ∧
    ∀ k : X → 𝕜, Integrable k μ →
      (∀ E, MeasurableSet E → ν E = ∫ x in E, k x ∂μ) → h =ᵐ[μ] k := by
  have hs : Ch06.ScalarIntegral.scalarIntegrable μ h :=
    (Ch06.ScalarIntegral.scalarIntegrable_iff μ h).mpr ⟨hm, hi⟩
  refine ⟨fun E hE => ?_, fun E hE => ?_, ?_⟩
  · rw [← hr, withDensityᵥ_apply hi hE]
  · rw [← hr]
    exact Ch14.DensityMeasureVariation.densityMeasure_variation_apply μ h hs E hE
  · intro k hk hkr
    apply hi.ae_eq_of_withDensityᵥ_eq hk
    rw [hr]
    apply VectorMeasure.ext
    intro E hE
    rw [withDensityᵥ_apply hk hE]
    exact hkr E hE

theorem rn_signed : Specs.D11.Ch15.RNSignedComplex.rn_signed := by
  intro X _ μ _ ν hac
  obtain ⟨h, hm, hi, hr⟩ := exists_signed_density μ ν hac
  exact ⟨h, hm, hi, density_conclusions μ ν h hm hi hr⟩

theorem rn_complex : Specs.D11.Ch15.RNSignedComplex.rn_complex := by
  intro X _ μ _ ν hac
  obtain ⟨h, hm, hi, hr⟩ := exists_complex_density μ ν hac
  exact ⟨h, hm, hi, density_conclusions μ ν h hm hi hr⟩

end D11.Ch15.RNSignedComplex
