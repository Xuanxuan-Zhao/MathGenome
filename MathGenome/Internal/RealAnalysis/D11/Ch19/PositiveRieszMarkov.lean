import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveContentIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch06.LinearityOrder
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveRieszMarkov

/-!
Positive Riesz–Markov on arbitrary LCH Hausdorff spaces.
Existence uses the previously constructed Borel measure and integral identity.
Uniqueness uses the native compact-support integral uniqueness theorem, after
transporting precisely the three shared Radon conditions to `Measure.Regular`.
The complex argument uses the existing real inclusion/restriction and real and
imaginary part maps; it introduces no new function space or conjugate pairing.
-/

open MeasureTheory
open D11.Ch06.ScalarIntegral
open D11.Ch19
open Specs.D11.Ch19.PositiveContentOuterMeasure (Positive)
open Specs.D11.Ch19.PositiveRieszMarkov (Represents ComplexPositive)

namespace D11.Ch19.PositiveRieszMarkov
universe u
noncomputable section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- Existence and uniqueness for positive real linear functionals on Cc. -/
theorem real_representation
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I) :
    ∃! μ : @Measure X (borel X), Represents I μ := by
  letI : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ := PositiveContentOuterMeasure.borelMeasure I hI
  have hμ : Represents I μ :=
    ⟨PositiveContentRadon.radon I hI, PositiveContentIntegral.integral_eq I hI⟩
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.1
  let : Measure.Regular ν := (D11.Ch18.isRadon_iff_regular ν).mp hν.1
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  obtain ⟨hfμ, heμ⟩ := hμ.2 f
  obtain ⟨hfν, heν⟩ := hν.2 f
  exact heν.symm.trans heμ

/-- Compact support gives actual Borel measurability and absolute integrability. -/
lemma radon_scalar_integrable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure X (borel X)) (hμ : D11.Ch18.isRadon μ)
    (f : CompactlySupportedContinuousMap X 𝕜) :
    letI : MeasurableSpace X := borel X
    scalarIntegrable μ f := by
  letI : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.1
  exact (scalarIntegrable_iff μ f).mpr ⟨f.continuous.measurable, f.integrable⟩

/-- Every positive Radon measure induces a positive real linear functional. -/
theorem radon_induces_real_functional
    (μ : @Measure X (borel X)) (hμ : D11.Ch18.isRadon μ) :
    ∃ I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ, Positive I ∧ Represents I μ := by
  letI : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.1
  let I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ :=
    (CompactlySupportedContinuousMap.integralPositiveLinearMap μ).toLinearMap
  refine ⟨I, ?_, hμ, ?_⟩
  · intro f hf
    exact integral_nonneg hf
  · intro f
    exact ⟨radon_scalar_integrable μ hμ f, rfl⟩

omit [T2Space X] [LocallyCompactSpace X] in
/-- Real functions have real functional values, with the original scalar inclusion. -/
lemma complex_ofReal_eq (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ)
    (hI : ComplexPositive I) (f : CompactlySupportedContinuousMap X ℝ) :
    I (ccOfReal f) = (realRestriction I f : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using positive_functional_ofReal_im I hI f

omit [T2Space X] [LocallyCompactSpace X] in
/-- The real and imaginary compact-support parts recover the complex value. -/
lemma complex_value_eq (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ)
    (hI : ComplexPositive I) (f : CompactlySupportedContinuousMap X ℂ) :
    I f = (realRestriction I (ccRe f) : ℂ) +
      Complex.I * (realRestriction I (ccIm f) : ℂ) := by
  have hsplit : f = ccOfReal (ccRe f) + Complex.I • ccOfReal (ccIm f) := by
    ext x
    simpa [CompactlySupportedContinuousMap.smul_apply, mul_comm] using
      (Complex.re_add_im (f x)).symm
  calc
    I f = I (ccOfReal (ccRe f)) + Complex.I • I (ccOfReal (ccIm f)) := by
      conv_lhs => rw [hsplit, map_add, map_smul]
    _ = _ := by rw [complex_ofReal_eq I hI, complex_ofReal_eq I hI]; rfl

/-- Restriction to real functions preserves exactly the representing measures. -/
lemma represents_realRestriction_iff
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ) (hI : ComplexPositive I)
    (μ : @Measure X (borel X)) :
    Represents (realRestriction I) μ ↔ Represents I μ := by
  letI : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro f
    have hf := radon_scalar_integrable μ h.1 f
    refine ⟨hf, ?_⟩
    obtain ⟨hr, er⟩ := h.2 (ccRe f)
    obtain ⟨hi, ei⟩ := h.2 (ccIm f)
    change I f = ∫ x, f x ∂μ
    rw [complex_value_eq I hI]
    change realRestriction I (ccRe f) = ∫ x, (f x).re ∂μ at er
    change realRestriction I (ccIm f) = ∫ x, (f x).im ∂μ at ei
    rw [er, ei]
    have hs := integral_re_add_im ((scalarIntegrable_iff μ f).mp hf).2
    simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
      RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal, mul_comm] using hs
  · intro h
    refine ⟨h.1, ?_⟩
    intro f
    refine ⟨radon_scalar_integrable μ h.1 f, ?_⟩
    obtain ⟨hf, he⟩ := h.2 (ccOfReal f)
    change I (ccOfReal f) = ∫ x, (f x : ℂ) ∂μ at he
    rw [integral_complex_ofReal] at he
    exact congrArg Complex.re he

/-- Complex positive functionals have a unique positive Radon representing measure. -/
theorem complex_representation
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ) (hI : ComplexPositive I) :
    ∃! μ : @Measure X (borel X), Represents I μ := by
  obtain ⟨μ, hμ, huniq⟩ := real_representation (realRestriction I)
    (realRestriction_nonneg I hI)
  exact ⟨μ, (represents_realRestriction_iff I hI μ).mp hμ,
    fun ν hν => huniq ν ((represents_realRestriction_iff I hI ν).mpr hν)⟩

/-- The representing positive measure is unchanged by real restriction. -/
theorem real_complex_compatibility
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ) (hI : ComplexPositive I) :
    ∃ J : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ,
      Positive J ∧
      (∀ (f : CompactlySupportedContinuousMap X ℝ)
        (g : CompactlySupportedContinuousMap X ℂ),
        (∀ x, g x = (f x : ℂ)) → I g = (J f : ℂ)) ∧
      ∀ μ : @Measure X (borel X), Represents J μ ↔ Represents I μ := by
  refine ⟨realRestriction I, realRestriction_nonneg I hI, ?_,
    represents_realRestriction_iff I hI⟩
  intro f g hfg
  have hg : g = ccOfReal f := by ext x; exact hfg x
  rw [hg]
  exact complex_ofReal_eq I hI f

/-- Integration against a positive Radon measure is complex-linear and positive. -/
theorem radon_induces_complex_functional
    (μ : @Measure X (borel X)) (hμ : D11.Ch18.isRadon μ) :
    ∃ I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ,
      ComplexPositive I ∧ Represents I μ := by
  letI : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.1
  let I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add' f.integrable g.integrable
      map_smul' := fun a f => integral_smul a f }
  refine ⟨I, ?_, hμ, ?_⟩
  · intro f hf
    change 0 ≤ (∫ x, f x ∂μ).re ∧ (∫ x, f x ∂μ).im = 0
    constructor
    · change 0 ≤ RCLike.re (∫ x, f x ∂μ)
      rw [← integral_re f.integrable]
      exact integral_nonneg (fun x => (hf x).1)
    · change RCLike.im (∫ x, f x ∂μ) = 0
      rw [← integral_im f.integrable]
      change (∫ x, (f x).im ∂μ) = 0
      simp only [show (fun x => (f x).im) = (fun _ => 0) from funext (fun x => (hf x).2)]
      exact integral_zero X ℝ
  · intro f
    exact ⟨radon_scalar_integrable μ hμ f, rfl⟩

end
end D11.Ch19.PositiveRieszMarkov
