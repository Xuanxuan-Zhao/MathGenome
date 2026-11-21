import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveRieszMarkov
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarTranslationIntegral

/-!
Measure invariance and translated integrals, paper.tex:5880–5887.
Translations are Borel homeomorphisms. Set invariance identifies their
pushforwards, so the Chapter 9 transport results apply without any size
assumption. Conversely, regularity is preserved by a homeomorphism and
real Cc tests determine a Radon measure on an arbitrary LCH Hausdorff space.
-/
namespace D11.Ch21.HaarTranslationIntegral

open MeasureTheory
open scoped ENNReal
open D11.Ch06.ScalarIntegral
open D11.Ch05.NonnegativeIntegral
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The Haar set condition identifies the pushforward by each left translation. -/
lemma map_left_translation_eq_self (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (a : G) :
    Measure.map (fun x => a * x) μ = μ := by
  let : BorelSpace G := ⟨rfl⟩
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (continuous_const_mul a).measurable hE]
  change μ ((Homeomorph.mulLeft a) ⁻¹' E) = μ E
  rw [← (Homeomorph.mulLeft a).image_symm]
  exact hμ.2.2 a⁻¹ E hE

/-- Nonnegative Borel integrals are invariant, with infinite values allowed. -/
theorem nonnegative_translation (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (a : G) (f : G → ℝ≥0∞)
    (hf : Measurable f) :
    nonnegativeIntegral μ (fun x => f (a⁻¹ * x)) = nonnegativeIntegral μ f := by
  let : BorelSpace G := ⟨rfl⟩
  have h := D11.Ch09.TransportNonnegative.transport_nonnegative
    (fun x => a⁻¹ * x) (continuous_const_mul a⁻¹).measurable μ f hf
  change nonnegativeIntegral (Measure.map (fun x => a⁻¹ * x) μ) f =
    nonnegativeIntegral μ (fun x => f (a⁻¹ * x)) at h
  rw [map_left_translation_eq_self μ hμ] at h
  exact h.symm

/-- Absolute integrability is preserved, for real and complex scalar functions. -/
theorem scalar_translation {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)) (hμ : D11.Ch21.isLeftHaarMeasure μ)
    (a : G) (f : G → 𝕜) (hf : scalarIntegrable μ f) :
    ∃ ht : scalarIntegrable μ (fun x => f (a⁻¹ * x)),
      scalarIntegral μ (fun x => f (a⁻¹ * x)) ht = scalarIntegral μ f hf := by
  let : BorelSpace G := ⟨rfl⟩
  have hmap := map_left_translation_eq_self μ hμ a⁻¹
  have hfm : scalarIntegrable (Measure.map (fun x => a⁻¹ * x) μ) f := by
    rwa [hmap]
  obtain ⟨ht, he⟩ := D11.Ch09.TransportIntegrable.transport_integral
    (fun x => a⁻¹ * x) (continuous_const_mul a⁻¹).measurable μ f hfm
  refine ⟨ht, ?_⟩
  change (∫ x, f (a⁻¹ * x) ∂μ) = ∫ x, f x ∂μ
  change (∫ x, f x ∂Measure.map (fun x => a⁻¹ * x) μ) =
    ∫ x, f (a⁻¹ * x) ∂μ at he
  rw [hmap] at he
  exact he.symm

/-- Equality on all real Cc translated tests forces the Haar set condition. -/
theorem leftHaar_of_test_translation (μ : @Measure G (borel G)) (hzero : μ ≠ 0)
    (hμ : D11.Ch18.isRadon μ)
    (htest : ∀ (a : G) (f : CompactlySupportedContinuousMap G ℝ),
      (∫ x, f (a⁻¹ * x) ∂μ) = ∫ x, f x ∂μ) :
    D11.Ch21.isLeftHaarMeasure μ := by
  let : BorelSpace G := ⟨rfl⟩
  let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ
  have hmap (a : G) : Measure.map (fun x => a⁻¹ * x) μ = μ := by
    let : Measure.Regular (Measure.map (fun x => a⁻¹ * x) μ) :=
      Measure.Regular.map (Homeomorph.mulLeft a⁻¹)
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    -- Both scalar integrals in transport are finite: the image measure is
    -- Radon and f is compactly supported. Transport also proves integrability
    -- of the translated test against μ before its integral is compared.
    have hmradon := (D11.Ch18.isRadon_iff_regular
      (Measure.map (fun x => a⁻¹ * x) μ)).mpr inferInstance
    have hf := D11.Ch19.PositiveRieszMarkov.radon_scalar_integrable
      (Measure.map (fun x => a⁻¹ * x) μ) hmradon f
    obtain ⟨ht, he⟩ := D11.Ch09.TransportIntegrable.transport_integral
      (fun x => a⁻¹ * x) (continuous_const_mul a⁻¹).measurable μ f hf
    exact he.trans (htest a f)
  refine ⟨hzero, hμ, ?_⟩
  intro a E hE
  have he := congrArg (fun ν : Measure G => ν E) (hmap a)
  rw [Measure.map_apply (continuous_const_mul a⁻¹).measurable hE] at he
  change μ ((Homeomorph.mulLeft a⁻¹) ⁻¹' E) = μ E at he
  rw [← (Homeomorph.mulLeft a⁻¹).image_symm] at he
  simpa only [Homeomorph.mulLeft_symm, inv_inv, Homeomorph.coe_mulLeft] using he

end D11.Ch21.HaarTranslationIntegral
