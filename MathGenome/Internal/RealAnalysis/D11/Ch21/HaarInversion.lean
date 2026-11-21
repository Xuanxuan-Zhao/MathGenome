import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportNonnegative
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarInversion

/-!
# Inversion exchanges left and right Haar measures

The inversion homeomorphism preserves precisely the Chapter 18 Radon class.
The integral formulas use the earlier arbitrary-measure transport theorems.
Setwise Haar invariance is proved directly: it needs no jointly measurable
multiplication for the product of two Borel sigma-algebras, and no countability
assumption on the group. No Haar existence or uniqueness theorem is used.
-/
namespace D11.Ch21.HaarInversion

open Set MeasureTheory
open scoped Pointwise ENNReal
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The positive Borel measure obtained by inversion. -/
noncomputable def inversionMeasure {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (μ : @Measure G (borel G)) : @Measure G (borel G) :=
  μ.inv

theorem inversionMeasure_apply (μ : @Measure G (borel G)) (E : Set G)
    (_hE : MeasurableSet E) :
    inversionMeasure μ E = μ ((fun x : G => x⁻¹) '' E) := by
  simpa only [inversionMeasure, image_inv_eq_inv] using μ.inv_apply E

theorem inversionMeasure_involutive (μ : @Measure G (borel G)) :
    inversionMeasure (inversionMeasure μ) = μ := μ.inv_inv

theorem inversionMeasure_nonzero_iff (μ : @Measure G (borel G)) :
    inversionMeasure μ ≠ 0 ↔ μ ≠ 0 := by
  constructor
  · intro h hμ
    apply h
    simp [inversionMeasure, Measure.inv, hμ]
  · intro h hμ
    apply h
    rw [← inversionMeasure_involutive μ, hμ]
    simp [inversionMeasure, Measure.inv]

/-- Homeomorphism transport preserves compact finiteness, outer regularity on
Borel sets, and compact-inner regularity on opens. -/
theorem inversionMeasure_radon [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)) (hμ : D11.Ch18.isRadon μ) :
    D11.Ch18.isRadon (inversionMeasure μ) := by
  let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ
  exact (D11.Ch18.isRadon_iff_regular (inversionMeasure μ)).mpr
    (Measure.Regular.map (Homeomorph.inv G))

theorem inversion_lintegral (μ : @Measure G (borel G)) (f : G → ℝ≥0∞)
    (hf : Measurable f) :
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral (inversionMeasure μ) f =
      D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ (fun x => f x⁻¹) :=
  D11.Ch09.TransportNonnegative.transport_nonnegative
    (fun x : G => x⁻¹) measurable_inv μ f hf

theorem inversion_integrable_iff {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)) (f : G → 𝕜) (hf : Measurable f) :
    D11.Ch06.ScalarIntegral.scalarIntegrable (inversionMeasure μ) f ↔
      D11.Ch06.ScalarIntegral.scalarIntegrable μ (fun x => f x⁻¹) :=
  D11.Ch09.TransportIntegrable.transport_integrable_iff
    (fun x : G => x⁻¹) measurable_inv μ f hf

theorem inversion_integral {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)) (f : G → 𝕜)
    (hf : D11.Ch06.ScalarIntegral.scalarIntegrable (inversionMeasure μ) f) :
    ∃ hc : D11.Ch06.ScalarIntegral.scalarIntegrable μ (fun x => f x⁻¹),
      D11.Ch06.ScalarIntegral.scalarIntegral (inversionMeasure μ) f hf =
        D11.Ch06.ScalarIntegral.scalarIntegral μ (fun x => f x⁻¹) hc :=
  D11.Ch09.TransportIntegrable.transport_integral
    (fun x : G => x⁻¹) measurable_inv μ f hf

variable [T2Space G] [LocallyCompactSpace G]

/-- `(E a)⁻¹ = a⁻¹ E⁻¹` transfers left invariance to right invariance. -/
theorem rightHaar_inversionMeasure (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) :
    D11.Ch21.isRightHaarMeasure (inversionMeasure μ) := by
  refine ⟨(inversionMeasure_nonzero_iff μ).mpr hμ.1,
    inversionMeasure_radon μ hμ.2.1, ?_⟩
  intro a E hE
  change μ.inv ((fun x => x * a) '' E) = μ.inv E
  rw [Measure.inv_apply, Measure.inv_apply]
  have heq : ((fun x => x * a) '' E)⁻¹ = (fun x => a⁻¹ * x) '' E⁻¹ := by
    simp only [← image_inv_eq_inv, image_image, mul_inv_rev]
  rw [heq]
  exact hμ.2.2 a⁻¹ E⁻¹ hE.inv

/-- `(a E)⁻¹ = E⁻¹ a⁻¹` gives the reverse exchange. -/
theorem leftHaar_inversionMeasure (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isRightHaarMeasure μ) :
    D11.Ch21.isLeftHaarMeasure (inversionMeasure μ) := by
  refine ⟨(inversionMeasure_nonzero_iff μ).mpr hμ.1,
    inversionMeasure_radon μ hμ.2.1, ?_⟩
  intro a E hE
  change μ.inv ((fun x => a * x) '' E) = μ.inv E
  rw [Measure.inv_apply, Measure.inv_apply]
  have heq : ((fun x => a * x) '' E)⁻¹ = (fun x => x * a⁻¹) '' E⁻¹ := by
    simp only [← image_inv_eq_inv, image_image, mul_inv_rev]
  rw [heq]
  exact hμ.2.2 a⁻¹ E⁻¹ hE.inv

theorem inversion_rightHaar_iff (μ : @Measure G (borel G)) :
    D11.Ch21.isRightHaarMeasure (inversionMeasure μ) ↔ D11.Ch21.isLeftHaarMeasure μ := by
  constructor
  · intro h
    simpa only [inversionMeasure_involutive] using leftHaar_inversionMeasure _ h
  · exact rightHaar_inversionMeasure μ

theorem inversion_leftHaar_iff (μ : @Measure G (borel G)) :
    D11.Ch21.isLeftHaarMeasure (inversionMeasure μ) ↔ D11.Ch21.isRightHaarMeasure μ := by
  constructor
  · intro h
    simpa only [inversionMeasure_involutive] using rightHaar_inversionMeasure _ h
  · exact leftHaar_inversionMeasure μ

end D11.Ch21.HaarInversion
