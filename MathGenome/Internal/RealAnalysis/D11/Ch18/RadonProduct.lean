import MathGenome.Internal.RealAnalysis.D11.Ch18.CcIteratedIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveRieszMarkov
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProduct

/-! The Radon product on the Borel sigma-algebra of the product topology.
We represent the positive real Cc iterated-integral functional using the
independently established positive Riesz–Markov theorem. Real and imaginary
parts then give the universal identity for both scalar fields. -/

noncomputable section
namespace D11.Ch18.RadonProduct

open Set MeasureTheory
open Specs.D11.Ch18.RadonProduct (RealProductLaw)
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]

/-- The canonical product, characterized below for all Radon factors. -/
def radonProduct : Specs.D11.Ch18.RadonProduct.radonProduct_type.{u,v} :=
  Specs.D11.Ch18.RadonProduct.radonProduct_value

theorem exists_unique : Specs.D11.Ch18.RadonProduct.exists_unique.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  obtain ⟨J, hJ⟩ := CcIteratedIntegrals.positive_linear_functional X Y μ ν hμ hν
  have hpos : Specs.D11.Ch19.PositiveContentOuterMeasure.Positive J.toLinearMap :=
    fun f hf => J.map_nonneg hf
  obtain ⟨ρ, hρ, hu⟩ := Ch19.PositiveRieszMarkov.real_representation J.toLinearMap hpos
  have hbridge (σ : @Measure (X × Y) (borel (X × Y))) :
      Specs.D11.Ch19.PositiveRieszMarkov.Represents J.toLinearMap σ ↔
        RealProductLaw μ ν σ := by
    constructor
    · intro h
      refine ⟨h.1, fun f => ?_⟩
      obtain ⟨hf, he⟩ := h.2 f
      exact ⟨((Ch06.ScalarIntegral.scalarIntegrable_iff σ f).mp hf).2,
        he.symm.trans (hJ f)⟩
    · intro h
      refine ⟨h.1, fun f => ?_⟩
      obtain ⟨hf, he⟩ := h.2 f
      exact ⟨(Ch06.ScalarIntegral.scalarIntegrable_iff σ f).mpr
        ⟨f.continuous.measurable, hf⟩, (hJ f).trans he.symm⟩
  exact ⟨ρ, (hbridge ρ).mp hρ, fun σ hσ => hu σ ((hbridge σ).mpr hσ)⟩

/-- The choice is justified by existence, with no extra hypotheses. -/
theorem radonProduct_law (μ : Measure X) (ν : Measure Y)
    (hμ : isRadon μ) (hν : isRadon ν) : RealProductLaw μ ν (radonProduct μ ν) := by
  exact Classical.epsilon_spec (exists_unique X Y μ ν hμ hν).exists

theorem radonProduct_isRadon : Specs.D11.Ch18.RadonProduct.radonProduct_isRadon.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  exact (radonProduct_law μ ν hμ hν).1

theorem unique : Specs.D11.Ch18.RadonProduct.unique.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν ρ hρ he
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let : IsFiniteMeasureOnCompacts ρ := (compactFinite_iff ρ).mp hρ.1
  exact (exists_unique X Y μ ν hμ hν).unique
    ⟨hρ, fun f => ⟨f.integrable, he f⟩⟩ (radonProduct_law μ ν hμ hν)

theorem integral_identity : Specs.D11.Ch18.RadonProduct.integral_identity.{u,v} := by
  intro X _ _ _ Y _ _ _ 𝕜 _ μ ν hμ hν f
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let ρ := radonProduct μ ν
  have hρ := radonProduct_law μ ν hμ hν
  let : IsFiniteMeasureOnCompacts ρ := (compactFinite_iff ρ).mp hρ.1.1
  obtain ⟨g, h, eg, eh, _, _, mg, mh, hg, hh⟩ :=
    CcIteratedIntegrals.section_integrals_cc X Y 𝕜 μ ν hμ hν f
  have mg' : Measurable (fun x => ∫ y, f (x,y) ∂ν) := by
    simpa only [show (g : X → 𝕜) = (fun x => ∫ y, f (x,y) ∂ν) from funext eg] using mg
  have mh' : Measurable (fun y => ∫ x, f (x,y) ∂μ) := by
    simpa only [show (h : Y → 𝕜) = (fun y => ∫ x, f (x,y) ∂μ) from funext eh] using mh
  have hg' : Integrable (fun x => ∫ y, f (x,y) ∂ν) μ := by
    simpa only [show (g : X → 𝕜) = (fun x => ∫ y, f (x,y) ∂ν) from funext eg] using hg
  have hh' : Integrable (fun y => ∫ x, f (x,y) ∂μ) ν := by
    simpa only [show (h : Y → 𝕜) = (fun y => ∫ x, f (x,y) ∂μ) from funext eh] using hh
  have hf : Integrable f ρ := f.integrable
  have hsec := (CcIteratedIntegrals.sections_integrable X Y 𝕜 μ ν hμ hν f).1
  let fr : CompactlySupportedContinuousMap (X × Y) ℝ :=
    ⟨⟨fun p => RCLike.re (f p), RCLike.continuous_re.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := RCLike.re) (by simp)⟩
  let fi : CompactlySupportedContinuousMap (X × Y) ℝ :=
    ⟨⟨fun p => RCLike.im (f p), RCLike.continuous_im.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := RCLike.im) (by simp)⟩
  have er := (hρ.2 fr).2
  have ei := (hρ.2 fi).2
  have e : (∫ p, f p ∂ρ) = ∫ x, (∫ y, f (x,y) ∂ν) ∂μ := by
    apply RCLike.ext
    · rw [← integral_re hf, ← integral_re hg']
      change (∫ p, fr p ∂ρ) = _
      rw [er]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => integral_re (hsec x).2)
    · rw [← integral_im hf, ← integral_im hg']
      change (∫ p, fi p ∂ρ) = _
      rw [ei]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => integral_im (hsec x).2)
  exact ⟨f.continuous.measurable, hf, mg', hg', mh', hh', e,
    e.trans (CcIteratedIntegrals.iterated_integrals X Y 𝕜 μ ν hμ hν f).2.2⟩

theorem measurable_finite_rectangle :
    Specs.D11.Ch18.RadonProduct.measurable_finite_rectangle.{u,v} :=
  CcIteratedIntegrals.measurable_finite_rectangle

theorem iterated_integrals : Specs.D11.Ch18.RadonProduct.iterated_integrals.{u,v} :=
  CcIteratedIntegrals.iterated_integrals

end D11.Ch18.RadonProduct
