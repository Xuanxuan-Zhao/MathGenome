import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonProduct
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProductSwap

/-! Swapping coordinates preserves the defining Cc functional and transports
Radon regularity by a homeomorphism. Uniqueness therefore identifies the
pushforward on the entire Borel sigma-algebra of the product topology. -/

noncomputable section
namespace D11.Ch18.RadonProductSwap

open Set MeasureTheory
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

theorem map_swap : Specs.D11.Ch18.RadonProductSwap.map_swap.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let : MeasurableSpace (Y × X) := borel (Y × X)
  let : BorelSpace (Y × X) := ⟨rfl⟩
  let ρ := RadonProduct.radonProduct μ ν
  have hρ : isRadon ρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  let : Measure.Regular ρ := (isRadon_iff_regular ρ).mp hρ
  let e : (X × Y) ≃ₜ (Y × X) := Homeomorph.prodComm X Y
  have hm : Measure.Regular (Measure.map e ρ) := Measure.Regular.map e
  have hr : isRadon (Measure.map e ρ) := (isRadon_iff_regular _).mpr hm
  change Measure.map e ρ = RadonProduct.radonProduct ν μ
  apply RadonProduct.unique Y X ν μ hν hμ _ hr
  intro f
  let g : CompactlySupportedContinuousMap (X × Y) ℝ := f.comp e.toCocompactMap
  have hi := RadonProduct.integral_identity X Y ℝ μ ν hμ hν g
  -- Both sides are integrals of Cc functions against compact-finite measures.
  have hg : Integrable g ρ := hi.2.1
  let : IsFiniteMeasureOnCompacts (Measure.map e ρ) := hm.toIsFiniteMeasureOnCompacts
  have hf : Integrable f (Measure.map e ρ) := f.integrable
  calc
    (∫ p, f p ∂(Measure.map e ρ)) = ∫ p, g p ∂ρ := by
      exact integral_map e.continuous.measurable.aemeasurable hf.aestronglyMeasurable
    _ = ∫ y, (∫ x, g (x,y) ∂μ) ∂ν := hi.2.2.2.2.2.2.2
    _ = ∫ y, (∫ x, f (y,x) ∂μ) ∂ν := rfl

theorem borel_swap : Specs.D11.Ch18.RadonProductSwap.borel_swap.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν E hE
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let : MeasurableSpace (Y × X) := borel (Y × X)
  let : BorelSpace (Y × X) := ⟨rfl⟩
  rw [← map_swap Y X ν μ hν hμ]
  exact Measure.map_apply (Homeomorph.prodComm Y X).continuous.measurable hE

theorem open_swap : Specs.D11.Ch18.RadonProductSwap.open_swap.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν E hE
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  exact borel_swap X Y μ ν hμ hν E hE.measurableSet

end D11.Ch18.RadonProductSwap
