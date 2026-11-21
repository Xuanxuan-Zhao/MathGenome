import MathGenome.Internal.RealAnalysis.D11.Ch18.SecondCountableBorelRegular
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.ProductBorelBridge

/-!
# Ordinary products and Borel products

`paper.tex:5428–5437`. Continuous projections give the inclusion for arbitrary
LCH Hausdorff factors. Second countability gives the reverse inclusion via
the library's product Borel-space instance. Compact-finite factors are
sigma-finite by the upstream Borel regularity theorem. Compact projections
bound the mass of any compact product subset by a finite rectangle mass.
The same Borel regularity theorem on the product then gives exactly the
three source Radon conditions. No completion or nonemptiness is assumed.
-/

namespace D11.Ch18.ProductBorelBridge

open Set MeasureTheory
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

theorem product_le_borel : Specs.D11.Ch18.ProductBorelBridge.product_le_borel.{u, v} := by
  intro X Y _ _ _ _ _ _
  exact prod_le_borel_prod

theorem product_eq_borel : Specs.D11.Ch18.ProductBorelBridge.product_eq_borel.{u, v} := by
  intro X Y _ _ _ _ _ _ _ _
  exact @BorelSpace.measurable_eq (X × Y) _ ((borel X).prod (borel Y))
    (Prod.borelSpace (α := X) (β := Y))

theorem compactFinite_sigmaFinite :
    Specs.D11.Ch18.ProductBorelBridge.compactFinite_sigmaFinite.{u} := by
  intro X _ _ _ _ μ hμ
  exact (SecondCountableBorelRegular.second_countable_regular μ hμ).1

/-- Apply the upstream Borel theorem with any explicitly identified Borel
structure; this lets the ordinary product keep its original measure type. -/
private theorem regular_of_compactFinite
    {Z : Type*} [TopologicalSpace Z] [T2Space Z] [LocallyCompactSpace Z]
    [SecondCountableTopology Z] [mZ : MeasurableSpace Z] [BorelSpace Z]
    (ρ : Measure Z) [IsFiniteMeasureOnCompacts ρ] : Measure.Regular ρ := by
  borelize Z
  exact (isRadon_iff_regular ρ).mp
    (SecondCountableBorelRegular.second_countable_regular ρ
      ((compactFinite_iff ρ).mpr inferInstance)).2.1

theorem product_radon : Specs.D11.Ch18.ProductBorelBridge.product_radon.{u, v} := by
  intro X Y _ _ _ _ _ _ _ _ μ ν hμ hν
  have hσμ : SigmaFinite μ := compactFinite_sigmaFinite μ hμ
  have hσν : SigmaFinite ν := compactFinite_sigmaFinite ν hν
  let : IsFiniteMeasureOnCompacts μ := (compactFinite_iff μ).mp hμ
  let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν
  -- The library instance uses K ⊆ fst '' K × snd '' K, compact projections,
  -- monotonicity, and the finite product bound; it needs no total finiteness.
  have : IsFiniteMeasureOnCompacts (μ.prod ν) := inferInstance
  exact ⟨hσμ, hσν, regular_of_compactFinite (μ.prod ν)⟩

end D11.Ch18.ProductBorelBridge
