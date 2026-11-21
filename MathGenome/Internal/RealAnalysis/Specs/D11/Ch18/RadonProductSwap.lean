import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProduct

/-! Coordinate interchange on the full topological-product Borel domains.
The factors are arbitrary Radon measures on LCH Hausdorff spaces; no mass
or countability hypothesis is imposed. -/

namespace Specs.D11.Ch18.RadonProductSwap

open Set MeasureTheory
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

/-- Pushforward commutation for the existing canonical Radon product. -/
def map_swap : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    letI : MeasurableSpace (X × Y) := borel (X × Y)
    letI : MeasurableSpace (Y × X) := borel (Y × X)
    Measure.map Prod.swap (RadonProduct.radonProduct_value μ ν) =
      RadonProduct.radonProduct_value ν μ

/-- The preimage is a subset of Y × X, with its full Borel structure. -/
def borel_swap : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ E : Set (X × Y), MeasurableSet[borel (X × Y)] E →
      RadonProduct.radonProduct_value μ ν E =
        RadonProduct.radonProduct_value ν μ (Prod.swap ⁻¹' E)

/-- The open-set specialization needed for the second section formula. -/
def open_swap : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ E : Set (X × Y), IsOpen E →
      RadonProduct.radonProduct_value μ ν E =
        RadonProduct.radonProduct_value ν μ (Prod.swap ⁻¹' E)

end Specs.D11.Ch18.RadonProductSwap
