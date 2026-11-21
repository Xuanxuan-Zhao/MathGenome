import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException

/-!
Independent statements for `D11.08.null_sections`, paper.tex:2672–2683.
The product is the shared ordinary product measure on the rectangle-generated
sigma-algebra. Almost everywhere means outside a measurable null envelope in
the original factor space. Both factors are sigma-finite; no completeness,
finite total mass, or nonemptiness is required.
-/

open Set MeasureTheory
open Specs.D11.Ch04.AeCommonException (almostEverywhere_value)
open Specs.D11.Ch08.ProductMeasure (productMeasure_value)

universe u v
noncomputable section

namespace Specs.D11.Ch08.NullSections

def null_sections_left : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      (productMeasure_value μ ν E = 0 ↔
        almostEverywhere_value μ (fun x => ν {y | (x, y) ∈ E} = 0))

def null_sections_right : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      (productMeasure_value μ ν E = 0 ↔
        almostEverywhere_value ν (fun y => μ {x | (x, y) ∈ E} = 0))

/-- The two equivalences for the same product-measurable set. -/
def null_sections : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      (productMeasure_value μ ν E = 0 ↔
        almostEverywhere_value μ (fun x => ν {y | (x, y) ∈ E} = 0)) ∧
      (productMeasure_value μ ν E = 0 ↔
        almostEverywhere_value ν (fun y => μ {x | (x, y) ∈ E} = 0))

end Specs.D11.Ch08.NullSections
