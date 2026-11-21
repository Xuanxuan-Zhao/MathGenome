import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProduct

/-! Open-rectangle stage of paper.tex:5459–5462. The factors have exactly
 their Borel sigma-algebras; the product has the product topology's Borel
 sigma-algebra. No sigma-finiteness or countability is imposed. ENNReal
 multiplication includes zero times infinity and empty rectangles. -/

namespace Specs.D11.Ch18.RadonProductOpenRectangles
open Set MeasureTheory
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

def open_rectangle : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ (U : Set X) (V : Set Y), IsOpen U → IsOpen V →
      RadonProduct.radonProduct_value μ ν (U ×ˢ V) = μ U * ν V

end Specs.D11.Ch18.RadonProductOpenRectangles
