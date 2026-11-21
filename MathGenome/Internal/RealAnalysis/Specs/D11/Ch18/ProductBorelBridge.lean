import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure

/-!
Independent statements for `paper.tex:5428–5437`.

The two measurable structures are explicit: the ordinary product of the
factor Borel structures and the Borel structure of the topological product.
Equality is asserted only under second countability. The product measure is
the shared ordinary product, without completion. `Measure.Regular` has
exactly the three manuscript Radon conditions, as identified by the upstream
`RadonPredicates.isRadon_iff_regular`; the equality of measurable structures
ensures that its measurable-set quantifier is exactly the product Borel domain.
The factors' sigma-finiteness is a conclusion, not a hypothesis.
-/

namespace Specs.D11.Ch18.ProductBorelBridge

open Set MeasureTheory
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

def product_le_borel : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y],
    (borel X).prod (borel Y) ≤ borel (X × Y)

def product_eq_borel : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y],
    (borel X).prod (borel Y) = borel (X × Y)

def compactFinite_sigmaFinite : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (μ : @Measure X (borel X)),
    RadonPredicates.compactFiniteValue μ → SigmaFinite μ

def product_radon : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : @Measure X (borel X)) (ν : @Measure Y (borel Y)),
    RadonPredicates.compactFiniteValue μ → RadonPredicates.compactFiniteValue ν →
    SigmaFinite μ ∧ SigmaFinite ν ∧
      Measure.Regular (Specs.D11.Ch08.ProductMeasure.productMeasure_value μ ν)

end Specs.D11.Ch18.ProductBorelBridge
