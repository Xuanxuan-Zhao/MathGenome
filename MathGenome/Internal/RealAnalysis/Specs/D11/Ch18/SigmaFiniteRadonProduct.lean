import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.FiniteRadonBorelProduct

/-! Full Borel section formulas in paper.tex:5453–5474. The product measure
has the Borel sigma-algebra of the product topology, without countability.
Restriction of sigma-algebras is expressed separately by `Measure.trim`. -/
namespace Specs.D11.Ch18.SigmaFiniteRadonProduct
open Set MeasureTheory
open scoped ENNReal
universe u v
local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

/-- The finite Borel restriction bridge used in the exhaustion argument. -/
def finite_borel_restriction : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : Measure X), RadonPredicates.isRadonValue μ →
    ∀ A : Set X, MeasurableSet[borel X] A → μ A < ∞ →
      RadonPredicates.isRadonValue (μ.restrict A) ∧ (μ.restrict A) univ < ∞

def increasing_finite_open_exhaustion : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : Measure X), RadonPredicates.isRadonValue μ → SigmaFinite μ →
    ∃ A : ℕ → Set X, (∀ n, IsOpen (A n) ∧ μ (A n) < ∞) ∧
      Monotone A ∧ ⋃ n, A n = univ

/-- Equality on all product-topology Borel sets, not merely on rectangles. -/
def finite_rectangle_restriction : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    SigmaFinite μ → SigmaFinite ν →
    ∀ (A : Set X) (B : Set Y), MeasurableSet[borel X] A →
      MeasurableSet[borel Y] B → μ A < ∞ → ν B < ∞ →
      (RadonProduct.radonProduct_value μ ν).restrict (A ×ˢ B) =
        RadonProduct.radonProduct_value (μ.restrict A) (ν.restrict B)

/-- Everywhere Borel section masses and both nonnegative integral identities. -/
def borel_integral_identity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet[borel (X × Y)] E →
      Measurable (fun x => ν {y | (x,y) ∈ E}) ∧
      Measurable (fun y => μ {x | (x,y) ∈ E}) ∧
      RadonProduct.radonProduct_value μ ν E = ∫⁻ x, ν {y | (x,y) ∈ E} ∂μ ∧
      RadonProduct.radonProduct_value μ ν E = ∫⁻ y, μ {x | (x,y) ∈ E} ∂ν

def ordinary_product_restriction : Prop :=
  SigmaFiniteRadonOrdinaryProduct.ordinary_product_restriction.{u,v}

def ordinary_product_apply : Prop :=
  SigmaFiniteRadonOrdinaryProduct.ordinary_product_apply.{u,v}

end Specs.D11.Ch18.SigmaFiniteRadonProduct
