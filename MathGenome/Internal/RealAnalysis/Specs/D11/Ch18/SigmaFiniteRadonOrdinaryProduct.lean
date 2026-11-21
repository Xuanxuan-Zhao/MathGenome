import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProductOpenRectangles
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Integral.Prod

/-! The ordinary-product restriction stage of paper.tex:5453–5464.
The Borel sigma-algebra of the product topology is never identified with the
product of the factor Borel sigma-algebras. Restriction to that smaller domain
is `Measure.trim`; the setwise conclusion quantifies only over its measurable
sets. No second countability, sigma-compactness, or finite total mass is added. -/

namespace Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct

open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

/-- Sigma-finite Radon measures have countable covers by finite-mass opens. -/
def finite_open_cover : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : Measure X), RadonPredicates.isRadonValue μ → SigmaFinite μ →
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n) ∧ μ (U n) < ∞) ∧ ⋃ n, U n = univ

/-- Equality of measures on exactly the ordinary product sigma-algebra. -/
def ordinary_product_restriction : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    SigmaFinite μ → SigmaFinite ν →
      (RadonProduct.radonProduct_value μ ν).trim prod_le_borel_prod = μ.prod ν

/-- In particular, evaluation agrees on every product-measurable set. -/
def ordinary_product_apply : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet[(borel X).prod (borel Y)] E →
      RadonProduct.radonProduct_value μ ν E = (μ.prod ν) E

/-- Ordinary Fubini for Cc tests, with absolute integrability and transfer of
the integral from the larger Borel domain to the ordinary product domain. -/
def cc_fubini : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    SigmaFinite μ → SigmaFinite ν →
    ∀ f : CompactlySupportedContinuousMap (X × Y) 𝕜,
      @Measurable (X × Y) 𝕜 ((borel X).prod (borel Y)) (borel 𝕜) f ∧
      Integrable f (RadonProduct.radonProduct_value μ ν) ∧
      Integrable f (μ.prod ν) ∧
      Integrable (fun x => ∫ y, f (x,y) ∂ν) μ ∧
      Integrable (fun y => ∫ x, f (x,y) ∂μ) ν ∧
      (∫ p, f p ∂(RadonProduct.radonProduct_value μ ν)) = ∫ p, f p ∂(μ.prod ν) ∧
      (∫ p, f p ∂(μ.prod ν)) = ∫ x, (∫ y, f (x,y) ∂ν) ∂μ ∧
      (∫ p, f p ∂(μ.prod ν)) = ∫ y, (∫ x, f (x,y) ∂μ) ∂ν

end Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct
