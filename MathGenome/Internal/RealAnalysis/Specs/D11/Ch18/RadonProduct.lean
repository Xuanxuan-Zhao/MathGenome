import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CcIteratedIntegrals

/-! Independent statements for paper.tex:5444–5455. The factors and the
resulting measure have exactly their Borel domains. The product topology's
Borel sigma-algebra is kept distinct from the factor product sigma-algebra.
No countability, sigma-finiteness, or nonemptiness assumptions are imposed. -/

noncomputable section
namespace Specs.D11.Ch18.RadonProduct

open Set MeasureTheory
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]

/-- The real universal property, including actual absolute integrability. -/
def RealProductLaw (μ : Measure X) (ν : Measure Y)
    (ρ : @Measure (X × Y) (borel (X × Y))) : Prop :=
  RadonPredicates.isRadonValue ρ ∧
    ∀ f : CompactlySupportedContinuousMap (X × Y) ℝ,
      Integrable f ρ ∧
      (∫ p, f p ∂ρ) = ∫ x, (∫ y, f (x,y) ∂ν) ∂μ

def radonProduct_type :=
  {X : Type u} → [TopologicalSpace X] → [T2Space X] → [LocallyCompactSpace X] →
  {Y : Type v} → [TopologicalSpace Y] → [T2Space Y] → [LocallyCompactSpace Y] →
  Measure X → Measure Y → @Measure (X × Y) (borel (X × Y))

/-- A total choice definition. Existence under the Radon hypotheses is a
theorem below, not a certificate assumed by this definition. Uniqueness makes
the chosen value canonical for Radon factors. -/
def radonProduct_value : radonProduct_type.{u,v} :=
  fun μ ν => Classical.epsilon (RealProductLaw μ ν)

def exists_unique : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
      ∃! ρ : @Measure (X × Y) (borel (X × Y)), RealProductLaw μ ν ρ

def radonProduct_isRadon : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
      RadonPredicates.isRadonValue (radonProduct_value μ ν)

/-- Both orders of the universal identity, for real and complex scalars.
All three displayed scalar integrals are absolutely integrable, both outer
integrands are Borel measurable, and the test is Borel measurable on the product topology. -/
def integral_identity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ f : CompactlySupportedContinuousMap (X × Y) 𝕜,
      @Measurable (X × Y) 𝕜 (borel (X × Y)) (borel 𝕜) f ∧
      Integrable f (radonProduct_value μ ν) ∧
      Measurable (fun x => ∫ y, f (x,y) ∂ν) ∧
      Integrable (fun x => ∫ y, f (x,y) ∂ν) μ ∧
      Measurable (fun y => ∫ x, f (x,y) ∂μ) ∧
      Integrable (fun y => ∫ x, f (x,y) ∂μ) ν ∧
      (∫ p, f p ∂(radonProduct_value μ ν)) =
        ∫ x, (∫ y, f (x,y) ∂ν) ∂μ ∧
      (∫ p, f p ∂(radonProduct_value μ ν)) =
        ∫ y, (∫ x, f (x,y) ∂μ) ∂ν

/-- Uniqueness among all Radon Borel measures requires only the real tests. -/
def unique : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ ρ : @Measure (X × Y) (borel (X × Y)),
      RadonPredicates.isRadonValue ρ →
      (∀ f : CompactlySupportedContinuousMap (X × Y) ℝ,
        (∫ p, f p ∂ρ) = ∫ x, (∫ y, f (x,y) ∂ν) ∂μ) →
      ρ = radonProduct_value μ ν

def measurable_finite_rectangle : Prop :=
  CcIteratedIntegrals.measurable_finite_rectangle.{u,v}

def iterated_integrals : Prop := CcIteratedIntegrals.iterated_integrals.{u,v}

end Specs.D11.Ch18.RadonProduct
