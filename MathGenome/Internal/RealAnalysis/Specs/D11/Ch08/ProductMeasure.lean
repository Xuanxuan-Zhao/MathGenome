import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.SectionIntegralsOneSided
import Mathlib.MeasureTheory.Measure.Prod

/-!
Independent specification of `D11.08.product_measure`, paper.tex:2580–2616.
The factors carry arbitrary specified measurable spaces; the product space
is their ordinary product, identified with rectangle generation upstream.
Every assertion about the product below assumes sigma-finiteness of both
factors. Empty spaces and zero measures are allowed. Native `Measure` has
already been identified with the source's function on measurable sets, and
all evaluations in the assertions below are on measurable sets.

The canonical product operation reuses the native measure. Its behavior
outside the sigma-finite hypotheses is not part of this specification.
The section formulas use the shared supremum-of-finite-simple-functions
integral, rather than assuming its identification with the library integral.
Multiplication is ENNReal multiplication, so zero times infinity is zero.
-/

open Set MeasureTheory
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)
open scoped ENNReal

universe u v
noncomputable section

namespace Specs.D11.Ch08.ProductMeasure

def productMeasure_type :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y],
    Measure X → Measure Y → Measure (X × Y)

def productMeasure_value : productMeasure_type.{u, v} :=
  fun μ ν => μ.prod ν

def rectangle_value : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
      productMeasure_value μ ν (A ×ˢ B) = μ A * ν B

/-- The competing measure has no additional finiteness hypothesis. -/
def uniqueness : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ η : Measure (X × Y),
      (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
        η (A ×ˢ B) = μ A * ν B) → η = productMeasure_value μ ν

def sigma_finite : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
      SigmaFinite (productMeasure_value μ ν)

def section_integrands_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      Measurable (fun x : X => ν {y : Y | (x, y) ∈ E}) ∧
      Measurable (fun y : Y => μ {x : X | (x, y) ∈ E})

def section_formula_left : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      productMeasure_value μ ν E =
        nonnegativeIntegral_value μ (fun x : X => ν {y : Y | (x, y) ∈ E})

def section_formula_right : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      productMeasure_value μ ν E =
        nonnegativeIntegral_value ν (fun y : Y => μ {x : X | (x, y) ∈ E})

/-- Existence and uniqueness are characterized solely by rectangle values. -/
def exists_unique : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∃! η : Measure (X × Y),
      ∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
        η (A ×ˢ B) = μ A * ν B

/-- All conclusions for the same witness, with uniqueness among all measures
having the prescribed rectangle values. -/
def product_measure : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∃ η : Measure (X × Y),
      (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
        η (A ×ˢ B) = μ A * ν B) ∧
      SigmaFinite η ∧
      (∀ E : Set (X × Y), MeasurableSet E →
        Measurable (fun x : X => ν {y : Y | (x, y) ∈ E}) ∧
        Measurable (fun y : Y => μ {x : X | (x, y) ∈ E}) ∧
        η E = nonnegativeIntegral_value μ (fun x : X => ν {y : Y | (x, y) ∈ E}) ∧
        η E = nonnegativeIntegral_value ν (fun y : Y => μ {x : X | (x, y) ∈ E})) ∧
      (∀ θ : Measure (X × Y),
        (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
          θ (A ×ˢ B) = μ A * ν B) → θ = η)

end Specs.D11.Ch08.ProductMeasure
