import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Restrict

/-!
Independent statements for paper.tex:283–295 and 326–341.

The positive measure and trace measurable space are the shared native objects
from the prerequisites. Restriction on the ambient space is `Measure.restrict`;
restriction on the subtype is the pullback along its inclusion. Its evaluation
and comparison with the ambient restriction are asserted only for measurable E.
No nonemptiness or positivity of the measure is assumed. Partition cells may be
empty, as required in particular when X is empty.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch01.ExhaustionRestriction

def sigmaFinite_iff_disjoint_partition : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    SigmaFinite μ ↔ ∃ D : ℕ → Set α,
      (∀ n, MeasurableSet (D n) ∧ μ (D n) < ∞) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧ (⋃ n, D n) = univ

def sigmaFinite_iff_increasing_exhaustion : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    SigmaFinite μ ↔ ∃ F : ℕ → Set α,
      (∀ n, MeasurableSet (F n) ∧ μ (F n) < ∞) ∧
      Monotone F ∧ (⋃ n, F n) = univ

def restrictOnSpace_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → Set α → Measure α

noncomputable def restrictOnSpace_value : restrictOnSpace_type.{u} :=
  fun μ E => μ.restrict E

def restrictToSubtype_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → (E : Set α) → Measure E

noncomputable def restrictToSubtype_value : restrictToSubtype_type.{u} :=
  fun μ E => μ.comap (Subtype.val : E → _)

def restrictOnSpace_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E → ∀ A : Set α, MeasurableSet A →
      restrictOnSpace_value μ E A = μ (A ∩ E)

def restrictToSubtype_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E → ∀ B : Set E, MeasurableSet B →
      restrictToSubtype_value μ E B = μ ((Subtype.val : E → α) '' B)

/-- Literal evaluation at a measurable ambient subset of E. -/
def restrictToSubtype_apply_subset : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E → ∀ A : Set α, MeasurableSet A → A ⊆ E →
      restrictToSubtype_value μ E ((Subtype.val : E → α) ⁻¹' A) = μ A

def restriction_mass : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E →
      restrictOnSpace_value μ E univ = μ E ∧
      restrictToSubtype_value μ E univ = μ E

def restriction_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E → IsFiniteMeasure μ →
      IsFiniteMeasure (restrictOnSpace_value μ E) ∧
      IsFiniteMeasure (restrictToSubtype_value μ E)

def restriction_sigmaFinite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E → SigmaFinite μ →
      SigmaFinite (restrictOnSpace_value μ E) ∧
      SigmaFinite (restrictToSubtype_value μ E)

/-- The two restrictions agree under the inclusion of the trace space. -/
def map_restrictToSubtype : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet E →
      (restrictToSubtype_value μ E).map (Subtype.val : E → α) =
        restrictOnSpace_value μ E

end Specs.D11.Ch01.ExhaustionRestriction
