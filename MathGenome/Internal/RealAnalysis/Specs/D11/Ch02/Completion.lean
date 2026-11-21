import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
Independent interfaces for paper.tex:655–698, completion of an arbitrary measure.
The original sigma-algebra `m` and completed sigma-algebra are explicit. Native
outer values on nonmeasurable sets do not assert original measurability.
No finite-mass, sigma-finite, complete, or nonempty-space premise is imposed.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch02.Completion

/-- The literal sandwich condition in the source. -/
def Sandwiched {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : Set α) : Prop :=
  ∃ A B : Set α, MeasurableSet A ∧ MeasurableSet B ∧
    A ⊆ E ∧ E ⊆ B ∧ μ (B \ A) = 0

/-- Original measurable sets together with all subsets of measurable null sets. -/
def generators {α : Type u} [MeasurableSpace α] (μ : Measure α) : Set (Set α) :=
  {E | MeasurableSet E ∨ Specs.D11.Ch01.MeasureDefinitions.negligible_value μ E}

end D11.Ch02.Completion

namespace Specs.D11.Ch02.Completion

open _root_.D11.Ch02.Completion

def completedSpace_type :=
  ∀ {α : Type u} [m : MeasurableSpace α], @Measure α m → MeasurableSpace α

def completedSpace_value : completedSpace_type.{u} :=
  fun {_} {m} μ => eventuallyMeasurableSpace m (ae μ)

def completedMeasure_type :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : @Measure α m),
    @Measure α (completedSpace_value μ)

noncomputable def completedMeasure_value : completedMeasure_type.{u} :=
  fun μ => μ.completion

def completed_measurable_iff : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α) (E : Set α),
    MeasurableSet[completedSpace_value μ] E ↔ Sandwiched μ E

/-- The value formula for *every* choice of sandwich, also with infinite masses. -/
def sandwich_value : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α) (E A B : Set α),
    MeasurableSet[m] A → MeasurableSet[m] B →
    A ⊆ E → E ⊆ B → μ (B \ A) = 0 →
      completedMeasure_value μ E = μ A ∧ μ A = μ B

/-- Explicit independence of both sandwich witnesses. -/
def well_defined : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α) (E A B C D : Set α),
    MeasurableSet[m] A → MeasurableSet[m] B → A ⊆ E → E ⊆ B → μ (B \ A) = 0 →
    MeasurableSet[m] C → MeasurableSet[m] D → C ⊆ E → E ⊆ D → μ (D \ C) = 0 →
      μ A = μ C ∧ μ B = μ D

def extends_original : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α),
    m ≤ completedSpace_value μ ∧
      ∀ E : Set α, MeasurableSet[m] E → completedMeasure_value μ E = μ E

def countable_additivity : Prop :=
  ∀ {α : Type u} {ι : Type v} [m : MeasurableSpace α] [Countable ι]
    (μ : Measure α) (E : ι → Set α),
    (∀ i, MeasurableSet[completedSpace_value μ] (E i)) →
    Pairwise (fun i j => Disjoint (E i) (E j)) →
      completedMeasure_value μ (⋃ i, E i) = ∑' i, completedMeasure_value μ (E i)

def completed_empty : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α),
    completedMeasure_value μ ∅ = 0

def completed_complete : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α),
    @Measure.IsComplete α (completedSpace_value μ) (completedMeasure_value μ)

/-- Completeness in the source formulation: every subset of a measurable null
set is measurable and null in the completed structure. -/
def completed_subset_null : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α) (E N : Set α),
    E ⊆ N → MeasurableSet[completedSpace_value μ] N → completedMeasure_value μ N = 0 →
      MeasurableSet[completedSpace_value μ] E ∧ completedMeasure_value μ E = 0

def generated_characterization : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α),
    completedSpace_value μ = MeasurableSpace.generateFrom (generators μ)

/-- Every complete measure on any larger sigma-algebra agreeing on the original
measurable sets contains, and agrees on, the entire completion. -/
def minimality : Prop :=
  ∀ {α : Type u} [m : MeasurableSpace α] (μ : @Measure α m)
    (n : MeasurableSpace α) (ν : @Measure α n),
    m ≤ n → @Measure.IsComplete α n ν →
    (∀ E : Set α, MeasurableSet[m] E → ν E = μ E) →
      completedSpace_value (m := m) μ ≤ n ∧
        ∀ E : Set α, MeasurableSet[completedSpace_value (m := m) μ] E →
          ν E = completedMeasure_value (m := m) μ E

end Specs.D11.Ch02.Completion
