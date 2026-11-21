import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.OuterCover
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.OuterMeasure

/-!
Independent specification of paper.tex:535–589. The splitting test quantifies
all subsets, with no ambient measurable space. The resulting measurable space
is exactly the native Carathéodory space. Its measure is only required to agree
with the original outer measure on the splitting-measurable sets. Completeness
is stated both natively and in the shared source sense (subsets of measurable
null sets). No finiteness or nonemptiness assumptions are made.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch02.Caratheodory

def isMeasurable_type : Type (u + 1) :=
  {α : Type u} → OuterMeasure α → Set α → Prop

def isMeasurable_value : isMeasurable_type.{u} :=
  fun m A => ∀ E, m E = m (E ∩ A) + m (E \ A)

def measurableSpace_type : Type (u + 1) :=
  {α : Type u} → OuterMeasure α → MeasurableSpace α

def measurableSpace_value : measurableSpace_type.{u} :=
  fun m => m.caratheodory

def measure_type : Type (u + 1) :=
  {α : Type u} → (m : OuterMeasure α) → @Measure α (measurableSpace_value m)

noncomputable def measure_value : measure_type.{u} :=
  fun m => @OuterMeasure.toMeasure _ (measurableSpace_value m) m le_rfl

def splitting_iff : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (A : Set α),
    isMeasurable_value m A ↔ ∀ E : Set α, m E = m (E ∩ A) + m (E \ A)

def splitting_le : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (A E : Set α),
    m E ≤ m (E ∩ A) + m (E \ A)

def isMeasurable_iff_le : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (A : Set α),
    isMeasurable_value m A ↔ ∀ E : Set α, m (E ∩ A) + m (E \ A) ≤ m E

def isMeasurable_iff_finite : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (A : Set α),
    isMeasurable_value m A ↔
      ∀ E : Set α, m E < ∞ → m (E ∩ A) + m (E \ A) ≤ m E

def measurableSet_iff : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (A : Set α),
    MeasurableSet[measurableSpace_value m] A ↔ isMeasurable_value m A

def sigmaAlgebra : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α),
    IsSetAlgebra {A : Set α | isMeasurable_value m A} ∧
      ∀ E : ℕ → Set α, (∀ n, isMeasurable_value m (E n)) →
        isMeasurable_value m (⋃ n, E n)

def measure_apply : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (A : Set α),
    isMeasurable_value m A → measure_value m A = m A

def countable_additivity : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (E : ℕ → Set α),
    (∀ n, isMeasurable_value m (E n)) →
      Pairwise (fun i j => Disjoint (E i) (E j)) →
        m (⋃ n, E n) = ∑' n, m (E n)

def null_subset : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α) (N Z : Set α),
    m N = 0 → Z ⊆ N → isMeasurable_value m Z ∧ m Z = 0

def measure_isComplete : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α),
    @Measure.IsComplete α (measurableSpace_value m) (measure_value m)

def complete : Prop :=
  ∀ {α : Type u} (m : OuterMeasure α),
    @_root_.Specs.D11.Ch01.MeasureDefinitions.isComplete_value α
      (measurableSpace_value m) (measure_value m)

end Specs.D11.Ch02.Caratheodory
