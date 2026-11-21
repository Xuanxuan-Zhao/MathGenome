import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Independent interfaces for the measure definitions in Chapter 1

The source measure has domain exactly the subtype of measurable sets. The native
`Measure` is used downstream only after the stated correspondence is proved.
In particular its value on an arbitrary set does not declare that set measurable.
`MeasurableNull` and `Negligible` below deliberately have different domains.
No nonemptiness, finiteness, or sigma-finiteness assumption is implicit.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch01.MeasureDefinitions

/-- The source's domain `Σ`, rather than the whole power set. -/
abbrev MeasurableDomain (α : Type u) [MeasurableSpace α] :=
  {s : Set α // MeasurableSet s}

/-- A positive measure in the literal source representation `Σ → [0,∞]`. -/
structure SourceMeasure (α : Type u) [MeasurableSpace α] where
  value : MeasurableDomain α → ℝ≥0∞
  empty : value ⟨∅, MeasurableSet.empty⟩ = 0
  iUnion (E : ℕ → MeasurableDomain α)
      (hd : Pairwise fun i j => Disjoint (E i).1 (E j).1) :
    value ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩ =
      ∑' n, value (E n)

/-- Finite additivity on an algebra, with evaluation restricted to that algebra.
The binary law and empty-set law are shown to give every finite disjoint-family
law in the implementation. Infinite masses are allowed. -/
structure AlgebraMeasure {α : Type u} (A : Set (Set α)) (hA : IsSetAlgebra A) where
  value : {s : Set α // s ∈ A} → ℝ≥0∞
  empty : value ⟨∅, hA.empty_mem⟩ = 0
  union (s t : {s : Set α // s ∈ A}) (hd : Disjoint s.1 t.1) :
    value ⟨s.1 ∪ t.1, hA.union_mem s.2 t.2⟩ = value s + value t

end D11.Ch01.MeasureDefinitions

namespace Specs.D11.Ch01.MeasureDefinitions

open _root_.D11.Ch01.MeasureDefinitions

-- Expected values fix the shared objects without importing any implementation.
def positiveMeasure_type := ∀ (α : Type u), MeasurableSpace α → Type u

def positiveMeasure_value : positiveMeasure_type.{u} := fun α _ => Measure α

def sourceMeasure_type := ∀ (α : Type u), MeasurableSpace α → Type u

def sourceMeasure_value : sourceMeasure_type.{u} := fun α _ => SourceMeasure α

def finitelyAdditiveMeasure_type :=
  ∀ (α : Type u) (A : Set (Set α)), IsSetAlgebra A → Type u

def finitelyAdditiveMeasure_value : finitelyAdditiveMeasure_type.{u} :=
  fun _ A hA => AlgebraMeasure A hA

def sourceOfMeasure_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → SourceMeasure α

noncomputable def sourceOfMeasure_value : sourceOfMeasure_type.{u} := fun μ =>
  { value := fun s => μ s.1
    empty := measure_empty
    iUnion := fun E hd => measure_iUnion hd fun n => (E n).2 }

def measureOfSource_type :=
  ∀ {α : Type u} [MeasurableSpace α], SourceMeasure α → Measure α

noncomputable def measureOfSource_value : measureOfSource_type.{u} := fun p =>
  Measure.ofMeasurable (fun s hs => p.value ⟨s, hs⟩) p.empty
    (fun _ hE hd => p.iUnion (fun n => ⟨_, hE n⟩) hd)

def measureOfSource_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (p : SourceMeasure α) (s : Set α)
    (hs : MeasurableSet s), measureOfSource_value p s = p.value ⟨s, hs⟩

def measure_correspondence : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (p : SourceMeasure α),
    ∃! μ : Measure α, ∀ (s : Set α) (hs : MeasurableSet s), μ s = p.value ⟨s, hs⟩

def measure_roundtrip : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    measureOfSource_value (sourceOfMeasure_value μ) = μ

def source_roundtrip : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (p : SourceMeasure α),
    sourceOfMeasure_value (measureOfSource_value p) = p

def countable_additivity : Prop :=
  ∀ {α : Type u} {ι : Type v} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (E : ι → Set α),
    (∀ i, MeasurableSet (E i)) → Pairwise (fun i j => Disjoint (E i) (E j)) →
      μ (⋃ i, E i) = ∑' i, μ (E i)

def empty_measure : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α), μ ∅ = 0

def finite_additivity : Prop :=
  ∀ {α : Type u} {ι : Type v} {A : Set (Set α)} (hA : IsSetAlgebra A)
    (p : AlgebraMeasure A hA) (I : Finset ι) (E : ι → {s : Set α // s ∈ A}),
    (↑I : Set ι).PairwiseDisjoint (fun i => (E i).1) →
    p.value ⟨⋃ i ∈ I, (E i).1, hA.biUnion_mem I (fun i _ => (E i).2)⟩ =
      ∑ i ∈ I, p.value (E i)

def isFinite_type := ∀ {α : Type u} [MeasurableSpace α], Measure α → Prop

def isFinite_value : isFinite_type.{u} := fun μ => IsFiniteMeasure μ

def isProbability_type := ∀ {α : Type u} [MeasurableSpace α], Measure α → Prop

def isProbability_value : isProbability_type.{u} := fun μ => IsProbabilityMeasure μ

def isSigmaFinite_type := ∀ {α : Type u} [MeasurableSpace α], Measure α → Prop

def isSigmaFinite_value : isSigmaFinite_type.{u} := fun μ => SigmaFinite μ

def isSigmaFiniteSet_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → Set α → Prop

def isSigmaFiniteSet_value : isSigmaFiniteSet_type.{u} := fun μ s =>
  MeasurableSet s ∧ ∃ E : ℕ → Set _,
    (∀ n, MeasurableSet (E n) ∧ E n ⊆ s ∧ μ (E n) < ∞) ∧ (⋃ n, E n) = s

def finite_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    isFinite_value μ ↔ μ univ < ∞

def probability_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    isProbability_value μ ↔ μ univ = 1

def sigmaFinite_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    isSigmaFinite_value μ ↔ ∃ E : ℕ → Set α,
      (∀ n, MeasurableSet (E n) ∧ μ (E n) < ∞) ∧ (⋃ n, E n) = univ

def sigmaFiniteSet_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α),
    isSigmaFiniteSet_value μ s ↔ MeasurableSet s ∧ SigmaFinite (μ.restrict s)

def measurableNull_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → Set α → Prop

def measurableNull_value : measurableNull_type.{u} :=
  fun μ s => MeasurableSet s ∧ μ s = 0

def negligible_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → Set α → Prop

def negligible_value : negligible_type.{u} :=
  fun μ s => ∃ N, s ⊆ N ∧ measurableNull_value μ N

def isComplete_type := ∀ {α : Type u} [MeasurableSpace α], Measure α → Prop

def isComplete_value : isComplete_type.{u} :=
  fun μ => ∀ s, negligible_value μ s → MeasurableSet s

def negligible_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α),
    negligible_value μ s ↔ μ s = 0

def complete_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α),
    isComplete_value μ ↔ μ.IsComplete

def complete_negligible_null : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α), isComplete_value μ →
    ∀ s, negligible_value μ s → measurableNull_value μ s

end Specs.D11.Ch01.MeasureDefinitions
