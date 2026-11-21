import MathGenome.Internal.RealAnalysis.D11.Ch01.SetSystems
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions

/-!
# Measures on a specified sigma-algebra

`SourceMeasure` evaluates only members of the original sigma-algebra. The
construction by `Measure.ofMeasurable` is proved to preserve exactly these
values, and restriction back is inverse to it. Native outer values on other
sets supply no additional measurability claims.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch01.MeasureDefinitions

abbrev positiveMeasure (α : Type u) [MeasurableSpace α] := Measure α
abbrev sourceMeasure (α : Type u) [MeasurableSpace α] := SourceMeasure α
abbrev finitelyAdditiveMeasure (α : Type u) (A : Set (Set α)) (hA : IsSetAlgebra A) :=
  AlgebraMeasure A hA

/-- Restrict native evaluation to the source's specified domain. -/
noncomputable def sourceOfMeasure {α : Type u} [MeasurableSpace α]
    (μ : Measure α) : SourceMeasure α where
  value s := μ s.1
  empty := measure_empty
  iUnion E hd := measure_iUnion hd fun n => (E n).2

/-- Construct the canonical native measure from countably additive source data. -/
noncomputable def measureOfSource {α : Type u} [MeasurableSpace α]
    (p : SourceMeasure α) : Measure α :=
  Measure.ofMeasurable (fun s hs => p.value ⟨s, hs⟩) p.empty
    (fun _ hE hd => p.iUnion (fun n => ⟨_, hE n⟩) hd)

theorem measureOfSource_apply {α : Type u} [MeasurableSpace α]
    (p : SourceMeasure α) (s : Set α) (hs : MeasurableSet s) :
    measureOfSource p s = p.value ⟨s, hs⟩ :=
  Measure.ofMeasurable_apply s hs

theorem measure_correspondence {α : Type u} [MeasurableSpace α] (p : SourceMeasure α) :
    ∃! μ : Measure α, ∀ (s : Set α) (hs : MeasurableSet s), μ s = p.value ⟨s, hs⟩ := by
  refine ⟨measureOfSource p, measureOfSource_apply p, ?_⟩
  intro μ hμ
  exact Measure.ext fun s hs => (hμ s hs).trans (measureOfSource_apply p s hs).symm

theorem measure_roundtrip {α : Type u} [MeasurableSpace α] (μ : Measure α) :
    measureOfSource (sourceOfMeasure μ) = μ := by
  exact Measure.ext fun s hs => measureOfSource_apply _ s hs

@[ext]
theorem SourceMeasure.ext {α : Type u} [MeasurableSpace α] {p q : SourceMeasure α}
    (h : ∀ s, p.value s = q.value s) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

theorem source_roundtrip {α : Type u} [MeasurableSpace α] (p : SourceMeasure α) :
    sourceOfMeasure (measureOfSource p) = p := by
  apply SourceMeasure.ext
  intro s
  exact measureOfSource_apply p s.1 s.2

theorem countable_additivity {α : Type u} {ι : Type v} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    μ (⋃ i, E i) = ∑' i, μ (E i) :=
  measure_iUnion hd hE

theorem empty_measure {α : Type u} [MeasurableSpace α] (μ : Measure α) : μ ∅ = 0 :=
  measure_empty

theorem finite_additivity {α : Type u} {ι : Type v} {A : Set (Set α)}
    (hA : IsSetAlgebra A) (p : AlgebraMeasure A hA) (I : Finset ι)
    (E : ι → {s : Set α // s ∈ A})
    (hd : (↑I : Set ι).PairwiseDisjoint (fun i => (E i).1)) :
    p.value ⟨⋃ i ∈ I, (E i).1, hA.biUnion_mem I (fun i _ => (E i).2)⟩ =
      ∑ i ∈ I, p.value (E i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using p.empty
  | @insert i I hi ih =>
    have hdI : (↑I : Set ι).PairwiseDisjoint (fun j => (E j).1) :=
      fun j hj k hk hjk => hd (by simp [hj]) (by simp [hk]) hjk
    have hdi : Disjoint (E i).1 (⋃ j ∈ I, (E j).1) := by
      simp only [disjoint_iUnion_right]
      intro j hj
      exact hd (by simp) (by simp [hj]) (by
        intro heq
        subst j
        exact hi hj)
    have hu : (⋃ j ∈ insert i I, (E j).1) = (E i).1 ∪ ⋃ j ∈ I, (E j).1 := by
      simp
    calc
      p.value ⟨⋃ j ∈ insert i I, (E j).1, _⟩ =
          p.value ⟨(E i).1 ∪ ⋃ j ∈ I, (E j).1,
            hA.union_mem (E i).2 (hA.biUnion_mem I fun j _ => (E j).2)⟩ := by
        congr 1
        exact Subtype.ext hu
      _ = p.value (E i) + p.value ⟨⋃ j ∈ I, (E j).1, _⟩ :=
        p.union (E i) ⟨⋃ j ∈ I, (E j).1, hA.biUnion_mem I fun j _ => (E j).2⟩ hdi
      _ = ∑ j ∈ insert i I, p.value (E j) := by rw [ih hdI, Finset.sum_insert hi]

abbrev isFinite {α : Type u} [MeasurableSpace α] (μ : Measure α) : Prop :=
  IsFiniteMeasure μ
abbrev isProbability {α : Type u} [MeasurableSpace α] (μ : Measure α) : Prop :=
  IsProbabilityMeasure μ
abbrev isSigmaFinite {α : Type u} [MeasurableSpace α] (μ : Measure α) : Prop :=
  SigmaFinite μ

/-- The set is measurable, and its cover consists of measurable subsets of itself. -/
def isSigmaFiniteSet {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α) : Prop :=
  MeasurableSet s ∧ ∃ E : ℕ → Set α,
    (∀ n, MeasurableSet (E n) ∧ E n ⊆ s ∧ μ (E n) < ∞) ∧ (⋃ n, E n) = s

theorem finite_iff {α : Type u} [MeasurableSpace α] (μ : Measure α) :
    isFinite μ ↔ μ univ < ∞ := isFiniteMeasure_iff μ

theorem probability_iff {α : Type u} [MeasurableSpace α] (μ : Measure α) :
    isProbability μ ↔ μ univ = 1 := isProbabilityMeasure_iff

theorem sigmaFinite_iff {α : Type u} [MeasurableSpace α] (μ : Measure α) :
    isSigmaFinite μ ↔ ∃ E : ℕ → Set α,
      (∀ n, MeasurableSet (E n) ∧ μ (E n) < ∞) ∧ (⋃ n, E n) = univ := by
  constructor
  · intro h
    let : SigmaFinite μ := h
    exact ⟨spanningSets μ, fun n => ⟨measurableSet_spanningSets μ n,
      measure_spanningSets_lt_top μ n⟩, iUnion_spanningSets μ⟩
  · rintro ⟨E, hE, hU⟩
    exact ⟨⟨⟨E, fun _ => trivial, fun n => (hE n).2, hU⟩⟩⟩

theorem sigmaFiniteSet_iff {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    isSigmaFiniteSet μ s ↔ MeasurableSet s ∧ SigmaFinite (μ.restrict s) := by
  constructor
  · rintro ⟨hs, E, hE, hU⟩
    refine ⟨hs, (sigmaFinite_iff (μ.restrict s)).mpr ?_⟩
    refine ⟨fun n => E n ∪ sᶜ, fun n => ⟨(hE n).1.union hs.compl, ?_⟩, ?_⟩
    · rw [Measure.restrict_apply ((hE n).1.union hs.compl)]
      simpa [union_inter_distrib_right, inter_eq_left.mpr (hE n).2.1] using (hE n).2.2
    · rw [← iUnion_union, hU]
      simp
  · rintro ⟨hs, h⟩
    obtain ⟨E, hE, hU⟩ := (sigmaFinite_iff (μ.restrict s)).mp h
    refine ⟨hs, fun n => E n ∩ s, fun n => ⟨(hE n).1.inter hs, inter_subset_right, ?_⟩, ?_⟩
    · simpa only [Measure.restrict_apply (hE n).1] using (hE n).2
    · rw [← iUnion_inter, hU, univ_inter]

/-- Null in the source sense includes membership in the given sigma-algebra. -/
def measurableNull {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α) : Prop :=
  MeasurableSet s ∧ μ s = 0

/-- An arbitrary subset of a measurable null set. -/
def negligible {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α) : Prop :=
  ∃ N, s ⊆ N ∧ measurableNull μ N

def isComplete {α : Type u} [MeasurableSpace α] (μ : Measure α) : Prop :=
  ∀ s, negligible μ s → MeasurableSet s

theorem negligible_iff {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    negligible μ s ↔ μ s = 0 := by
  constructor
  · rintro ⟨N, hsN, _, hN⟩
    exact measure_mono_null hsN hN
  · intro hs
    exact exists_measurable_superset_of_null hs

theorem complete_iff {α : Type u} [MeasurableSpace α] (μ : Measure α) :
    isComplete μ ↔ μ.IsComplete := by
  rw [Measure.isComplete_iff]
  constructor
  · intro h s hs
    exact h s ((negligible_iff μ s).mpr hs)
  · intro h s hs
    exact h s ((negligible_iff μ s).mp hs)

theorem complete_negligible_null {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (hμ : isComplete μ) (s : Set α) (hs : negligible μ s) : measurableNull μ s :=
  ⟨hμ s hs, (negligible_iff μ s).mp hs⟩

end D11.Ch01.MeasureDefinitions
