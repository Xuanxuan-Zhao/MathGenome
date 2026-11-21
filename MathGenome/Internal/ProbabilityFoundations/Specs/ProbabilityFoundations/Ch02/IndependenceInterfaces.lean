import Mathlib.Probability.Independence.Basic

/-! Independent specification of Definition 2.1 (paper.tex:493–505).
The ambient space and measure are Mathlib's original objects, without a
completeness assumption. Finsets encode finite distinct indices, including
zero indices. Independence predicates extend to arbitrary sigma-algebras;
the stated application is to F i ≤ mΩ, measurable random elements, and events.
The sigma-algebra inclusion conclusions below verify these domain interfaces.
Pairwise predicates impose only the two-distinct-indices condition.
-/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces

universe u v w

set_option linter.unusedVariables false
set_option linter.checkUnivs false

def MutuallyIndependentType := ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω), Prop

def MutuallyIndependentValue {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω) : Prop :=
  ∀ (s : Finset I) (A : I → Set Ω),
    (∀ i ∈ s, MeasurableSet[F i] (A i)) →
      P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i)

def IndependentRandomElementsType := ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i), Prop

def IndependentRandomElementsValue {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i) : Prop :=
  MutuallyIndependentValue P (fun i => (mS i).comap (X i))

def IndependentEventsType := ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω), Prop

def IndependentEventsValue {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω) : Prop :=
  MutuallyIndependentValue P (fun i => MeasurableSpace.generateFrom {A i})

def PairwiseIndependentType := ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω), Prop

def PairwiseIndependentValue {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω) : Prop :=
  ∀ i j, i ≠ j → ∀ B C : Set Ω,
    MeasurableSet[F i] B → MeasurableSet[F j] C → P (B ∩ C) = P B * P C

def PairwiseIndependentRandomElementsType := ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i), Prop

def PairwiseIndependentRandomElementsValue {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i) : Prop :=
  PairwiseIndependentValue P (fun i => (mS i).comap (X i))

def PairwiseIndependentEventsType := ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω), Prop

def PairwiseIndependentEventsValue {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω) : Prop :=
  PairwiseIndependentValue P (fun i => MeasurableSpace.generateFrom {A i})

def mutuallyIndependent_iff_iIndepType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω),
    MutuallyIndependentValue P F ↔ ProbabilityTheory.iIndep F P

def independentRandomElements_iff_iIndepFunType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i),
    IndependentRandomElementsValue P X ↔ ProbabilityTheory.iIndepFun X P

def independentEvents_iff_iIndepSetType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω),
    IndependentEventsValue P A ↔ ProbabilityTheory.iIndepSet A P

def pairwiseIndependent_iffType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω),
    PairwiseIndependentValue P F ↔
    Pairwise (fun i j => ProbabilityTheory.Indep (F i) (F j) P)

def pairwiseIndependentRandomElements_iffType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i),
    PairwiseIndependentRandomElementsValue P X ↔
    Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) P)

def pairwiseIndependentEvents_iffType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω),
    PairwiseIndependentEventsValue P A ↔
    Pairwise (fun i j => ProbabilityTheory.IndepSet (A i) (A j) P)

def mutuallyIndependent_pairwiseType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω),
    MutuallyIndependentValue P F → PairwiseIndependentValue P F

def randomElements_sigma_leType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {S : I → Type w} [mS : ∀ i, MeasurableSpace (S i)] (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i)),
    ∀ i, (mS i).comap (X i) ≤ mΩ

def events_sigma_leType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)),
    ∀ i, MeasurableSpace.generateFrom {A i} ≤ mΩ

def mutuallyIndependent_emptyType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : I → MeasurableSpace Ω) (h : MutuallyIndependentValue P F),
    P (⋂ i ∈ (∅ : Finset I), (Set.univ : Set Ω)) =
    ∏ i ∈ (∅ : Finset I), P (Set.univ : Set Ω)

def independentEvents_iff_finite_intersectionsType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)),
    IndependentEventsValue P A ↔
    ∀ s : Finset I, P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i)

def pairwiseIndependentEvents_iff_intersectionsType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)),
    PairwiseIndependentEventsValue P A ↔
    ∀ i j, i ≠ j → P (A i ∩ A j) = P (A i) * P (A j)

end Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
