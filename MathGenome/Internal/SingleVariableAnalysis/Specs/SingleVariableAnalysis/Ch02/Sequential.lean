import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-!
Independent specifications for K03.02.sequential, paper.tex:384–392.
The metric theorem includes both real and complex finite-point domains and both
scalar targets, with their canonical metrics. The four scalar specializations
spell out the manuscript's sequence predicates. Natural index n represents
source index n+1. Every test sequence lies in the indicated domain at every
index; finite-point tests avoid the approach point. Sided statements assume
accumulation on the selected side, and infinite-input statements assume the
corresponding directional unboundedness. All output limits here are finite.
-/
namespace Specs.SingleVariableAnalysis.Ch02.Sequential

open scoped Topology
open RelativeLimit OneSided
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
universe u v

def relativePuncturedLimitSequentialIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y),
    domainAccumulationValue E a →
      (relativePuncturedLimitValue f E a L ↔
        ∀ x : ℕ → X, (∀ n, x n ∈ E ∧ x n ≠ a) →
          Filter.Tendsto x Filter.atTop (𝓝 a) →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L))

def rightRelativeLimitSequentialIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    rightAccumulationValue E a →
      (rightRelativeLimitValue f E a L ↔
        ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ a < x n) →
          realSequenceConvergesValue x a →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L))

def leftRelativeLimitSequentialIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    leftAccumulationValue E a →
      (leftRelativeLimitValue f E a L ↔
        ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ x n < a) →
          realSequenceConvergesValue x a →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L))

def limitAtPosInfinitySequentialIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y),
    domainUnboundedAboveValue E →
      (limitAtPosInfinityValue f E L ↔
        ∀ x : ℕ → ℝ, (∀ n, x n ∈ E) → divergesToPosInfinityValue x →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L))

def limitAtNegInfinitySequentialIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y),
    domainUnboundedBelowValue E →
      (limitAtNegInfinityValue f E L ↔
        ∀ x : ℕ → ℝ, (∀ n, x n ∈ E) → divergesToNegInfinityValue x →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 L))

def realRealSequentialIff : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a L : ℝ), domainAccumulationValue E a →
    (relativePuncturedLimitValue f E a L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        realSequenceConvergesValue x a → realSequenceConvergesValue (fun n => f (x n)) L)

def realComplexSequentialIff : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ) (L : ℂ), domainAccumulationValue E a →
    (relativePuncturedLimitValue f E a L ↔
      ∀ x : ℕ → ℝ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        realSequenceConvergesValue x a → complexSequenceConvergesValue (fun n => f (x n)) L)

def complexRealSequentialIff : Prop :=
  ∀ (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ) (L : ℝ), domainAccumulationValue E a →
    (relativePuncturedLimitValue f E a L ↔
      ∀ x : ℕ → ℂ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        complexSequenceConvergesValue x a → realSequenceConvergesValue (fun n => f (x n)) L)

def complexComplexSequentialIff : Prop :=
  ∀ (f : ℂ → ℂ) (E : Set ℂ) (a L : ℂ), domainAccumulationValue E a →
    (relativePuncturedLimitValue f E a L ↔
      ∀ x : ℕ → ℂ, (∀ n, x n ∈ E ∧ x n ≠ a) →
        complexSequenceConvergesValue x a → complexSequenceConvergesValue (fun n => f (x n)) L)

end Specs.SingleVariableAnalysis.Ch02.Sequential
