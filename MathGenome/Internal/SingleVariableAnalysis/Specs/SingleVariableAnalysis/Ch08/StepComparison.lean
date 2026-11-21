import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! Finite step data on open cells, with independently chosen real node values.
The integral is a finite weighted sum, not a Darboux bound by definition.
Source: paper.tex:1941–1953. -/
namespace SingleVariableAnalysis.Riemann.Step
open scoped BigOperators

structure StepData (a b : ℝ) where
  partition : PartitionData a b
  constant : Fin partition.n → ℝ
  node : Fin (partition.n + 1) → ℝ

noncomputable def value {a b : ℝ} (s : StepData a b) (x : ℝ) : ℝ :=
  (∑ i : Fin s.partition.n,
    if x ∈ Set.Ioo (s.partition.point i.castSucc) (s.partition.point i.succ)
      then s.constant i else 0) +
  ∑ i : Fin (s.partition.n + 1), if x = s.partition.point i then s.node i else 0

noncomputable def weightedIntegral {a b : ℝ} (s : StepData a b) : ℝ :=
  ∑ i : Fin s.partition.n,
    s.constant i * Specs.SingleVariableAnalysis.Ch08.Partitions.lengthValue s.partition i

noncomputable def minorantIntegrals (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {r | ∃ s : StepData a b,
    (∀ x ∈ Set.Icc a b, value s x ≤ f x) ∧ weightedIntegral s = r}

noncomputable def majorantIntegrals (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {r | ∃ s : StepData a b,
    (∀ x ∈ Set.Icc a b, f x ≤ value s x) ∧ weightedIntegral s = r}

end SingleVariableAnalysis.Riemann.Step

namespace Specs.SingleVariableAnalysis.Ch08.StepComparison
open _root_.SingleVariableAnalysis.Riemann
open _root_.SingleVariableAnalysis.Riemann.Step
open DarbouxSums Integral
open scoped BigOperators

def openCellValues : Prop := ∀ {a b : ℝ} (s : StepData a b)
  (i : Fin s.partition.n) (x : ℝ),
  x ∈ Set.Ioo (s.partition.point i.castSucc) (s.partition.point i.succ) →
    value s x = s.constant i

def nodeValues : Prop := ∀ {a b : ℝ} (s : StepData a b)
  (i : Fin (s.partition.n + 1)), value s (s.partition.point i) = s.node i

/-- The analytic comparison includes arbitrary values at every node. -/
def comparison : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hf : boundedOnIntervalValue f a b),
  lowerIntegralValue f hab hf = sSup (minorantIntegrals f a b) ∧
  upperIntegralValue f hab hf = sInf (majorantIntegrals f a b)

def stepBounds : Prop := ∀ {a b : ℝ} (s : StepData a b) (hab : a ≤ b),
  ∃ hf : boundedOnIntervalValue (value s) a b,
    lowerIntegralValue (value s) hab hf = weightedIntegral s ∧
    upperIntegralValue (value s) hab hf = weightedIntegral s

def stepIntegrable : Prop := ∀ {a b : ℝ} (s : StepData a b) (_hab : a ≤ b),
  ∃ h : realIntegrableValue (value s) a b,
    realIntegralValue (value s) h = weightedIntegral s

def stepFamiliesFinite : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (_hab : a ≤ b)
  (_hf : boundedOnIntervalValue f a b),
  (minorantIntegrals f a b).Nonempty ∧ (majorantIntegrals f a b).Nonempty ∧
  BddAbove (minorantIntegrals f a b) ∧ BddBelow (majorantIntegrals f a b)

/-- A quantitative short-neighborhood statement: sum incident cell lengths,
counting each incidence separately, which dominates the union's length. -/
def shortNodeNeighborhoods : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (ε : ℝ), 0 < ε → ∃ Q : PartitionData a b,
  Partitions.refinesValue Q P ∧
  (∑ k : Fin (P.n + 1), ∑ j : Fin Q.n,
    ((if Q.point j.castSucc = P.point k then 1 else 0) +
     (if Q.point j.succ = P.point k then 1 else 0)) *
       Partitions.lengthValue Q j) < ε

end Specs.SingleVariableAnalysis.Ch08.StepComparison
