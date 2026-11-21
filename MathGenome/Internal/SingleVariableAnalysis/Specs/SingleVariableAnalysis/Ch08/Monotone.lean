import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn

/-! Independent statements for K03.08.monotone, paper.tex:2028–2048.
Monotonicity is relative to the whole closed interval. Step functions are
constant on open partition cells, with no restriction on their node values.
Piecewise continuity requires finite scalar one-sided limits separately on
each side of each cell; these limits need not agree with assigned node values.
The conclusions use the shared bounded Darboux predicates, including [a,a]. -/
namespace Specs.SingleVariableAnalysis.Ch08.Monotone
open _root_.SingleVariableAnalysis.Riemann Filter
open scoped Topology

def realMonotoneIntegrable : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b →
    (MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b)) →
    Integral.realIntegrableValue f a b

def realStepIntegrable : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (P : PartitionData a b),
    (∀ i : Fin P.n, ∃ c : ℝ,
      ∀ x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ), f x = c) →
    Integral.realIntegrableValue f a b

def complexStepIntegrable : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ} (P : PartitionData a b),
    (∀ i : Fin P.n, ∃ c : ℂ,
      ∀ x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ), f x = c) →
    Integral.complexIntegrableValue f a b

def realPiecewiseContinuousIntegrable : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (P : PartitionData a b),
    (∀ i : Fin P.n,
      ContinuousOn f (Set.Ioo (P.point i.castSucc) (P.point i.succ)) ∧
      ∃ L R : ℝ, Tendsto f (𝓝[>] (P.point i.castSucc)) (𝓝 L) ∧
        Tendsto f (𝓝[<] (P.point i.succ)) (𝓝 R)) →
    Integral.realIntegrableValue f a b

def complexPiecewiseContinuousIntegrable : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ} (P : PartitionData a b),
    (∀ i : Fin P.n,
      ContinuousOn f (Set.Ioo (P.point i.castSucc) (P.point i.succ)) ∧
      ∃ L R : ℂ, Tendsto f (𝓝[>] (P.point i.castSucc)) (𝓝 L) ∧
        Tendsto f (𝓝[<] (P.point i.succ)) (𝓝 R)) →
    Integral.complexIntegrableValue f a b

end Specs.SingleVariableAnalysis.Ch08.Monotone
