import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.ContinuousOn

/-! Independent statements of K03.09.continuous_primitive, paper.tex:2415–2430.
`OrdConnected` expresses the interval convention, including the empty set,
singletons, unbounded intervals, and intervals with either endpoint excluded.
Functions on the interval are represented by ambient functions; all assertions
are restricted to the stated domain. Continuity on I includes every included
finite endpoint, while derivatives are required only in `interior I`.

For every chosen base point, the primitive is the proper oriented Darboux
integral of f. Integrability is supplied in the conclusion. The existence
statements have no nonemptiness assumption, so also cover the empty interval.
No value or finite limit at any excluded endpoint is asserted.
-/
namespace Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive
open Specs.SingleVariableAnalysis.Ch08

def realConstruction : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → ContinuousOn f I →
    ∀ x₀ ∈ I, ∃ F : ℝ → ℝ,
      (∀ x ∈ I, ∃ h : Oriented.realIntegrableValue f x₀ x,
        F x = Oriented.realIntegralValue f h) ∧
      F x₀ = 0 ∧ ContinuousOn F I ∧
      ∀ x ∈ interior I, HasDerivAt F (f x) x

def complexConstruction : Prop :=
  ∀ (f : ℝ → ℂ) (I : Set ℝ), I.OrdConnected → ContinuousOn f I →
    ∀ x₀ ∈ I, ∃ F : ℝ → ℂ,
      (∀ x ∈ I, ∃ h : Oriented.complexIntegrableValue f x₀ x,
        F x = Oriented.complexIntegralValue f h) ∧
      F x₀ = 0 ∧ ContinuousOn F I ∧
      ∀ x ∈ interior I, HasDerivAt F (f x) x

def realExistence : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → ContinuousOn f I →
    ∃ F : ℝ → ℝ, ContinuousOn F I ∧
      ∀ x ∈ interior I, HasDerivAt F (f x) x

def complexExistence : Prop :=
  ∀ (f : ℝ → ℂ) (I : Set ℝ), I.OrdConnected → ContinuousOn f I →
    ∃ F : ℝ → ℂ, ContinuousOn F I ∧
      ∀ x ∈ interior I, HasDerivAt F (f x) x

end Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive
