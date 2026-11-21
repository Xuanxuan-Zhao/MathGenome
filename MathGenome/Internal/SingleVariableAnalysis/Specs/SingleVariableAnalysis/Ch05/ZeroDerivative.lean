import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.MeanInequality
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.LinearRules
import Mathlib.Order.Interval.Set.OrdConnected

/-!
Independent specification of K03.05.zero_derivative (paper.tex:852–860).
An interval is an order-connected real set, with no nonemptiness or openness
assumption. Ambient functions represent functions on that set, as in the
upstream derivative interface. Continuity includes all included endpoints;
derivatives are taken over ℝ only at interior points. In particular a total
`deriv` equal to zero is accompanied by actual differentiability.

The equal-derivative statements require neither derivative to be zero.
Existence of a constant also covers empty and singleton intervals. The last
statement checks the manuscript's specific two-component counterexample.
-/

namespace Specs.SingleVariableAnalysis.Ch05.ZeroDerivative

open Set

def realZeroDerivativeConstant : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → ContinuousOn f I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, deriv f x = 0) →
    ∃ c : ℝ, ∀ x ∈ I, f x = c

def complexZeroDerivativeConstant : Prop :=
  ∀ (f : ℝ → ℂ) (I : Set ℝ), I.OrdConnected → ContinuousOn f I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, deriv f x = 0) →
    ∃ c : ℂ, ∀ x ∈ I, f x = c

def realEqualDerivativesDifferByConstant : Prop :=
  ∀ (f g : ℝ → ℝ) (I : Set ℝ), I.OrdConnected →
    ContinuousOn f I → ContinuousOn g I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, DifferentiableAt ℝ g x) →
    (∀ x ∈ interior I, deriv f x = deriv g x) →
    ∃ c : ℝ, ∀ x ∈ I, f x - g x = c

def complexEqualDerivativesDifferByConstant : Prop :=
  ∀ (f g : ℝ → ℂ) (I : Set ℝ), I.OrdConnected →
    ContinuousOn f I → ContinuousOn g I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, DifferentiableAt ℝ g x) →
    (∀ x ∈ interior I, deriv f x = deriv g x) →
    ∃ c : ℂ, ∀ x ∈ I, f x - g x = c

def disconnectedZeroDerivativeExample : Prop :=
  let I : Set ℝ := Ioo (-2) (-1) ∪ Ioo 1 2
  let f : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  ContinuousOn f I ∧
    (∀ x ∈ I, HasDerivAt f 0 x) ∧
    (∀ x ∈ Ioo (-2 : ℝ) (-1), f x = 0) ∧
    (∀ x ∈ Ioo (1 : ℝ) 2, f x = 1) ∧
    ¬ (∃ c : ℝ, ∀ x ∈ I, f x = c)

end Specs.SingleVariableAnalysis.Ch05.ZeroDerivative
