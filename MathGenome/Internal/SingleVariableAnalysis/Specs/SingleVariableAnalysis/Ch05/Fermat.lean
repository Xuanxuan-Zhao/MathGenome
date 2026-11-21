import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative
import Mathlib.Topology.Order.LocalExtr

/-!
Independent specifications for K03.05.fermat, paper.tex:799–806.
The functions are real valued and all derivative values are finite real numbers.
An ambient extension represents a function on a domain; at an interior point
its relative derivative is the ordinary two-sided derivative. No interval
assumption is needed for this local result, so arbitrary real domains are allowed.
Both counterexamples in the source are part of the obligation.
-/

namespace Specs.SingleVariableAnalysis.Ch05.Fermat

open Set

def fermatHasDerivAt : Prop :=
  ∀ (f : ℝ → ℝ) (a L : ℝ), IsLocalExtr f a → HasDerivAt f L a → L = 0

def fermatWithin : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ), a ∈ interior I →
    IsLocalExtrOn f I a →
    Ch04.Derivative.hasRealIncrementDerivativeWithinValue f L I a → L = 0

def fermatDeriv : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    IsLocalExtrOn f I a → DifferentiableAt ℝ f a → deriv f a = 0

/-- On [0,1], x has an endpoint minimum and right derivative 1, which is nonzero. -/
def endpointMinimumExample : Prop :=
  (0 : ℝ) ∈ Icc 0 1 ∧
    (0 : ℝ) ∉ interior (Icc (0 : ℝ) 1) ∧
    IsMinOn (fun x : ℝ => x) (Icc 0 1) 0 ∧
    IsLocalMinOn (fun x : ℝ => x) (Icc 0 1) 0 ∧
    HasDerivWithinAt (fun x : ℝ => x) 1 (Ici 0) 0 ∧
    Ch04.Derivative.hasRealIncrementDerivativeWithinValue
      (fun x : ℝ => x) 1 (Icc 0 1) 0 ∧
    (1 : ℝ) ≠ 0

/-- The interior minimum of |x| at 0 has no finite two-sided derivative. -/
def absMinimumExample : Prop :=
  (0 : ℝ) ∈ interior (univ : Set ℝ) ∧
    IsMinOn (abs : ℝ → ℝ) univ 0 ∧
    IsLocalMin (abs : ℝ → ℝ) 0 ∧
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
    ¬ ∃ L : ℝ, Ch04.Derivative.hasRealIncrementDerivativeValue (abs : ℝ → ℝ) L 0

end Specs.SingleVariableAnalysis.Ch05.Fermat
