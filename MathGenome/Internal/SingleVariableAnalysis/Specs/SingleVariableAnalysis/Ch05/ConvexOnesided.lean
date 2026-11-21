import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.OneSided

/-!
Independent specification for K03.05.convex_onesided (paper.tex:941–957).
Continuity is the preceding ConvexLocalLipschitz obligation. Here a real-valued
function is finite, an interval is order connected, and openness ensures that
both real increment approaches are available at every member. No continuity,
boundedness or differentiability is assumed. The derivative predicates below
are the shared predicates, including their side availability and accumulation
requirements. The supporting inequality is tested on the entire interval.
-/

namespace Specs.SingleVariableAnalysis.Ch05.ConvexOnesided

open Specs.SingleVariableAnalysis.Ch05.Convexity
open Specs.SingleVariableAnalysis.Ch04.OneSided

/-- Finite left and right derivatives exist and are ordered. -/
def finiteOneSidedDerivatives : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected →
    ∀ (f : ℝ → ℝ), convexFunctionOnValue I f → ∀ x ∈ I,
      ∃ L R : ℝ, hasLeftRealIncrementDerivativeWithinValue f L I x ∧
        hasRightRealIncrementDerivativeWithinValue f R I x ∧ L ≤ R

/-- Exactly the closed interval between the one-sided derivatives consists of
supporting slopes, including both endpoint slopes. -/
def supportingSlopeIff : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected →
    ∀ (f : ℝ → ℝ), convexFunctionOnValue I f → ∀ x ∈ I,
      ∀ L R : ℝ, hasLeftRealIncrementDerivativeWithinValue f L I x →
        hasRightRealIncrementDerivativeWithinValue f R I x → ∀ p : ℝ,
          (∀ y ∈ I, f x + p * (y - x) ≤ f y) ↔ L ≤ p ∧ p ≤ R

end Specs.SingleVariableAnalysis.Ch05.ConvexOnesided
