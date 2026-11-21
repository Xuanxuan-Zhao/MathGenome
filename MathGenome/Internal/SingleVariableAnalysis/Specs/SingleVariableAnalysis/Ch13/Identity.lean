import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Analyticity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.IntervalImages

/-!
K03.13.identity, paper.tex:1442–1453.

The interval may be bounded or unbounded. Analyticity is the upstream local
ordinary power-series predicate, with real domain for both scalar codomains.
Agreement is pointwise on the interval; no conclusion is imposed outside it.
An accumulation point lies in the open interval and is approached by distinct
points of the agreement set. It need not itself belong to that set.
The two alternatives in the source are specified separately for each codomain.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Identity
open Analyticity
open Specs.SingleVariableAnalysis.Ch03.IntervalImages

def realIdentityOfAccumulation : Prop :=
  ∀ (f g : ℝ → ℝ) (I : Set ℝ), IsOpen I → realIntervalValue I →
    RealAnalyticOnValue f I → RealAnalyticOnValue g I →
    ∀ E : Set ℝ, E ⊆ I → Set.EqOn f g E →
      (∃ c ∈ I, ∀ ε : ℝ, 0 < ε →
        ∃ x ∈ E, 0 < |x-c| ∧ |x-c| < ε) →
      Set.EqOn f g I

def complexRealIdentityOfAccumulation : Prop :=
  ∀ (f g : ℝ → ℂ) (I : Set ℝ), IsOpen I → realIntervalValue I →
    ComplexRealAnalyticOnValue f I → ComplexRealAnalyticOnValue g I →
    ∀ E : Set ℝ, E ⊆ I → Set.EqOn f g E →
      (∃ c ∈ I, ∀ ε : ℝ, 0 < ε →
        ∃ x ∈ E, 0 < |x-c| ∧ |x-c| < ε) →
      Set.EqOn f g I

def realIdentityOfOpenSubinterval : Prop :=
  ∀ (f g : ℝ → ℝ) (I : Set ℝ), IsOpen I → realIntervalValue I →
    RealAnalyticOnValue f I → RealAnalyticOnValue g I →
    ∀ J : Set ℝ, IsOpen J → realIntervalValue J → J.Nonempty →
      J ⊆ I → Set.EqOn f g J → Set.EqOn f g I

def complexRealIdentityOfOpenSubinterval : Prop :=
  ∀ (f g : ℝ → ℂ) (I : Set ℝ), IsOpen I → realIntervalValue I →
    ComplexRealAnalyticOnValue f I → ComplexRealAnalyticOnValue g I →
    ∀ J : Set ℝ, IsOpen J → realIntervalValue J → J.Nonempty →
      J ⊆ I → Set.EqOn f g J → Set.EqOn f g I

end Specs.SingleVariableAnalysis.Ch13.Identity
