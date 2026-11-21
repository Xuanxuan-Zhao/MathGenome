import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.ControlledPicard

/-! Independent statements for paper.tex, d13:03:uniqueness.
The shared ODE contains its open domain and continuous field. The state space
is any finite-dimensional real normed space, with its given norm. All solution
and comparison conditions concern the recorded actual open intervals only.
-/
noncomputable section
open Set
open _root_.D13Unified

namespace Specs.D13Unified.Ch03.LocalExistenceUniqueness
universe u

/-- Every admissible datum has a classical solution on an actual nonempty open
interval through its initial time, agreeing with every other such solution on
the entire common interval, on both sides of the initial time. -/
def localExistenceUniquenessExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E),
    LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (s : ℝ) (ξ : E), (s, ξ) ∈ F.domain →
    ∃ (I : OpenTimeInterval) (x : ℝ → E),
      Ch01.SolutionConcepts.classicalIVPOnValue F I x s ξ ∧
      ∀ (J : OpenTimeInterval) (y : ℝ → E),
        Ch01.SolutionConcepts.classicalIVPOnValue F J y s ξ →
        EqOn x y (I.carrier ∩ J.carrier)

/-- Uniqueness compares arbitrary solutions, without a controlled-box range
restriction and without requiring that either solution be maximal. -/
def overlapUniquenessExpected : Prop :=
  ControlledPicard.overlapUniquenessExpected.{u}

/-- Meeting at any common time forces agreement throughout the common interval.
The meeting time need not be either solution's originally chosen base time. -/
def noCrossingExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E),
    LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (I J : OpenTimeInterval) (x y : ℝ → E) (s : ℝ),
      Ch01.SolutionConcepts.classicalSolutionOnValue F I x →
      Ch01.SolutionConcepts.classicalSolutionOnValue F J y →
      s ∈ I.carrier ∩ J.carrier → x s = y s →
      EqOn x y (I.carrier ∩ J.carrier)

end Specs.D13Unified.Ch03.LocalExistenceUniqueness
