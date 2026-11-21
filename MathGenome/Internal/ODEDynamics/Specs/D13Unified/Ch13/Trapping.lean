import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Nullclines
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Invariant

/-! Independent statement of paper.tex, Chapter 13, d13:13:trapping.
Positive invariance refers only to times in the actual maximal interval.
Forward completeness is a conclusion, as are the complete periodic orbit
and its classical solution on all real time. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch13.Trapping
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open _root_.D13Unified.Ch06.StateDerivative _root_.D13Unified.Ch11.Orbits
open Ch01.AutonomousParameters Ch11.Invariant

/-- Every compact nonempty positively invariant planar set without equilibria
contains a nonconstant periodic orbit. Its canonical solution is complete,
has a positive least period, is C¹ on ℝ, and satisfies the original equation.
All starting points in the trapping set have complete forward solutions. -/
def Trapping : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ K : Set Plane, K.Nonempty → IsCompact K → positiveInvariantValue F K →
    (∀ p ∈ K, autonomousEvalValue F p ≠ 0) →
    (∀ x ∈ K, Ici 0 ⊆ (flowInterval F x).carrier ∧
      ∀ t : ℝ, 0 ≤ t → flow F t x ∈ K) ∧
    ∃ p ∈ K, ¬ IsConstant F p ∧ HasLeastPeriod F p ∧ orbit F p ⊆ K ∧
      ContDiff ℝ 1 (fun t => flow F t p) ∧
      (∀ t : ℝ, HasDerivAt (fun r => flow F r p)
        (autonomousEvalValue F (flow F t p)) t) ∧
      flow F 0 p = p

end Specs.D13Unified.Ch13.Trapping
