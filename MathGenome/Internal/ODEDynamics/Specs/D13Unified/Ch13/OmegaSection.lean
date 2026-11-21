import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.MonotoneCrossings
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.OmegaTopology

/-! Independent original statements for the omega-limit consequence of
paper.tex, d13:13:monotone-crossings, lines 2888–2897. The omega set is the
ambient intersection of all late closed tails, including when it is empty.
No compactness assumption is made on the orbit or its closure. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch13.OmegaSection
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch13.Nullclines Ch11.OmegaTopology

/-- Relative interior of the chosen straight segment, not ambient interior. -/
def sectionInteriorValue (S : StraightSegment) : Set Plane :=
  segmentPointValue S '' Ioo (-S.radius) S.radius

/-- The same forward-complete orbit's omega set meets the interior of any
straight transverse segment in at most one point. -/
def OmegaSection : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, Ici 0 ⊆ (flowInterval F x).carrier →
    ∀ S : TransverseSegment F,
      (omegaValue F x ∩ sectionInteriorValue S.toStraightSegment).Subsingleton

/-- Arbitrarily short sections through every regular point. If the center
belongs to this orbit's omega set, the intersection is exactly the center. -/
def RegularSection : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, Ici 0 ⊆ (flowInterval F x).carrier →
    ∀ p ∈ F.domain, autonomousEvalValue F p ≠ 0 →
    ∀ R : ℝ, 0 < R → ∃ S : TransverseSegment F,
      S.center = p ∧ S.radius < R ∧
      (omegaValue F x ∩ sectionInteriorValue S.toStraightSegment).Subsingleton ∧
      (p ∈ omegaValue F x →
        omegaValue F x ∩ sectionInteriorValue S.toStraightSegment = {p})
end Specs.D13Unified.Ch13.OmegaSection
