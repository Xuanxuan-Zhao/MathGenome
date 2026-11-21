import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow

/-! Scalar part of paper.tex, Theorem d13:11:first-integral.
The ambient representative of H is only used on the original open state domain.
Constancy is asserted at every pair of times in a solution's actual interval;
neither forward completeness nor a restriction to nonnegative time is imposed.
The regular-constraint assertion of the source is a separate obligation. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch11.FirstIntegral
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch01.SolutionConcepts
universe u

/-- Vanishing directional derivative conserves H on every classical solution,
including restrictions of maximal solutions and intervals not containing zero. -/
def Conservation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ H : E → ℝ, ContDiffOn ℝ 1 H F.domain →
      (∀ x ∈ F.domain, (fderiv ℝ H x) (autonomousEvalValue F x) = 0) →
      ∀ (I : OpenTimeInterval) (x : ℝ → E),
        classicalSolutionOnValue (autonomousToODEValue F) I x →
        ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, H (x t) = H (x s)

/-- The canonical maximal solution through every initial point, with every time
in its actual lifespan, including negative times. -/
def FlowEquivalence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ H : E → ℝ, ContDiffOn ℝ 1 H F.domain →
      ((∀ x ∈ F.domain, ∀ t ∈ (flowInterval F x).carrier,
          H (flow F t x) = H x) ↔
        ∀ x ∈ F.domain, (fderiv ℝ H x) (autonomousEvalValue F x) = 0)

/-- Constancy on every maximal solution object is equivalent to DH f = 0.
The maximality predicate is the original absence of strict extension. -/
def MaximalEquivalence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ H : E → ℝ, ContDiffOn ℝ 1 H F.domain →
      ((∀ x : Solution (autonomousToODEValue F), maximalValue x →
          ∀ s ∈ x.interval.carrier, ∀ t ∈ x.interval.carrier,
            H (x.representative t) = H (x.representative s)) ↔
        ∀ x ∈ F.domain, (fderiv ℝ H x) (autonomousEvalValue F x) = 0)

end Specs.D13Unified.Ch11.FirstIntegral
