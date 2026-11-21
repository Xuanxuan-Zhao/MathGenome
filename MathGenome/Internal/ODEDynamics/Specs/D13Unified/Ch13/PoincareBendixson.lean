import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.OmegaSection
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Omega

/-! The original regular compact Poincaré–Bendixson theorem, paper.tex
lines 2900–2926. Extra premises used by conditional drafts are not part
of this independent statement. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch13.PoincareBendixson
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open _root_.D13Unified.Ch06.StateDerivative _root_.D13Unified.Ch11.Orbits
open Ch01.AutonomousParameters Ch11.OmegaTopology

/-- The entire omega set equals one nonconstant complete periodic trajectory,
with a positive least period (and all periods its integer multiples). -/
def PoincareBendixson : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, IsCompact (closure (positiveOrbit F x)) →
    closure (positiveOrbit F x) ⊆ F.domain →
    (∀ p ∈ omegaValue F x, autonomousEvalValue F p ≠ 0) →
    ∃ p ∈ omegaValue F x,
      ¬ IsConstant F p ∧ HasLeastPeriod F p ∧ omegaValue F x = orbit F p

end Specs.D13Unified.Ch13.PoincareBendixson
