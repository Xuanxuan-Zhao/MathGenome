import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.MatrixLyapunov
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.LinearizedInstability

/-! Independent statements of paper.tex, d13:12:linearized-stability.
The matrix is the actual derivative in an arbitrary real basis. Both
implications retain the original C¹ field and its canonical partial flow.
There is no implication from a merely nonpositive spectrum. -/
noncomputable section
namespace Specs.D13Unified.Ch12.LinearizedStability
open _root_.D13Unified _root_.D13Unified.Ch12
open Ch01.AutonomousParameters Ch12.StabilityDefinitions
universe u v

def linearizedStabilityType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : Type v} [Fintype n] [DecidableEq n]
    (basis : Module.Basis n ℝ E) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0),
    IsHurwitz (LinearMap.toMatrix basis basis
      (fderiv ℝ (autonomousEvalValue F) 0).toLinearMap) →
      locallyExponentiallyStableValue F hF h0 heq

/-- The second implication is retained from the independently proved unstable
criterion, including escape at an actual time in the maximal interval. -/
def linearizedInstabilityType : Prop :=
  Specs.D13Unified.Ch12.LinearizedInstability.linearizedInstabilityType.{u, v}

end Specs.D13Unified.Ch12.LinearizedStability
