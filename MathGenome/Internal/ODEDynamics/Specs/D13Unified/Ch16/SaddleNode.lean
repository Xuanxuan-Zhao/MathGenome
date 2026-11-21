import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.SimplePersistence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
The parameter is the first coordinate, as in `SimplePersistence`.
The conclusion concerns exactly the local zero set, with its original time
parameter in the separate stability assertions.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch16.SaddleNode
open Specs.D13Unified.Ch16.SimplePersistence

/-- Parameter partial derivative of the original family. -/
def parameterDerivative (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ f z (1, 0)

/-- Second state partial derivative of the original family. -/
def stateSecondDerivative (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (stateDerivative f) z (0, 1)

/-- Coefficient with the normalization of the paper. -/
def coefficient (f : ℝ × ℝ → ℝ) : ℝ :=
  -stateSecondDerivative f (0, 0) / (2 * parameterDerivative f (0, 0))

/-- Stability is asserted for the actual parameter slice, centered at the
particular equilibrium, on exactly the prescribed open domain. -/
def HasScalarStability (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (μ p : ℝ) : Prop :=
  ∃ F : D13Unified.AutonomousODE ℝ,
    F.domain = {y | (μ, p + y) ∈ U} ∧
    (∀ y ∈ F.domain,
      Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F y = f (μ, p + y)) ∧
    ∃ (hF : ContDiffOn ℝ 1
        (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain)
      (h0 : (0 : ℝ) ∈ F.domain)
      (heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0),
      (stateDerivative f (μ, p) < 0 →
        Specs.D13Unified.Ch12.StabilityDefinitions.locallyExponentiallyStableValue F hF h0 heq) ∧
      (0 < stateDerivative f (μ, p) →
        Specs.D13Unified.Ch12.LinearizedInstability.EscapeWitness F ∧
        Specs.D13Unified.Ch12.StabilityDefinitions.unstableValue F hF h0 heq)

/-- All conclusions of the generic scalar saddle-node in one fixed state
neighborhood and one fixed parameter interval. The coordinate has an actual
C¹ inverse, fixes zero, and has derivative one. -/
def SaddleNodeConclusion (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  coefficient f ≠ 0 ∧
  ∃ e : OpenPartialHomeomorph ℝ ℝ, ∃ ε : ℝ,
    0 < ε ∧ (0 : ℝ) ∈ e.source ∧ e 0 = 0 ∧
    ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
    HasDerivAt e 1 0 ∧
    Metric.ball 0 ε ×ˢ e.source ⊆ U ∧
    (∀ μ ∈ Metric.ball 0 ε, ∀ x ∈ e.source,
      f (μ, x) = 0 ↔ μ = coefficient f * (e x) ^ 2) ∧
    (∀ μ ∈ Metric.ball 0 ε,
      (μ / coefficient f < 0 → ∀ x ∈ e.source, f (μ, x) ≠ 0) ∧
      (μ = 0 → ∀ x ∈ e.source, f (μ, x) = 0 ↔ x = 0) ∧
      (0 < μ / coefficient f →
        ∃ xneg xpos : ℝ, xneg ∈ e.source ∧ xpos ∈ e.source ∧ xneg < 0 ∧ 0 < xpos ∧
          e xneg = -Real.sqrt (μ / coefficient f) ∧
          e xpos = Real.sqrt (μ / coefficient f) ∧
          (∀ x ∈ e.source, f (μ, x) = 0 ↔ x = xneg ∨ x = xpos) ∧
          stateDerivative f (μ, xneg) * stateDerivative f (μ, xpos) < 0 ∧
          HasScalarStability f U μ xneg ∧ HasScalarStability f U μ xpos)) ∧
    (∀ x ∈ e.source, f (0, x) = 0 ↔ x = 0) ∧
    stateDerivative f (0, 0) = 0 ∧ stateSecondDerivative f (0, 0) ≠ 0

end D13Unified.Ch16.SaddleNode
namespace Specs.D13Unified.Ch16.SaddleNode
open Specs.D13Unified.Ch16.SimplePersistence
open _root_.D13Unified.Ch16.SaddleNode

/-- The generic scalar saddle-node under the source's local C³ and
nondegeneracy hypotheses. No behavior outside the open neighborhood is assumed. -/
def saddleNode : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0, 0) ∈ U → ContDiffOn ℝ 3 f U →
    f (0, 0) = 0 → stateDerivative f (0, 0) = 0 →
    parameterDerivative f (0, 0) ≠ 0 → stateSecondDerivative f (0, 0) ≠ 0 →
    SaddleNodeConclusion f U

end Specs.D13Unified.Ch16.SaddleNode
