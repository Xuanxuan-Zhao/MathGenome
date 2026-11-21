import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.StabilityDefinitions
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent statements for paper.tex, d13:12:lyapunov.
The open neighborhood U is allowed to be smaller than the field domain.
All three conclusions use the original canonical maximal partial flow.
No trapping, completeness, or convergence certificate is an input. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch12.Lyapunov
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch12.StabilityDefinitions
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lieDerivative (F : AutonomousODE E) (V : E → ℝ) (x : E) : ℝ :=
  (fderiv ℝ V x) (autonomousEvalValue F x)

/-- The origin is stable, including complete forward nearby solutions. -/
def Stability : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0)
    (U : Set E), IsOpen U → (0 : E) ∈ U → U ⊆ F.domain →
    ∀ (V : E → ℝ), ContDiffOn ℝ 1 V U → V 0 = 0 →
    (∀ x ∈ U, x ≠ 0 → 0 < V x) →
    (∀ x ∈ U, lieDerivative F V x ≤ 0) →
    lyapunovStableValue F hF h0 heq

/-- Strict negativity is required only away from the equilibrium. -/
def AsymptoticStability : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0)
    (U : Set E), IsOpen U → (0 : E) ∈ U → U ⊆ F.domain →
    ∀ (V : E → ℝ), ContDiffOn ℝ 1 V U → V 0 = 0 →
    (∀ x ∈ U, x ≠ 0 → 0 < V x) →
    (∀ x ∈ U, x ≠ 0 → lieDerivative F V x < 0) →
    locallyAsymptoticallyStableValue F hF h0 heq

/-- The constants in the source's quantitative estimate are retained exactly.
The same small initial ball supports the estimate, forward completeness, and
confinement to the neighborhood on which the quadratic inequalities hold. -/
def ExponentialStability : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : E) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0)
    (U : Set E), IsOpen U → (0 : E) ∈ U → U ⊆ F.domain →
    ∀ (V : E → ℝ), ContDiffOn ℝ 1 V U →
    ∀ c₁ c₂ c₃ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ →
    (∀ x ∈ U, c₁ * ‖x‖ ^ 2 ≤ V x ∧ V x ≤ c₂ * ‖x‖ ^ 2) →
    (∀ x ∈ U, lieDerivative F V x ≤ -c₃ * ‖x‖ ^ 2) →
    locallyExponentiallyStableValue F hF h0 heq ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F.domain, ‖x‖ < δ →
        forwardCompleteValue F hF x ∧ ∀ t : ℝ, 0 ≤ t →
          flow F t x ∈ U ∧
          ‖flow F t x‖ ≤ Real.sqrt (c₂ / c₁) *
            Real.exp (-c₃ * t / (2 * c₂)) * ‖x‖

end Specs.D13Unified.Ch12.Lyapunov
