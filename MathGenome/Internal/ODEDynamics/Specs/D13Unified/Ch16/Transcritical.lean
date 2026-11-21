import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.SimplePersistence
import Mathlib.Analysis.Asymptotics.Defs

/-! Independent statement of paper.tex, Theorem d13:16:transcritical.
The parameter is the first coordinate, as in SimplePersistence. All
regularity and equations are local on the actual open domain. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch16.Transcritical
open Specs.D13Unified.Ch16.SimplePersistence

/-- The coefficient `f_{xμ}(0,0)`. -/
def mixedCoefficient (f : ℝ × ℝ → ℝ) : ℝ :=
  fderiv ℝ (stateDerivative f) (0,0) (1,0)

/-- The coefficient `f_{xx}(0,0)/2`. -/
def quadraticCoefficient (f : ℝ × ℝ → ℝ) : ℝ :=
  stateDerivative (stateDerivative f) (0,0) / 2

/-- Actual scalar stability, realized on exactly the translated state slice.
The stable conclusion includes forward existence and an exponential estimate;
the unstable conclusion includes finite-time escape in the canonical flow. -/
def HasScalarStability (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (μ p l : ℝ) : Prop :=
  ∃ F : D13Unified.AutonomousODE ℝ,
    F.domain = {y | (μ,p+y) ∈ U} ∧
    (∀ y ∈ F.domain,
      Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F y = f (μ,p+y)) ∧
    ∃ (hF : ContDiffOn ℝ 1
      (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain)
      (h0 : (0 : ℝ) ∈ F.domain)
      (heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0),
      (l < 0 → Specs.D13Unified.Ch12.StabilityDefinitions.locallyExponentiallyStableValue
        F hF h0 heq) ∧
      (0 < l → Specs.D13Unified.Ch12.LinearizedInstability.EscapeWitness F ∧
        Specs.D13Unified.Ch12.StabilityDefinitions.unstableValue F hF h0 heq)

/-- Both branches and every nearby equilibrium on one fixed product box. -/
def IsTranscriticalGraph (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (χ : ℝ → ℝ) (r s : ℝ) : Prop :=
  0 < r ∧ 0 < s ∧ χ 0 = 0 ∧
    Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U ∧
    ContDiffOn ℝ 1 χ (Metric.ball 0 r) ∧
    ∀ μ ∈ Metric.ball 0 r,
      χ μ ∈ Metric.ball 0 s ∧
      (χ μ = 0 ↔ μ = 0) ∧
      ∀ x ∈ Metric.ball 0 s, f (μ,x) = 0 ↔ x = 0 ∨ x = χ μ

end D13Unified.Ch16.Transcritical

namespace Specs.D13Unified.Ch16.Transcritical
open _root_.Specs.D13Unified.Ch16.SimplePersistence
open _root_.D13Unified.Ch16.Transcritical

/-- The full local transcritical exchange theorem under the original
regularity and nondegeneracy hypotheses. -/
def transcriticalExchange : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0,0) ∈ U → ContDiffOn ℝ 3 f U →
    (∀ᶠ μ in 𝓝 (0 : ℝ), f (μ,0) = 0) →
    stateDerivative f (0,0) = 0 →
    mixedCoefficient f ≠ 0 → quadraticCoefficient f ≠ 0 →
    ∃ χ : ℝ → ℝ, ∃ r s : ℝ,
      IsTranscriticalGraph f U χ r s ∧
      HasDerivAt χ (-mixedCoefficient f / quadraticCoefficient f) 0 ∧
      Asymptotics.IsLittleO (𝓝 (0 : ℝ))
        (fun μ => χ μ - (-mixedCoefficient f / quadraticCoefficient f) * μ)
        (fun μ : ℝ => μ) ∧
      ∀ μ ∈ Metric.ball 0 r, μ ≠ 0 →
        0 < stateDerivative f (μ,0) * (mixedCoefficient f * μ) ∧
        stateDerivative f (μ,χ μ) * (mixedCoefficient f * μ) < 0 ∧
        HasScalarStability f U μ 0 (mixedCoefficient f * μ) ∧
        HasScalarStability f U μ (χ μ) (-(mixedCoefficient f * μ))

end Specs.D13Unified.Ch16.Transcritical
