import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.SimplePersistence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent specification of paper.tex, Theorem d13:16:pitchfork.
The coordinates are `(μ,x)`, consistently with SimplePersistence. Regularity
and symmetry are imposed only on the actual open neighborhood `U`. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch16.Pitchfork
open Specs.D13Unified.Ch16.SimplePersistence

/-- Local odd symmetry wherever both reflected points lie in the domain.
Every open neighborhood of the origin contains a symmetric product box. -/
def OddOn (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ μ x : ℝ, (μ,x) ∈ U → (μ,-x) ∈ U → f (μ,-x) = -f (μ,x)

/-- `f_{xμ}(0,0)`, with parameter first in the product coordinates. -/
def mixedCoefficient (f : ℝ × ℝ → ℝ) : ℝ :=
  fderiv ℝ (stateDerivative f) (0,0) (1,0)

/-- The cubic coefficient `f_{xxx}(0,0)/6`. -/
def cubicCoefficient (f : ℝ × ℝ → ℝ) : ℝ :=
  stateDerivative (stateDerivative (stateDerivative f)) (0,0) / 6

/-- The actual scalar equation centered at an equilibrium, on precisely the
original parameter slice. Stability includes existence for all forward times;
instability includes a finite-time escape witness for the canonical flow. -/
def ScalarStabilityAt (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (μ p : ℝ) : Prop :=
  ∃ F : _root_.D13Unified.AutonomousODE ℝ,
    F.domain = {y | (μ,p+y) ∈ U} ∧
    (∀ y ∈ F.domain,
      Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F y = f (μ,p+y)) ∧
    ∃ (hF : ContDiffOn ℝ 1
        (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain)
      (h0 : (0 : ℝ) ∈ F.domain)
      (heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0),
      (stateDerivative f (μ,p) < 0 →
        Specs.D13Unified.Ch12.StabilityDefinitions.locallyExponentiallyStableValue F hF h0 heq) ∧
      (0 < stateDerivative f (μ,p) →
        Specs.D13Unified.Ch12.LinearizedInstability.EscapeWitness F ∧
        Specs.D13Unified.Ch12.StabilityDefinitions.unstableValue F hF h0 heq)

/-- A single fixed product neighborhood contains exactly the claimed roots.
The conditions at μ=0 are included. Strict sign products at nonzero μ state
both the sign and nonvanishing, without classifying the degenerate origin. -/
def Conclusion (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (a b : ℝ) : Prop :=
  ∃ s : ℝ → ℝ, ∃ α ρ : ℝ,
    0 < α ∧ 0 < ρ ∧
    Metric.ball 0 α ×ˢ Metric.ball 0 ρ ⊆ U ∧
    ContDiffOn ℝ 1 s (Metric.ball 0 α) ∧
    s 0 = 0 ∧ HasDerivAt s (-a/b) 0 ∧
    (∀ μ ∈ Metric.ball 0 α,
      f (μ,0) = 0 ∧
      (μ ≠ 0 → 0 < s μ * (-a*μ/b)) ∧
      (0 < -a*μ/b → 0 < Real.sqrt (s μ) ∧ Real.sqrt (s μ) < ρ) ∧
      (∀ x ∈ Metric.ball 0 ρ,
        f (μ,x) = 0 ↔ x = 0 ∨
          (0 < -a*μ/b ∧ (x = Real.sqrt (s μ) ∨ x = -Real.sqrt (s μ)))) ∧
      (μ ≠ 0 →
        0 < stateDerivative f (μ,0) * (a*μ) ∧
        ScalarStabilityAt f U μ 0 ∧
        ∀ x ∈ Metric.ball 0 ρ, x ≠ 0 → f (μ,x) = 0 →
          0 < stateDerivative f (μ,x) * (-a*μ) ∧ ScalarStabilityAt f U μ x))

/-- The original unconditional target. No upstream proof or reduction
certificate is assumed in this independent specification. -/
def pitchfork : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (0,0) ∈ U → ContDiffOn ℝ 5 f U → OddOn f U →
    stateDerivative f (0,0) = 0 →
    mixedCoefficient f ≠ 0 → cubicCoefficient f ≠ 0 →
    Conclusion f U (mixedCoefficient f) (cubicCoefficient f)

end Specs.D13Unified.Ch16.Pitchfork
