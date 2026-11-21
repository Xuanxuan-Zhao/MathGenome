import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.StabilityDefinitions
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The scalar examples in paper.tex, d13:12:zero-example. All trajectories
below refer to the existing canonical maximal solution, on its actual domain.
The quotient by sqrt is the real formula x₀(1−2atx₀²)^(−1/2).
The coefficient a = −1, 1, 0 gives precisely the three source fields. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch12.ZeroExample
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch04.MaximalSolutionMap Ch12.StabilityDefinitions

def cubicODE (a : ℝ) : AutonomousODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun x => a * x.val ^ 3
  continuous_field := continuous_const.mul (continuous_subtype_val.pow 3)

def cubicCurve (a x t : ℝ) : ℝ := x / Real.sqrt (1 - 2 * a * t * x^2)

def escapeTime (x : ℝ) : ℝ := 1 / (2 * x^2)

def FieldProperties : Prop :=
  ∀ a : ℝ, ContDiffOn ℝ 1 (autonomousEvalValue (cubicODE a)) univ ∧
    autonomousEvalValue (cubicODE a) 0 = 0 ∧
    HasDerivAt (autonomousEvalValue (cubicODE a)) 0 0

def NegativeFormula : Prop :=
  ∀ x t : ℝ, 0 ≤ t → (t,x) ∈ flowDomain (cubicODE (-1)) ∧
    flow (cubicODE (-1)) t x = x / Real.sqrt (1 + 2*t*x^2)

def NegativeStability : Prop :=
  ∀ (hF : ContDiffOn ℝ 1 (autonomousEvalValue (cubicODE (-1))) univ),
    locallyAsymptoticallyStableValue (cubicODE (-1)) hF (mem_univ 0) (by
      simp [autonomousEvalValue, cubicODE])

/-- The whole actual interval and its finite upper endpoint are specified.
The divergence is to +∞ in real time approaching the endpoint from below. -/
def PositiveEscape : Prop :=
  ∀ x : ℝ, 0 < x →
    (flowInterval (cubicODE 1) x).carrier = Iio (escapeTime x) ∧
    upperEndpointValue (autonomousToODEValue (cubicODE 1)) 0 x = (escapeTime x : EReal) ∧
    (∀ t < escapeTime x, flow (cubicODE 1) t x = cubicCurve 1 x t) ∧
    Tendsto (fun t => flow (cubicODE 1) t x) (𝓝[<] (escapeTime x)) atTop

def PositiveInstability : Prop :=
  ∀ (hF : ContDiffOn ℝ 1 (autonomousEvalValue (cubicODE 1)) univ),
    unstableValue (cubicODE 1) hF (mem_univ 0) (by
      simp [autonomousEvalValue, cubicODE])

def ZeroFormula : Prop :=
  ∀ x t : ℝ, (t,x) ∈ flowDomain (cubicODE 0) ∧ flow (cubicODE 0) t x = x

/-- The explicit non-attraction clause rules out attraction of any neighborhood,
independently of the stable part of asymptotic stability. -/
def ZeroStability : Prop :=
  ∀ (hF : ContDiffOn ℝ 1 (autonomousEvalValue (cubicODE 0)) univ),
    lyapunovStableValue (cubicODE 0) hF (mem_univ 0) (by
      simp [autonomousEvalValue, cubicODE]) ∧
    ¬ (∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, ‖x‖ < δ →
      Tendsto (fun t => flow (cubicODE 0) t x) atTop (𝓝 0))

end Specs.D13Unified.Ch12.ZeroExample
