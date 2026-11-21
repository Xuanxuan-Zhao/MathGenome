import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalInstability
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch14.ZeroDivergence
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative _root_.D13Unified.Ch11.Orbits
open Ch01.AutonomousParameters Ch14.Multipliers Ch14.OrbitalDefinitions Ch14.OrbitalInstability

/-- A genuine planar periodic orbit at equality in the divergence criterion.
The least period and completeness concern the canonical maximal flow. -/
def ZeroDivergencePeriodicOrbit (F : AutonomousODE ℂ) (p : ℂ) (T : ℝ) : Prop :=
  ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain ∧ p ∈ F.domain ∧
  0 < T ∧ IsComplete F p ∧ Function.Periodic (fun t => flow F t p) T ∧
  (∀ S > 0, Function.Periodic (fun t => flow F t p) S → T ≤ S) ∧
  ¬ IsConstant F p ∧ (∫ t in (0 : ℝ)..T, divergence F (flow F t p)) = 0

/-- At zero divergence integral both asymptotic orbital stability and
orbital instability occur, with actual positive-time escape in the latter
case. The real plane is represented by ℂ. -/
def ZeroDivergenceBothOutcomes : Prop :=
  (∃ (F : AutonomousODE ℂ) (p : ℂ) (T : ℝ),
    ZeroDivergencePeriodicOrbit F p T ∧ orbitalAsymptoticallyStableValue F (orbit F p)) ∧
  (∃ (F : AutonomousODE ℂ) (p : ℂ) (T : ℝ),
    ZeroDivergencePeriodicOrbit F p T ∧
      distanceEscapeValue F p ∧ orbitalUnstableValue F (orbit F p))

end Specs.D13Unified.Ch14.ZeroDivergence
