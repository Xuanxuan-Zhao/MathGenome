import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz
import Mathlib.Analysis.Real.Sqrt

/-! Independent specification for paper.tex, d13:03:nonunique.
The scalar field is defined on all real time-state pairs. Curves have the
actual full open time interval, C¹ regularity, the differential equation,
and initial data in the common upstream solution concept.
-/

noncomputable section
open Set

namespace D13Unified.WaitingTime

/-- The continuous scalar field in the nonuniqueness example. -/
def field (x : ℝ) : ℝ := 2 * Real.sqrt |x|

/-- The solution that waits at zero up to time `a`. -/
def curve (a t : ℝ) : ℝ := if t ≤ a then 0 else (t - a) ^ 2

/-- The actual time-state domain is all of ℝ × ℝ. -/
def equation : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => field p.val.2
  continuous_field := by
    unfold field
    fun_prop

/-- The full real time interval; no finite endpoint is suppressed. -/
def wholeTime : OpenTimeInterval :=
  ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩

end D13Unified.WaitingTime

namespace Specs.D13Unified.Ch03.WaitingTimeNonuniqueness
open _root_.D13Unified
open _root_.D13Unified.WaitingTime

def fieldContinuousExpected : Prop := Continuous field

def curveDerivativeExpected : Prop :=
  ∀ a t : ℝ, HasDerivAt (curve a) (2 * max (t - a) 0) t

def joinDerivativeExpected : Prop :=
  ∀ a : ℝ, HasDerivAt (curve a) 0 a

def globalIVPExpected : Prop :=
  ∀ a : ℝ, 0 ≤ a →
    Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
      equation wholeTime (curve a) 0 0

def zeroGlobalIVPExpected : Prop :=
  Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
    equation wholeTime (fun _ => 0) 0 0

def distinctExpected : Prop :=
  ∀ a b : ℝ, a < b → curve a ≠ curve b

def distinctFromZeroExpected : Prop :=
  ∀ a : ℝ, curve a ≠ (fun _ => 0)

/-- Two different global classical solutions with the same zero initial data. -/
def nonuniqueExpected : Prop :=
  ∃ x y : ℝ → ℝ,
    Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
      equation wholeTime x 0 0 ∧
    Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
      equation wholeTime y 0 0 ∧ x ≠ y

def quotientExpected : Prop :=
  ∀ x : ℝ, 0 < x → |field x - field 0| / |x| = 2 / Real.sqrt x

/-- Arbitrarily large quotients in every positive right neighborhood of zero. -/
def quotientUnboundedExpected : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ M : ℝ,
    ∃ x : ℝ, 0 < x ∧ x < ε ∧ M < |field x - field 0| / |x|

/-- Explicit failure of any state Lipschitz estimate on a product about (0,0). -/
def noLocalBoundExpected : Prop :=
  ∀ a b L : ℝ, 0 < a → 0 < b → 0 ≤ L →
    ¬ Specs.D13Unified.Ch03.LocalLipschitz.stateLipschitzOnValue
      equation.eval (Metric.ball 0 a) (Metric.ball 0 b) L

def notLocallyLipschitzExpected : Prop :=
  ¬ Specs.D13Unified.Ch03.LocalLipschitz.locallyLipschitzInStateValue equation

end Specs.D13Unified.Ch03.WaitingTimeNonuniqueness
