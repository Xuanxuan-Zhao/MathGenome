import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Basic

/-! Independent statements for paper.tex, example d13:06:smooth-not-analytic.
The forcing is one-sided; the primitive is an oriented integral on all real time.
All derivative orders include order zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Specs.D13Unified.Ch06.SmoothNonanalyticExample

def gType := ℝ → ℝ

def gValue (t : ℝ) : ℝ := if 0 < t then Real.exp (-1 / t ^ 2) else 0

def xType := ℝ → ℝ

def xValue (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, gValue r

def smoothExpected : Prop := ContDiff ℝ ∞ gValue

/-- One polynomial for each derivative order, valid at every positive time. -/
def polynomialDerivativesExpected : Prop :=
  ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ t : ℝ, 0 < t →
    iteratedDeriv n gValue t = p.eval t⁻¹ * Real.exp (-1 / t ^ 2)

def derivativeLimitsExpected : Prop :=
  ∀ n : ℕ, Tendsto (iteratedDeriv n gValue) (𝓝[>] 0) (𝓝 0)

def flatForcingExpected : Prop := ∀ n : ℕ, iteratedDeriv n gValue 0 = 0

def smoothIVPExpected : Prop :=
  ContDiff ℝ ∞ xValue ∧ xValue 0 = 0 ∧ ∀ t, HasDerivAt xValue (gValue t) t

/-- Existence and uniqueness also on every actual interval containing zero;
this uses the shared endpoint-aware scalar solution convention. -/
def uniqueIVPExpected : Prop :=
  ∀ (I : _root_.D13Unified.TimeInterval), 0 ∈ I.carrier →
    _root_.D13Unified.ScalarLinear.IsIVP I (fun _ => 0) gValue 0 0 xValue ∧
    ∀ y : ℝ → ℝ,
      _root_.D13Unified.ScalarLinear.IsIVP I (fun _ => 0) gValue 0 0 y ↔
      EqOn y xValue I.carrier

def flatSolutionExpected : Prop := ∀ n : ℕ, iteratedDeriv n xValue 0 = 0

def positiveSolutionExpected : Prop := ∀ t : ℝ, 0 < t → 0 < xValue t

/-- The actual Taylor coefficients vanish and the Taylor series sums to zero
at every real argument. -/
def zeroTaylorExpected : Prop :=
  (∀ n : ℕ, iteratedDeriv n xValue 0 / (n.factorial : ℝ) = 0) ∧
  ∀ t : ℝ, HasSum (fun n : ℕ =>
    iteratedDeriv n xValue 0 / (n.factorial : ℝ) * t ^ n) 0

/-- Every neighborhood contains a point where the Taylor series fails. -/
def taylorFailureExpected : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t| < ε ∧
    ¬ HasSum (fun n : ℕ =>
      iteratedDeriv n xValue 0 / (n.factorial : ℝ) * t ^ n) (xValue t)

def nonanalyticExpected : Prop := ¬ AnalyticAt ℝ xValue 0

end Specs.D13Unified.Ch06.SmoothNonanalyticExample
