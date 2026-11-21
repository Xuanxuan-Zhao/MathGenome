import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Independent statements for the unit-circle boundary example in Chapter 15. -/
namespace Specs.D13Unified.Ch15.UnitCircleExamples
open Filter Function
open scoped Topology
open Specs.D13Unified.Ch15.DiscreteDefinitions

abbrev ScalarMapType := ℝ → ℝ
def minus : ScalarMapType := fun x => x - x ^ 3
def plus : ScalarMapType := fun x => x + x ^ 3

def minus_continuousStatement : Prop := Continuous minus
def plus_continuousStatement : Prop := Continuous plus

def minus_fixedStatement : Prop := minus 0 = 0
def plus_fixedStatement : Prop := plus 0 = 0
def minus_derivativeStatement : Prop := HasDerivAt minus 1 0
def plus_derivativeStatement : Prop := HasDerivAt plus 1 0

def minus_abs_decreasesStatement : Prop :=
  ∀ x : ℝ, 0 < |x| → |x| < 1 → |minus x| < |x|
def minus_convergesStatement : Prop :=
  ∀ x : ℝ, |x| < 1 → Tendsto (fun n : ℕ => minus^[n] x) atTop (𝓝 0)
def minus_stableStatement : Prop := LyapunovStable minus 0
def minus_asymptotically_stableStatement : Prop := AsymptoticallyStable minus 0

def plus_abs_increasesStatement : Prop :=
  ∀ x : ℝ, x ≠ 0 → |x| < |plus x|
def plus_abs_iterates_strictMonoStatement : Prop :=
  ∀ x : ℝ, x ≠ 0 → StrictMono (fun n : ℕ => |plus^[n] x|)
def plus_escapeStatement : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x : ℝ, x ≠ 0 → ∃ n : ℕ, r ≤ |plus^[n] x|
def plus_first_exitStatement : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x : ℝ, 0 < |x| → |x| < r →
    ∃ N : ℕ, 0 < N ∧ r ≤ |plus^[N] x| ∧ ∀ n : ℕ, n < N → |plus^[n] x| < r
def plus_unstableStatement : Prop := ¬ LyapunovStable plus 0

end Specs.D13Unified.Ch15.UnitCircleExamples
