import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.HarmonicOscillator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Independent statements for paper.tex, d13:01:boundary-example.
The scalar statements use the shared C² solution predicate on a recorded open
interval. The companion statements also cover intervals with included endpoints,
using the shared continuity and within-derivative convention. All comparisons are
on the actual interval, and both boundary times must belong to that interval. -/

noncomputable section
open Set

namespace Specs.D13Unified.Ch01.BoundaryValueExample
open _root_.D13Unified _root_.D13Unified.HarmonicOscillator

/-- Every choice of coefficients gives a global classical solution. -/
def globalFamilyExpected : Prop :=
  ∀ A B : ℝ,
    ContDiff ℝ 2 (fun t => A * Real.cos t + B * Real.sin t) ∧
    ∀ t, HasDerivAt (deriv (fun t => A * Real.cos t + B * Real.sin t))
      (-(A * Real.cos t + B * Real.sin t)) t

/-- Exactly the restrictions of the two-parameter global family are solutions. -/
def classificationExpected : Prop :=
  ∀ (I : OpenTimeInterval) (y : ℝ → ℝ),
    IsOscillatorOn 1 I y ↔
      ∃ A B : ℝ, EqOn y (fun t => A * Real.cos t + B * Real.sin t) I.carrier

/-- The homogeneous two-point data leave precisely an arbitrary sine coefficient. -/
def homogeneousBoundaryExpected : Prop :=
  ∀ (I : OpenTimeInterval) (y : ℝ → ℝ), 0 ∈ I.carrier → Real.pi ∈ I.carrier →
    ((IsOscillatorOn 1 I y ∧ y 0 = 0 ∧ y Real.pi = 0) ↔
      ∃ B : ℝ, EqOn y (fun t => B * Real.sin t) I.carrier)

/-- The inhomogeneous boundary data have no solution. -/
def incompatibleBoundaryExpected : Prop :=
  ∀ (I : OpenTimeInterval) (y : ℝ → ℝ), 0 ∈ I.carrier → Real.pi ∈ I.carrier →
    ¬ (IsOscillatorOn 1 I y ∧ y 0 = 0 ∧ y Real.pi = 1)

/-- The same classification on every endpoint type, recording position and velocity. -/
def intervalClassificationExpected : Prop :=
  ∀ (I : TimeInterval) (Y : ℝ → (Fin 2 → ℝ)),
    Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue (equation 1).toODE I Y ↔
      ∃ A B : ℝ, EqOn Y
        (fun t => ![A * Real.cos t + B * Real.sin t,
          -A * Real.sin t + B * Real.cos t]) I.carrier

/-- Complete homogeneous boundary family, including compact solution intervals. -/
def intervalHomogeneousBoundaryExpected : Prop :=
  ∀ (I : TimeInterval) (Y : ℝ → (Fin 2 → ℝ)),
    0 ∈ I.carrier → Real.pi ∈ I.carrier →
    ((Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue (equation 1).toODE I Y ∧
      Y 0 0 = 0 ∧ Y Real.pi 0 = 0) ↔
      ∃ B : ℝ, EqOn Y (fun t => ![B * Real.sin t, B * Real.cos t]) I.carrier)

/-- Incompatible data are impossible also at included interval endpoints. -/
def intervalIncompatibleBoundaryExpected : Prop :=
  ∀ (I : TimeInterval) (Y : ℝ → (Fin 2 → ℝ)),
    0 ∈ I.carrier → Real.pi ∈ I.carrier →
    ¬ (Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue (equation 1).toODE I Y ∧
      Y 0 0 = 0 ∧ Y Real.pi 0 = 1)

end Specs.D13Unified.Ch01.BoundaryValueExample
