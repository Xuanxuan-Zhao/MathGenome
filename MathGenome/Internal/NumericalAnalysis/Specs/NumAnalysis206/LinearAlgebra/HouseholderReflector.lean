import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Matrix.DotProduct

noncomputable section
open scoped BigOperators
open Matrix
namespace NumAnalysis206.HouseholderDefinitions

/-- The stable real sign convention, including signPlus 0 = 1. -/
def signPlus (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

/-- First coordinate vector; the instance expresses the source condition d ≥ 1. -/
def firstVector (d : ℕ) [NeZero d] : MatrixDefinitions.Vec ℝ d :=
  EuclideanSpace.single 0 1

def alpha {d : ℕ} [NeZero d] (x : MatrixDefinitions.Vec ℝ d) : ℝ :=
  -signPlus (x 0) * ‖x‖

def direction {d : ℕ} [NeZero d] (x : MatrixDefinitions.Vec ℝ d) :
    MatrixDefinitions.Vec ℝ d := x - alpha x • firstVector d

/-- I - 2 vvᵀ / (vᵀv), with the scalar division interpreted over ℝ. -/
def reflector {d : ℕ} (v : MatrixDefinitions.Vec ℝ d) : MatrixDefinitions.Mat ℝ d d :=
  1 - (2 / (⇑v ⬝ᵥ ⇑v)) • Matrix.vecMulVec (⇑v) (⇑v)

/-- A zero column tail requires no reflection. -/
def step {d : ℕ} [NeZero d] (x : MatrixDefinitions.Vec ℝ d) :
    MatrixDefinitions.Mat ℝ d d := if x = 0 then 1 else reflector (direction x)

end NumAnalysis206.HouseholderDefinitions

namespace Specs.NumAnalysis206.HouseholderReflector
open NumAnalysis206.MatrixDefinitions NumAnalysis206.HouseholderDefinitions

def signPlus_type := ℝ → ℝ
def signPlus_value : signPlus_type := signPlus

def firstVector_type := (d : ℕ) → [NeZero d] → Vec ℝ d
def firstVector_value : firstVector_type := firstVector

def alpha_type := {d : ℕ} → [NeZero d] → Vec ℝ d → ℝ
def alpha_value : alpha_type := @alpha

def direction_type := {d : ℕ} → [NeZero d] → Vec ℝ d → Vec ℝ d
def direction_value : direction_type := @direction

def reflector_type := {d : ℕ} → Vec ℝ d → Mat ℝ d d
def reflector_value : reflector_type := @reflector

def step_type := {d : ℕ} → [NeZero d] → Vec ℝ d → Mat ℝ d d
def step_value : step_type := @step

/-- W30, with Euclidean norm and real conjugate transpose. -/
def householder : Prop :=
  ∀ {d : ℕ} [NeZero d] (x : Vec ℝ d), x ≠ 0 →
    |direction x 0| = |x 0| + ‖x‖ ∧
    direction x ≠ 0 ∧
    (reflector (direction x)).conjTranspose * reflector (direction x) = 1 ∧
    reflector (direction x) *ᵥ ⇑x = ⇑(alpha x • firstVector d)

def step_zero : Prop :=
  ∀ (d : ℕ) [NeZero d], step (0 : Vec ℝ d) = 1

def step_nonzero : Prop :=
  ∀ {d : ℕ} [NeZero d] (x : Vec ℝ d), x ≠ 0 →
    step x = reflector (direction x)

end Specs.NumAnalysis206.HouseholderReflector
