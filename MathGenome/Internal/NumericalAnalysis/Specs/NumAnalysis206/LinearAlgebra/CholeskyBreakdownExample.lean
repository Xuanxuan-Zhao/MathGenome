import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.CholeskyBackward
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The concrete breakdown example in the proof of W26.  These data use W01
nearest rounding, rather than an assumed relative-error map.  No successful
execution hypothesis is included in the primitive trace. -/
noncomputable section

namespace NumAnalysis206.LinearAlgebra.CholeskyBreakdownData
open NumAnalysis206.Rounding
open NumAnalysis206.MatrixDefinitions

def format : RadixFormat where
  β := 2
  p := 4
  emin := -8
  emax := 2
  gradual := false
  radix_ge_two := by decide
  precision_pos := by decide
  exponent_order := by decide

def A : Mat ℝ 2 2 := !![(9 / 32 : ℝ), 1 / 4; 1 / 4, 1 / 4]

/-- The stored lower triangular output, allowing the final zero square root. -/
def L : Mat ℝ 2 2 := !![(1 / 2 : ℝ), 0; 1 / 2, 0]

/-- Only the state at t=1 in column 1 is used after a subtraction. -/
def states (i j : Fin 2) (t : ℕ) : ℝ := if t = 0 then A i j else 0

end NumAnalysis206.LinearAlgebra.CholeskyBreakdownData

namespace Specs.NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample
open _root_.NumAnalysis206.Rounding
open _root_.NumAnalysis206.LinearAlgebra.CholeskyData
open _root_.NumAnalysis206.LinearAlgebra.CholeskyBreakdownData

def inputProperties : Prop :=
  A.PosDef ∧ 0 < A 0 0 ∧ A.det = 1 / 128 ∧
    0 < A 1 1 - A 1 0 * A 0 1 / A 0 0 ∧
    ∀ i j, A i j ∈ Specs.FValue format

def roundedSteps : Prop :=
  Specs.flValue format (Real.sqrt (9 / 32)) = 1 / 2 ∧
  Specs.flValue format ((1 / 4) / (1 / 2)) = 1 / 2 ∧
  Specs.flValue format ((1 / 2) * (1 / 2)) = 1 / 4 ∧
  Specs.flValue format ((1 / 4) - Specs.flValue format ((1 / 2) * (1 / 2))) = 0

def breakdown : Prop :=
  PrimitiveTrace (Specs.flValue format) A L states ∧ states 1 1 1 = 0 ∧
  (∀ (L' : _root_.NumAnalysis206.MatrixDefinitions.Mat ℝ 2 2)
      (s : Fin 2 → Fin 2 → ℕ → ℝ),
    PrimitiveTrace (Specs.flValue format) A L' s → s 1 1 1 = 0) ∧
  ∀ (u : ℝ) (D : Set ℝ)
      (L' : _root_.NumAnalysis206.MatrixDefinitions.Mat ℝ 2 2)
      (s : Fin 2 → Fin 2 → ℕ → ℝ),
    ¬ SafeTrace (Specs.flValue format) u D A L' s

end Specs.NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample
