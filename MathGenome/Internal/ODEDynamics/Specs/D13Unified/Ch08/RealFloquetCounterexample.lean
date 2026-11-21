import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch08.RealFloquetCounterexample

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- Rotation through the angle πt, on the whole real time axis. -/
def R (t : ℝ) : Mat :=
  !![Real.cos (Real.pi * t), -Real.sin (Real.pi * t);
     Real.sin (Real.pi * t), Real.cos (Real.pi * t)]

/-- The explicitly prescribed fundamental matrix, with real powers. -/
def X (t : ℝ) : Mat := R t * !![1, 0; 0, (2 : ℝ) ^ t]

/-- The coefficient matrix in the source example; inverse is matrix inverse. -/
def A (t : ℝ) : Mat :=
  Real.pi • !![0, -1; 1, 0] + R t * !![0, 0; 0, Real.log 2] * (R t)⁻¹

def M : Mat := !![-1, 0; 0, -2]

end D13Unified.Ch08.RealFloquetCounterexample

namespace Specs.D13Unified.Ch08.RealFloquetCounterexample
open _root_.D13Unified.Ch08.RealFloquetCounterexample
open Specs.D13Unified.Ch07.MatrixExponential (exponentialValue)

/-- All assertions of paper.tex, d13:08:real-log-counterexample. No hypothesis
about a logarithm or a Floquet factor is assumed. In fact the obstruction
excludes even periodic factors with no differentiability hypothesis. -/
def Counterexample : Prop :=
  Continuous A ∧ Function.Periodic A 1 ∧ X 0 = 1 ∧
  (∀ t : ℝ, HasDerivAt X (A t * X t) t) ∧
  (∀ t : ℝ, IsUnit (X t)) ∧ X 1 = M ∧
  (∀ B : Mat, exponentialValue B 1 ≠ M) ∧
  ¬ ∃ (P : ℝ → Mat) (B : Mat), Function.Periodic P 1 ∧
    (∀ t : ℝ, IsUnit (P t)) ∧ ∀ t : ℝ, X t = P t * exponentialValue B t

end Specs.D13Unified.Ch08.RealFloquetCounterexample
