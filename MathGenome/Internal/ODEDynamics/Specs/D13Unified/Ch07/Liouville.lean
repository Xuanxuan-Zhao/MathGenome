import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.EvolutionMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Independent statements for paper.tex, Theorem d13:07:liouville.
Both scalar fields use oriented integrals in real time. The matrix solution
and every derivative retain their actual interval, including its endpoints.
-/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace Specs.D13Unified.Ch07.Liouville
open _root_.D13Unified _root_.D13Unified.Ch07.EvolutionMatrix

/-- Liouville's formula for every fundamental matrix over ℝ or ℂ. -/
def Formula : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A X : ℝ → Matrix (Fin n) (Fin n) 𝕂),
    ContinuousOn A I.carrier → IsFundamentalMatrixOn I A X →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier,
      (X t).det = (X s).det * NormedSpace.exp (∫ r in s..t, (A r).trace)

/-- The real determinant has one fixed, nonzero sign on the whole interval. -/
def RealConstantSign : Prop :=
  ∀ (n : ℕ) (I : TimeInterval) (A X : ℝ → Matrix (Fin n) (Fin n) ℝ),
    ContinuousOn A I.carrier → IsFundamentalMatrixOn I A X →
    (∀ t ∈ I.carrier, 0 < (X t).det) ∨ (∀ t ∈ I.carrier, (X t).det < 0)

end Specs.D13Unified.Ch07.Liouville
