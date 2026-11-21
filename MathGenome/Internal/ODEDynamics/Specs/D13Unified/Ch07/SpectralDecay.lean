import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Exponential

noncomputable section

namespace Specs.D13Unified.Ch07.SpectralDecay

open _root_.D13Unified.Ch07
open Specs.D13Unified.Ch07.MatrixExponential (exponentialValue)
universe u v

/-- Spectral decay in the operator norm induced by the arbitrary fixed norm on
 the complex state space. The hypothesis concerns all eigenvalues, with no
 diagonalizability assumption. Time is real and the bound includes time zero. -/
def complexDecayType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (basis : Module.Basis n ℂ E) (A : Matrix n n ℂ) (a : ℝ), 0 < a →
    (∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' A) μ → μ.re < -a) →
    ∀ b : ℝ, 0 < b → b < a →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        matrixOperatorNorm basis (exponentialValue A t) ≤ C * Real.exp (-b * t)

/-- For a real matrix the spectral condition is imposed on its complexification.
 The conclusion uses the original real state space with its arbitrary fixed norm. -/
def realDecayType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (basis : Module.Basis n ℝ E) (A : Matrix n n ℝ) (a : ℝ), 0 < a →
    (∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) μ →
      μ.re < -a) →
    ∀ b : ℝ, 0 < b → b < a →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        matrixOperatorNorm basis (exponentialValue A t) ≤ C * Real.exp (-b * t)

end Specs.D13Unified.Ch07.SpectralDecay
