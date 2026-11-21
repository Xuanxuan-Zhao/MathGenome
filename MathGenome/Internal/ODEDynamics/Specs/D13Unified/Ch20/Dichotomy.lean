import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.HyperbolicSplitting
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

namespace Specs.D13Unified.Ch20.Dichotomy
open _root_.D13Unified _root_.D13Unified.Ch07 _root_.D13Unified.Ch20
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch07.MatrixExponential
universe u v

/-- The canonical real projections, represented as matrices in the common
coordinate space. These use the same generalized spectral sums as Chapter 20. -/
def projectionMatrix {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (stable : Bool) : Matrix n n ℝ :=
  Matrix.toLinAlgEquiv'.symm (projectionValue A stable)

/-- Both estimates in any fixed norm, using its induced operator norm.
The finite index type may be empty; neither spectral subspace need be nonzero. -/
def dichotomyType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∃ K α : ℝ, 1 ≤ K ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
      matrixOperatorNorm b (exponentialValue A t * projectionMatrix A true) ≤
        K * Real.exp (-α * t) ∧
      matrixOperatorNorm b (exponentialValue A (-t) * projectionMatrix A false) ≤
        K * Real.exp (-α * t)

/-- Bounded differentiable solutions on the entire real line vanish.
The equation itself implies C¹ regularity, so no extra regularity is assumed. -/
def boundedSolutionType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A → ∀ z : ℝ → E,
    (∀ t : ℝ, HasDerivAt z (matrixOperatorEquiv b A (z t)) t) →
    (∃ M : ℝ, ∀ t : ℝ, ‖z t‖ ≤ M) → ∀ t : ℝ, z t = 0

end Specs.D13Unified.Ch20.Dichotomy
