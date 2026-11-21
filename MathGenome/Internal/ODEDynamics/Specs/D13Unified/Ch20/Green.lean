import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Dichotomy
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Independent specification of paper.tex, Lemma d13:20:green.
The state norm is arbitrary and the projections are the canonical real spectral
projections. Half-line Bochner integrability includes absolute convergence.
The limits below also identify these integrals with oriented improper integrals.
No solution or Green-inverse certificate is assumed in these definitions. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace D13Unified.Ch20.Green
open D13Unified.Ch07
open Specs.D13Unified.Ch07.MatrixExponential
open Specs.D13Unified.Ch20.Dichotomy

variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual kernel in the fixed norm, with either canonical projection. -/
def kernel (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (stable : Bool) (g : ℝ → E) (t s : ℝ) : E :=
  matrixOperatorEquiv b (exponentialValue A (t - s) * projectionMatrix A stable) (g s)

/-- The two-sided Green formula, defined before any regularity is proved. -/
def greenValue (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (g : ℝ →ᵇ E) (t : ℝ) : E :=
  (∫ s in Iic t, kernel b A true g t s) -
    ∫ s in Ioi t, kernel b A false g t s

/-- The same estimates and the same constants as in the exponential dichotomy. -/
def DichotomyBounds (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (K α : ℝ) : Prop :=
  1 ≤ K ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
    matrixOperatorNorm b (exponentialValue A t * projectionMatrix A true) ≤
      K * Real.exp (-α * t) ∧
    matrixOperatorNorm b (exponentialValue A (-t) * projectionMatrix A false) ≤
      K * Real.exp (-α * t)

end D13Unified.Ch20.Green

namespace Specs.D13Unified.Ch20.Green
open _root_.D13Unified.Ch07 _root_.D13Unified.Ch20.Green
open Specs.D13Unified.Ch20.HyperbolicSplitting
universe u v

/-- Bounded continuous functions form the complete supremum-norm space, and
all ordinary bounded continuous functions have representatives in this space. -/
def functionSpaceExpected : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    CompleteSpace (ℝ →ᵇ E) ∧
    (∀ (g : ℝ →ᵇ E) (C : ℝ), ‖g‖ ≤ C ↔ ∀ t : ℝ, ‖g t‖ ≤ C) ∧
    (∀ g : ℝ → E, Continuous g → (∃ C : ℝ, ∀ t, ‖g t‖ ≤ C) →
      ∃ G : ℝ →ᵇ E, ∀ t, G t = g t)

def greenType :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    Module.Basis n ℝ E → Matrix n n ℝ → (ℝ →ᵇ E) → ℝ → E

def greenExpectedValue : greenType := @greenValue

/-- Absolute convergence and identification with both improper limits. -/
def convergenceExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (K α : ℝ),
    DichotomyBounds b A K α → ∀ (g : ℝ →ᵇ E) (t : ℝ),
      IntegrableOn (kernel b A true g t) (Iic t) ∧
      IntegrableOn (kernel b A false g t) (Ioi t) ∧
      Tendsto (fun a : ℝ => ∫ s in a..t, kernel b A true g t s) atBot
        (𝓝 (∫ s in Iic t, kernel b A true g t s)) ∧
      Tendsto (fun a : ℝ => ∫ s in t..a, kernel b A false g t s) atTop
        (𝓝 (∫ s in Ioi t, kernel b A false g t s))

/-- The full bounded Green inverse, with no restriction on dimension (including
zero), either spectral subspace, the fixed norm, or the bounded continuous
forcing. Uniqueness covers every differentiable bounded whole-line solution.
The equation also yields the explicitly asserted C¹ regularity. -/
def inverseExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ K α : ℝ, DichotomyBounds b A K α → ∀ g : ℝ →ᵇ E,
      ∃ G : ℝ →ᵇ E,
        (∀ t : ℝ, G t = greenValue b A g t) ∧
        ContDiff ℝ 1 (G : ℝ → E) ∧
        (∀ t : ℝ, HasDerivAt (G : ℝ → E) (matrixOperatorEquiv b A (G t) + g t) t) ∧
        ‖G‖ ≤ (2 * K / α) * ‖g‖ ∧
        (∀ z : ℝ → E,
          (∀ t : ℝ, HasDerivAt z (matrixOperatorEquiv b A (z t) + g t) t) →
          (∃ M : ℝ, ∀ t : ℝ, ‖z t‖ ≤ M) → ∀ t : ℝ, z t = G t)

end Specs.D13Unified.Ch20.Green
