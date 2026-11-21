import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Green

/-! Independent statement of the bounded construction in the proof of
`d13:20:hartman-grobman`. The state has any fixed finite-dimensional real norm.
The nonlinear term is a bounded continuous map with the stated C¹ and Lipschitz
regularity. Its argument (the linear orbit plus a bounded correction) is allowed
to be unbounded. The resulting equivalence is only a bijection here. -/
noncomputable section
open scoped BoundedContinuousFunction NNReal

namespace D13Unified.Ch20.BoundedNonlinearConjugacy
open D13Unified.Ch07 Specs.D13Unified.Ch07.MatrixExponential

variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The fixed point equation, with its actual bounded continuous forcing.
The existential packaging avoids imposing boundedness on the linear orbit. -/
def IsCorrection (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) : Prop :=
  ∃ g : ℝ →ᵇ E,
    (∀ t, g t = r (matrixOperatorEquiv b (exponentialValue A t) x + z t)) ∧
    ∀ t, z t = Green.greenValue b A g t

end D13Unified.Ch20.BoundedNonlinearConjugacy

namespace Specs.D13Unified.Ch20.BoundedNonlinearConjugacy
open _root_.D13Unified.Ch07 _root_.D13Unified.Ch20
open _root_.D13Unified.Ch20.BoundedNonlinearConjugacy
open Specs.D13Unified.Ch07.MatrixExponential
open Specs.D13Unified.Ch20.HyperbolicSplitting
universe u v

/-- Unique bounded correction, its C¹ equation and uniform bound. -/
def fixedPointsExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ (K α : ℝ), Green.DichotomyBounds b A K α →
    ∀ (r : E →ᵇ E) (L : ℝ≥0),
      ContDiff ℝ 1 (r : E → E) → r 0 = 0 → LipschitzWith L r →
      (2 * K / α) * (L : ℝ) < 1 →
      ∃ z : E → (ℝ →ᵇ E), ∀ x,
        IsCorrection b A r x (z x) ∧
        (∀ w, IsCorrection b A r x w → w = z x) ∧
        ‖z x‖ ≤ (2 * K / α) * ‖r‖ ∧
        ContDiff ℝ 1 (z x : ℝ → E) ∧
        ∀ t, HasDerivAt (z x : ℝ → E)
          (matrixOperatorEquiv b A (z x t) +
            r (matrixOperatorEquiv b (exponentialValue A t) x + z x t)) t

/-- The bijection and its explicit inverse for any complete solution flow.
Only the initial values and the whole-line differential equation are needed
of the flow: this stronger formulation applies in particular to the complete
continuous flow constructed by the cutoff theorem. -/
def conjugacyExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ (K α : ℝ), Green.DichotomyBounds b A K α →
    ∀ (r : E →ᵇ E) (L : ℝ≥0),
      ContDiff ℝ 1 (r : E → E) → r 0 = 0 → LipschitzWith L r →
      (2 * K / α) * (L : ℝ) < 1 →
    ∀ φ : ℝ → E → E, (∀ y, φ 0 y = y) →
      (∀ y t, HasDerivAt (fun s => φ s y)
        (matrixOperatorEquiv b A (φ t y) + r (φ t y)) t) →
      ∃ (z : E → (ℝ →ᵇ E)) (H : E ≃ E),
        (∀ x, IsCorrection b A r x (z x) ∧
          (∀ w, IsCorrection b A r x w → w = z x)) ∧
        (∀ x, ‖z x‖ ≤ (2 * K / α) * ‖r‖) ∧
        (∀ x, H x = x + z x 0) ∧ H 0 = 0 ∧
        (∀ x τ t, z (matrixOperatorEquiv b (exponentialValue A τ) x) t = z x (t+τ)) ∧
        (∀ t x, H (matrixOperatorEquiv b (exponentialValue A t) x) = φ t (H x)) ∧
        (∀ y, ∃ g : ℝ →ᵇ E,
          (∀ t, g t = r (φ t y)) ∧ H.symm y = y - Green.greenValue b A g 0)

end Specs.D13Unified.Ch20.BoundedNonlinearConjugacy
