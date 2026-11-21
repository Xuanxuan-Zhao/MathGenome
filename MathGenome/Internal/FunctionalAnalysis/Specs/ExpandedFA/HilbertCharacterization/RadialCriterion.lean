import Mathlib.Analysis.Normed.Module.Basic

namespace ExpandedFA.HilbertCharacterization

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Radial retraction onto the closed unit ball. -/
noncomputable def radialRetraction (x : X) : X := (max 1 ‖x‖)⁻¹ • x

/-- Every real minimizing coefficient for a nonzero equal-norm pair lies in [-1,1]. -/
def EqualNormMinimizerBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (x y : X), ‖x‖ = ‖y‖ → 0 < ‖x‖ → ∀ a : ℝ,
    (∀ t : ℝ, ‖x - a • y‖ ≤ ‖x - t • y‖) → |a| ≤ 1

/-- The full radial nonexpansion criterion, without dimension or completeness assumptions. -/
def RadialCriterionStatement : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X],
    (∀ x y : X, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x - y‖) ↔
      EqualNormMinimizerBound X

end ExpandedFA.HilbertCharacterization
