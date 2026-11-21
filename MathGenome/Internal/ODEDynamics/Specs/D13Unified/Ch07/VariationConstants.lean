import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.EvolutionMatrix
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! Independent statement of paper.tex, Theorem d13:07:variation.
The representative of the solution is specified by the evolution-matrix
formula. Its domain is the actual interval, and uniqueness is equality there.
All integrals are oriented real-time Bochner integrals, over either scalar field.
-/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace Specs.D13Unified.Ch07.VariationConstants
open _root_.D13Unified _root_.D13Unified.Ch07.EvolutionMatrix

/-- Whole-interval existence, classical regularity, initial data, uniqueness,
and both variation-of-constants formulas, for every fundamental matrix. -/
def VariationOfConstants : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂)
    (s : ℝ) (x₀ : Fin n → 𝕂),
    s ∈ I.carrier → ContinuousOn A I.carrier → ContinuousOn b I.carrier →
    let x : ℝ → Fin n → 𝕂 := fun t =>
      U I A t s *ᵥ x₀ + ∫ r in s..t, U I A t r *ᵥ b r
    ContinuousOn x I.carrier ∧ x s = x₀ ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt x (A t *ᵥ x t + b t) I.carrier t) ∧
      ContDiffOn ℝ 1 x I.carrier ∧
      (∀ y : ℝ → Fin n → 𝕂, ContinuousOn y I.carrier → y s = x₀ →
        (∀ t ∈ I.carrier, HasDerivWithinAt y (A t *ᵥ y t + b t) I.carrier t) →
        EqOn y x I.carrier) ∧
      ∀ X : ℝ → Matrix (Fin n) (Fin n) 𝕂, IsFundamentalMatrixOn I A X →
        ∀ t ∈ I.carrier, x t = X t *ᵥ
          ((X s)⁻¹ *ᵥ x₀ + ∫ r in s..t, (X r)⁻¹ *ᵥ b r)

end Specs.D13Unified.Ch07.VariationConstants
