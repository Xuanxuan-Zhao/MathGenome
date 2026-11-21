import MathGenome.Internal.FourierSobolev.Specs.P102.U4.TestSpace

/-! The local order criterion, paper.tex:1300–1310.
The seminorms are the canonical coordinate multi-index seminorms, as identified
in `TestSpace`. Constants and natural-number orders are chosen separately for
each ambient compact subset of the open set. No nonemptiness is required.
-/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions

namespace P102.U4.Expected

def LocalOrder : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T : TestSpace 𝕜 Ω →ₗ[𝕜] 𝕜),
    Continuous T ↔
      ∀ (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω),
        ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ φ : FixedSupport d 𝕜 K,
          ‖T (stageInclusion 𝕜 hK φ)‖ ≤ C * coordinateSupSeminorm 𝕜 K m φ

end P102.U4.Expected
