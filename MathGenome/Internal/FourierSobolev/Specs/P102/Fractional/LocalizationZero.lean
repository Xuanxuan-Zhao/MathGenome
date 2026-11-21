import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space

/-! Independent quantitative zero extension across an artificial edge. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace Specs.P102.Fractional.LocalizationZero
open _root_.P102.Fractional
universe u

/-- The constant is finite, uniform over scalar fields, open domains and radii.
The original energy has coefficient exactly one. Separation is only from H \ G.
The second clause uses the same constant for the canonical sum norm. -/
def zeroExtensionAway : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∃ C : ℝ≥0, ∀ {𝕜 : Type u} [RCLike 𝕜]
    (G H : Set (Domain d)), IsOpen G → IsOpen H → G ⊆ H →
    ∀ (δ : ℝ), 0 < δ →
    (∀ u : Domain d → 𝕜, MemLp u p (domainMeasure G) →
      (∀ᵐ x ∂domainMeasure G, u x ≠ 0 → ∀ y ∈ H \ G, δ ≤ dist x y) →
      energy H s p (G.indicator u) ≤ energy G s p u +
        (C : ℝ≥0∞) * ENNReal.ofReal (δ ^ (-s * p.toReal)) *
          (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G)) ∧
    (∀ u : Space 𝕜 G s p,
      (∀ᵐ x ∂domainMeasure G, firstProjection u x ≠ 0 →
        ∀ y ∈ H \ G, δ ≤ dist x y) →
      ∃ v : Space 𝕜 H s p,
        (firstProjection v : Domain d → 𝕜) =ᵐ[domainMeasure H]
          G.indicator (firstProjection u) ∧
        ‖v‖ ≤ (2 + (C : ℝ) * δ ^ (-s * p.toReal)) * ‖u‖)

end Specs.P102.Fractional.LocalizationZero
