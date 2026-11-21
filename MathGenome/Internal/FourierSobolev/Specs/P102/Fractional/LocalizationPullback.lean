import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace P102.Fractional.Pullback
open P102.Fractional

/-- The raw chart pullback, with the stipulated zero value off the source. -/
def raw {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G H : Set (Domain d)} (F : G ≃ₜ H) (u : Domain d → 𝕜)
    (x : Domain d) : 𝕜 := by
  classical
  exact if hx : x ∈ G then u (F ⟨x, hx⟩) else 0

end P102.Fractional.Pullback

namespace Specs.P102.Fractional.LocalizationPullback
open _root_.P102.Fractional _root_.P102.Fractional.Pullback
universe u

/-- The full chart theorem. The finite constant is uniform in the scalar field,
open sets, chart and representative, and controls all three estimates. -/
def bilipschitzPullback : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ (K K' : ℝ≥0),
  ∃ C : ℝ≥0, ∀ {𝕜 : Type u} [RCLike 𝕜]
    (G H : Set (Domain d)), IsOpen G → IsOpen H →
    ∀ (F : G ≃ₜ H), LipschitzWith K F → LipschitzWith K' F.symm →
    (∀ u v : Domain d → 𝕜, u =ᵐ[domainMeasure H] v →
      raw F u =ᵐ[domainMeasure G] raw F v) ∧
    (∀ u : Domain d → 𝕜, MemLp u p (domainMeasure H) →
      energy G s p (raw F u) ≤ (C : ℝ≥0∞) * energy H s p u ∧
      (∫⁻ x, ‖raw F u x‖ₑ ^ p.toReal ∂domainMeasure G) ≤ (C : ℝ≥0∞) * (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure H)) ∧
    ∃ T : Space 𝕜 H s p →L[𝕜] Space 𝕜 G s p,
      ∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        raw F (firstProjection u) ∧ ‖T u‖ ≤ (C : ℝ) * ‖u‖


end Specs.P102.Fractional.LocalizationPullback
