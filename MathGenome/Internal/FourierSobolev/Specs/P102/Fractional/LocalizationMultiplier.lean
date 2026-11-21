import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace Specs.P102.Fractional.LocalizationMultiplier
open _root_.P102.Fractional
universe u

/-- Bounded Lipschitz scalar multiplication, for either real or complex scalars.
The same finite constant bounds the energy comparison and the sum-norm operator.
The hypotheses on φ concern only G. No smoothness of G or φ is required. -/
def boundedMultiplier : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ (M L : ℝ≥0),
  ∃ C : ℝ≥0, ∀ {𝕜 : Type u} [RCLike 𝕜]
    (G : Set (Domain d)), IsOpen G → ∀ (φ : Domain d → 𝕜),
    LipschitzOnWith L φ G → (∀ x ∈ G, ‖φ x‖ ≤ M) →
    (∀ u : Domain d → 𝕜, MemLp u p (domainMeasure G) →
      energy G s p (fun x => φ x * u x) ≤
        (C : ℝ≥0∞) * (energy G s p u + (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G))) ∧
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 G s p,
      ∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        (fun x => φ x * firstProjection u x) ∧ ‖T u‖ ≤ (C : ℝ) * ‖u‖

end Specs.P102.Fractional.LocalizationMultiplier
