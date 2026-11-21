import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition

/-! paper.tex:4394–4427. One exceptional set for the fixed finite-valued
real or complex representative. The ball families are arbitrary filtered
families; positive radii tending to zero are equivalent to positive ball
diameters tending to zero in Euclidean dimension at least one. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
universe u
namespace Specs.D11.Ch13.LebesgueDifferentiation
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch13.AveragesMaximalDefinition

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace_value n

/-- Full representative-level differentiation, with the same exceptional set
for centered absolute averages and every containing-ball family. -/
def lebesgue_differentiation : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable_value f),
    ∃ N : Set (Point n), MeasurableSet N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N, lebesguePoint_value f hf x ∧
        Tendsto (fun r => average_value f hf r x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) ∧
        ∀ {ι : Type u} {l : Filter ι} (z : ι → Point n) (r : ι → ℝ),
          Tendsto (fun i => Metric.diam (Metric.ball (z i) (r i))) l (𝓝 (0 : ℝ)) →
          (∀ᶠ i in l, x ∈ Metric.ball (z i) (r i)) →
          Tendsto (fun i => ((lebesgue_value n) (Metric.ball (z i) (r i))).toReal⁻¹ *
              ∫ y in Metric.ball (z i) (r i), ‖f y - f x‖ ∂(lebesgue_value n))
            l (𝓝 0) ∧
          Tendsto (fun i => average_value f hf (r i) (z i)) l (𝓝 (f x))
end Specs.D11.Ch13.LebesgueDifferentiation
