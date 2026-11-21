import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionBound
import Mathlib.Topology.Order.Basic

/-! Paper, Theorem D11.11.approximate_identity_lp. All functions are scalar,
the measure is completed Euclidean Lebesgue measure, and p is finite and at
least one. The extended norm agrees with the ordinary quotient norm on these
MemLp functions by the upstream quotient bridge. No condition on the sign,
symmetry, or integral of the kernel is imposed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Specs.D11.Ch11.ApproximateIdentityLp
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

def scaledKernel_type := ∀ (d : ℕ) {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → ℝ → Point d → 𝕜

def scaledKernel_value : scaledKernel_type := fun d _ _ φ t x =>
  (t ^ d)⁻¹ • φ (t⁻¹ • x)

def approximate_identity_lp : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    letI := lebesgueSpace_value d
    ∀ (φ f : Point d → 𝕜), Measurable φ → Measurable f →
      MemLp φ 1 (lebesgue_value d) → MemLp f p (lebesgue_value d) →
      (∀ t : ℝ, 0 < t → MemLp (scaledKernel_value d φ t) 1 (lebesgue_value d) ∧
        MemLp (Specs.D11.Ch11.ConvolutionBound.convolution_value d f
          (scaledKernel_value d φ t)) p (lebesgue_value d)) ∧
      Tendsto (fun t : ℝ => eLpNorm
        (Specs.D11.Ch11.ConvolutionBound.convolution_value d f (scaledKernel_value d φ t) -
          (∫ z, φ z ∂lebesgue_value d) • f) p (lebesgue_value d))
        (𝓝[>] (0 : ℝ)) (𝓝 0)

end Specs.D11.Ch11.ApproximateIdentityLp
