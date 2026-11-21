import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionBound
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition
import Mathlib.Topology.Algebra.Support

/-! Values at Lebesgue points, paper.tex:3761–3782. The representative is
finite-valued and measurable for the completed Euclidean Lebesgue space.
The exponent includes infinity. Kernels can be real or complex and need
neither positivity nor symmetry. All convolution integrals are absolute. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Specs.D11.Ch11.ApproximateIdentityLebesguePoints
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch13.AveragesMaximalDefinition

def dilate_type := ∀ (n : ℕ) [NeZero n] {𝕜 : Type} [RCLike 𝕜],
  (Point n → 𝕜) → ℝ → Point n → 𝕜

def dilate_value : dilate_type := fun n _ _ _ φ t y =>
  (t ^ n)⁻¹ • φ (t⁻¹ • y)

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace_value n

/-- Local integrability, all-point absolute existence, and all three
pointwise convergence assertions, for the same fixed representative. -/
def approximate_identity : Prop :=
  ∀ (n : ℕ) [NeZero n] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞), 1 ≤ p →
    ∀ (f φ : Point n → 𝕜), Measurable f → MemLp f p (lebesgue_value n) →
    Measurable φ → HasCompactSupport φ → (∃ M : ℝ, ∀ y, ‖φ y‖ ≤ M) →
    (∫ y, φ y ∂lebesgue_value n) = 1 →
    ∃ hf : locallyIntegrable_value f,
      (∀ t : ℝ, 0 < t → ∀ x : Point n,
        Integrable (fun y => f y * dilate_value n φ t (x-y)) (lebesgue_value n)) ∧
      (∀ x, lebesguePoint_value f hf x →
        Tendsto (fun t => Specs.D11.Ch11.ConvolutionBound.convolution_value n
          f (dilate_value n φ t) x) (𝓝[>] (0 : ℝ)) (𝓝 (f x))) ∧
      (∀ᵐ x ∂lebesgue_value n,
        Tendsto (fun t => Specs.D11.Ch11.ConvolutionBound.convolution_value n
          f (dilate_value n φ t) x) (𝓝[>] (0 : ℝ)) (𝓝 (f x))) ∧
      (∀ x, ContinuousAt f x →
        Tendsto (fun t => Specs.D11.Ch11.ConvolutionBound.convolution_value n
          f (dilate_value n φ t) x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)))

end Specs.D11.Ch11.ApproximateIdentityLebesguePoints
