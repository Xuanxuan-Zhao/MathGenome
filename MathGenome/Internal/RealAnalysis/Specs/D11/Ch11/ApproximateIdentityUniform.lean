import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionBound
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Uniform approximate identities, paper.tex:3744–3760. All integrals use
the full completed Euclidean Lebesgue measure. Kernels are arbitrary real or
complex L¹ functions, with no sign, symmetry, or normalization assumption.
Uniform convergence is stated by its usual entourage definition, including
every point of the indicated set (not an essential supremum).
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Specs.D11.Ch11.ApproximateIdentityUniform
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch11.ConvolutionBound (convolution_value)

def scaledKernel_type := ∀ (d : ℕ) [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → ℝ → Point d → 𝕜

/-- For positive t this is exactly t^(-d) φ(x/t). -/
def scaledKernel_value : scaledKernel_type := fun d _ _ _ φ t x =>
  (t ^ d)⁻¹ • φ (t⁻¹ • x)

def absolute_existence : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI := lebesgueSpace_value d
  ∀ (φ f : Point d → 𝕜), Measurable φ → Integrable φ (lebesgue_value d) →
    Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
    ∀ t : ℝ, 0 < t → ∀ x,
      Integrable (fun y => f y * scaledKernel_value d φ t (x-y)) (lebesgue_value d) ∧
      Integrable (fun y => scaledKernel_value d φ t y * f (x-y)) (lebesgue_value d)

def uniform_convergence : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI := lebesgueSpace_value d
  ∀ (φ f : Point d → 𝕜), Measurable φ → Integrable φ (lebesgue_value d) →
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) → UniformContinuous f →
    TendstoUniformly (fun t => convolution_value d f (scaledKernel_value d φ t))
      (fun x => (∫ z, φ z ∂lebesgue_value d) * f x) (𝓝[>] (0 : ℝ))

def compact_local_convergence : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI := lebesgueSpace_value d
  ∀ (φ f : Point d → 𝕜), Measurable φ → Integrable φ (lebesgue_value d) →
    Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
    ∀ U : Set (Point d), IsOpen U → ContinuousOn f U →
    ∀ K : Set (Point d), IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun t => convolution_value d f (scaledKernel_value d φ t))
        (fun x => (∫ z, φ z ∂lebesgue_value d) * f x) (𝓝[>] (0 : ℝ)) K

end Specs.D11.Ch11.ApproximateIdentityUniform
