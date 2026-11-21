import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ConvolutionEndpointBounds

/-! Young's full inequality, paper.tex:17287–17305. All dimensions, both scalar
fields, all endpoints, and arbitrary a.e. strongly measurable representatives
are included. The integral uses the already fixed scalar convolution. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.Distributions.YoungConvolutionInequalitySpec
open ConvolutionEndpointBoundsSpec

def Young : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p q r : ℝ≥0∞),
    1 ≤ p → 1 ≤ q → 1 ≤ r → 1 + r⁻¹ = p⁻¹ + q⁻¹ →
    ∀ (f g : (Fin d → ℝ) → 𝕜), MemLp f p volume → MemLp g q volume →
    (∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))) ∧
    AEStronglyMeasurable (ConvolutionValue f g) volume ∧
    MemLp (ConvolutionValue f g) r volume ∧
    eLpNorm (ConvolutionValue f g) r volume ≤ eLpNorm f p volume * eLpNorm g q volume

def YoungQuotientBound : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p q r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)],
    1 + r⁻¹ = p⁻¹ + q⁻¹ →
    ∀ (f : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) (g : Lp 𝕜 q volume),
    ∃! h : Lp 𝕜 r volume,
      (h : (Fin d → ℝ) → 𝕜) =ᵐ[volume] ConvolutionValue f g ∧ ‖h‖ ≤ ‖f‖ * ‖g‖

end ExpandedFA.Distributions.YoungConvolutionInequalitySpec
