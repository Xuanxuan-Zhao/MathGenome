import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing

/-! The sigma-finite conclusion of paper.tex:5708–5718. Native Lp is the
ordinary measurable a.e. quotient fixed by the upstream quotient bridge.
The product pairing is bilinear over both real and complex scalars. -/
open MeasureTheory
open scoped ENNReal
universe u
namespace Specs.D11.Ch20.LpDualSigmafiniteLocal

def sigmaFinite_duality : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ → ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃! g : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        ℓ f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖ℓ‖

end Specs.D11.Ch20.LpDualSigmafiniteLocal
