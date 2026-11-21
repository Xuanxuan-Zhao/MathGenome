import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction

/-! Independent statement of paper.tex:3690–3704. The measure and measurable
space are the full Carathéodory Lebesgue objects, in positive Euclidean
dimension. Native Lp is the ordinary scalar a.e. quotient identified by the
upstream quotient construction. The representative formula is required for
*every* MemLp representative. The translations are invertible linear
isometries, and continuity is asserted at every translation parameter. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.D11.Ch11.TranslationContinuity
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def translation_continuity : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    letI := lebesgueSpace_value d
    ∃ τ : Point d → (Lp 𝕜 p (lebesgue_value d) ≃ₗᵢ[𝕜] Lp 𝕜 p (lebesgue_value d)),
      (∀ (h : Point d) (f : Point d → 𝕜) (hf : MemLp f p (lebesgue_value d)),
        ∃ ht : MemLp (fun x => f (x - h)) p (lebesgue_value d),
          τ h (hf.toLp f) = ht.toLp (fun x => f (x - h))) ∧
      ∀ (f : Lp 𝕜 p (lebesgue_value d)) (k : Point d),
        Tendsto (fun h => ‖τ h f - τ k f‖) (𝓝 k) (𝓝 0)

end Specs.D11.Ch11.TranslationContinuity
