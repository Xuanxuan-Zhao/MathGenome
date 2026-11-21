import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LpDualSigmafiniteLocal
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions

/-! Independent statement of paper.tex:5721–5723. The measure is arbitrary,
and native Lp is the ordinary a.e. quotient. The indicator is formed in
the same Lp space, using its measurable-set cutoff map. -/
open Set MeasureTheory
open scoped ENNReal
universe u
namespace Specs.D11.Ch20.FunctionalVisibleSigmafiniteSupport

def functional_visible_sigmafinite_support : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃ F : Set X, MeasurableSet F ∧ SigmaFinite (μ.restrict F) ∧
      ∀ f : Lp 𝕜 p μ,
        ∃ fF : Lp 𝕜 p μ, (fF : X → 𝕜) =ᵐ[μ] F.indicator (f : X → 𝕜) ∧
          ℓ f = ℓ fF

end Specs.D11.Ch20.FunctionalVisibleSigmafiniteSupport
