import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! The endpoint corollary at paper.tex:5741–5747. Native `Lp` is the
ordinary measurable a.e. quotient, through the upstream representative-preserving
linear isometries in `QuotientConstruction`. No local-null quotient is used.
The equivalence below is scalar-linear also over ℂ; its formula has no conjugation.
-/
open MeasureTheory
open scoped ENNReal
universe u
namespace Specs.D11.Ch20.LoneDualSigmafinite

/-- The integral pairing is a linear isometric bijection onto the entire
continuous scalar dual, for every sigma-finite positive measure. Explicit
integrability prevents relying on a totalized integral outside its domain. -/
def lone_dual_sigmafinite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ],
    ∃ T : Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] (Lp 𝕜 1 μ →L[𝕜] 𝕜),
      ∀ (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ),
        Integrable (fun x => f x * g x) μ ∧
          T g f = ∫ x, f x * g x ∂μ

end Specs.D11.Ch20.LoneDualSigmafinite
