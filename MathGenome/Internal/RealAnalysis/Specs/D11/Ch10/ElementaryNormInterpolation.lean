import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction

/-!
Elementary interpolation, paper.tex:3460–3474.

Exponents are extended nonnegative reals, so `1 ≤ p`, `p < q`, `q < r`
encode the entire displayed range, including `r = ∞`. The reciprocal identity
is in ENNReal, where `∞⁻¹ = 0`: `ofReal θ / p` is precisely θ/p.
The norms are the shared integral/ordinary essential-supremum `sourceNorm`.
The function is an ordinary measurable scalar representative. The conclusion
also records membership in the intermediate raw space; the upstream quotient
construction identifies its norm with that of the ordinary a.e. class.
No completeness, finiteness, or sigma-finiteness of the measure is assumed.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.ElementaryNormInterpolation

open Specs.D11.Ch10.QuotientConstruction

def elementary_norm_interpolation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q r : ℝ≥0∞) (θ : ℝ) (f : X → 𝕜),
    1 ≤ p → p < q → q < r → 0 < θ → θ < 1 →
    q⁻¹ = ENNReal.ofReal θ / p + ENNReal.ofReal (1 - θ) / r →
    Measurable f → sourceNorm μ p f < ∞ → sourceNorm μ r f < ∞ →
    f ∈ rawSpace μ q ∧
      sourceNorm μ q f ≤ sourceNorm μ p f ^ θ * sourceNorm μ r f ^ (1 - θ)

end Specs.D11.Ch10.ElementaryNormInterpolation
