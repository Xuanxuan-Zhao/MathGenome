import MathGenome.Internal.FourierSobolev.Specs.P102.U2.WeakNorms
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Interpolation.Marcinkiewicz

/-! Independent statement of paper.tex, Theorem p102:AN-06-C04-R02.
We reuse the library's common sum domain and sublinearity on a.e. classes.
`SublinearOn` includes measurable outputs, congruence under input a.e. equality,
subadditivity of the modulus and absolute homogeneity on that common domain.
The endpoint sizes below are exactly the project's distribution-based weak sizes.
Nonnegative real constants include zero and are always finite. -/

open MeasureTheory
open scoped ENNReal NNReal

universe u v w

namespace P102.U2.MarcinkiewiczSpec

open ExpandedFA.Interpolation.MarcinkiewiczSpec

/-- A weak endpoint bound for the same operator, with essential supremum at infinity. -/
def WeakEndpointBound {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) (r : ℝ≥0∞)
    (M : ℝ≥0) (T : (X → 𝕜) → Y → 𝕜) : Prop :=
  ∀ f, MemLp f r μ →
    (if r = ∞ then weakSizeInfinity ν (T f) else weakSize ν r.toReal (T f)) ≤
      (M : ℝ≥0∞) * eLpNorm f r μ

/-- The constant depends only on the exponents and endpoint bounds. This
statement holds on arbitrary measure spaces, and hence on the sigma-finite
spaces in the source. The explicit sum-domain conclusion makes evaluation of
`T f` legitimate. Exponents use ENNReal to include the infinity upper endpoint;
the strict inequalities force the lower and intermediate exponents to be finite. -/
def DiagonalInterpolation : Prop :=
  ∀ (p₀ p₁ p : ℝ≥0∞) (M₀ M₁ : ℝ≥0), 1 ≤ p₀ → p₀ < p → p < p₁ →
  ∃ C : ℝ≥0,
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure X) (ν : Measure Y) (T : (X → 𝕜) → Y → 𝕜),
    SublinearOn μ ν (sumDomain μ p₀ p₁) T →
    WeakEndpointBound μ ν p₀ M₀ T →
    WeakEndpointBound μ ν p₁ M₁ T →
    ∀ f, MemLp f p μ →
      sumDomain μ p₀ p₁ f ∧ MemLp (T f) p ν ∧
        eLpNorm (T f) p ν ≤ (C : ℝ≥0∞) * eLpNorm f p μ

end P102.U2.MarcinkiewiczSpec
