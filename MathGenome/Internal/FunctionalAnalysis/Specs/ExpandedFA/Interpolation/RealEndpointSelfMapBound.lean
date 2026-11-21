import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.EndpointInterpolation

/-! The finite-measure self-map specialization of
`fa2:p4:riesz-thorin` (paper.tex:18122–18127).

The two endpoint maps are compatible through the canonical inclusions into L¹.
The conclusion supplies the restriction of that same L¹ map to every intermediate
Lp, with its operator norm bounded by the exact endpoint norms. The exponent
`1 - 1 / p.toReal` equals `1 / p'` for the conjugate exponent. No positivity of
the measure is required, and only the two endpoint complexifications are used
in passing from complex to real scalars. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.Interpolation.RealEndpointSelfMapBoundSpec
open ExpandedFA.BanachGeometry.EndpointInterpolationSpec

/-- The sharp self-map estimate for any given compatible bounded endpoint maps.
All maps are scalar-linear over the displayed field. -/
def SelfMapBoundFor (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (S : Lp 𝕜 ∞ μ →L[𝕜] Lp 𝕜 ∞ μ),
    (∀ f, toL1 ∞ le_top (S f) = T (toL1 ∞ le_top f)) →
    ∀ (p : ℝ≥0∞) (hp : 1 < p) (_hpt : p < ∞) [Fact (1 ≤ p)],
      ∃ U : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
        (∀ f, toL1 p hp.le (U f) = T (toL1 p hp.le f)) ∧
        ‖U‖ ≤ ‖T‖ ^ (1 / p.toReal) * ‖S‖ ^ (1 - 1 / p.toReal)

/-- The complex-linear specialization of Riesz–Thorin. -/
def ComplexSelfMapBound : Prop := SelfMapBoundFor.{u} ℂ

/-- The real-linear version obtained by norm-preserving endpoint complexification. -/
def RealSelfMapBound : Prop := SelfMapBoundFor.{u} ℝ

end ExpandedFA.Interpolation.RealEndpointSelfMapBoundSpec
