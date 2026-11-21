import MathGenome.Internal.RealAnalysis.D11.Ch09.Pushforward
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportNonnegative
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
Nonnegative transport (paper.tex:2998–3009), using the canonical positive
measure, pushforward and nonnegative integral from the earlier chapters.
The proved bridge to the library lower integral allows reuse of
`lintegral_map`, whose two measurability hypotheses are exactly those here.
It imposes no size hypothesis on the measure and admits infinite integrals.
-/

open MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch09.TransportNonnegative

/-- Transport of a measurable extended nonnegative function along a
measurable map, for an arbitrary positive measure. -/
theorem transport_nonnegative {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (h : Y → ℝ≥0∞)
    (hh : Measurable h) :
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral
        (D11.Ch09.Pushforward.pushforward u hu μ) h =
      D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ (h ∘ u) := by
  simp only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  exact lintegral_map hh hu

end D11.Ch09.TransportNonnegative
