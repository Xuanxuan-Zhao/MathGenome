import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.Pushforward
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral

/-!
Independent statement of nonnegative transport, paper.tex:2998–3009.

The two spaces carry their specified sigma-algebras. The integral is the
shared supremum over finite nonnegative simple minorants, and pushforward
is the shared construction along a measurable map. Both functions are
measurable for the displayed structures. Integral values may be infinite;
there is no finiteness, sigma-finiteness, completeness or nonemptiness premise.
-/

open MeasureTheory
open scoped ENNReal

universe u v

namespace Specs.D11.Ch09.TransportNonnegative

def transport_nonnegative : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (h : Y → ℝ≥0∞),
    Measurable h →
    Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value
        (Specs.D11.Ch09.Pushforward.pushforward_value u hu μ) h =
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ (h ∘ u)

end Specs.D11.Ch09.TransportNonnegative
