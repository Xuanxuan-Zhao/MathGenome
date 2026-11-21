import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.Pushforward
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-!
Independent statements for scalar transport, paper.tex:3010–3020.
The specified measurable structures are retained. Integrability includes
actual measurability and finiteness of the nonnegative integral of the norm.
`RCLike` covers both real and complex scalars. No size or completeness
assumption is imposed on the positive measure. Scalar integral equality is
asserted only with integrability proofs on both spaces.
-/

open MeasureTheory

universe u v

namespace Specs.D11.Ch09.TransportIntegrable

open Specs.D11.Ch09.Pushforward
open Specs.D11.Ch06.ScalarIntegral

def transport_integrable_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (h : Y → 𝕜),
    Measurable h →
    (scalarIntegrable_value (pushforward_value u hu μ) h ↔
      scalarIntegrable_value μ (h ∘ u))

/-- Integrability of the composition and equality of the finite scalar
integrals, given integrability on the pushforward space. The equivalence
above also covers starting with integrability of the composition. -/
def transport_integral : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (h : Y → 𝕜)
    (hh : scalarIntegrable_value (pushforward_value u hu μ) h),
    ∃ hc : scalarIntegrable_value μ (h ∘ u),
      scalarIntegral_value (pushforward_value u hu μ) h hh =
        scalarIntegral_value μ (h ∘ u) hc

end Specs.D11.Ch09.TransportIntegrable
