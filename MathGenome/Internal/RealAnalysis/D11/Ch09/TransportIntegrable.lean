import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportNonnegative
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral

/-! Scalar transport on arbitrary positive measure spaces
(paper.tex:3010–3020). The integrability equivalence follows by applying
nonnegative transport to the norm. The scalar equality reuses the library
map-integral theorem, after establishing the source integrability on both
spaces. The public scalar integrals require these proofs. -/

open MeasureTheory
open scoped ENNReal

universe u v

namespace D11.Ch09.TransportIntegrable

open D11.Ch09.Pushforward
open D11.Ch06.ScalarIntegral

theorem transport_integrable_iff {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (h : Y → 𝕜)
    (hh : Measurable h) :
    scalarIntegrable (pushforward u hu μ) h ↔ scalarIntegrable μ (h ∘ u) := by
  have hnorm := D11.Ch09.TransportNonnegative.transport_nonnegative
    u hu μ (fun y => ENNReal.ofReal ‖h y‖) hh.norm.ennreal_ofReal
  change (Measurable h ∧ _ < ∞) ↔ (Measurable (h ∘ u) ∧ _ < ∞)
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral (pushforward u hu μ)
      (fun y => ENNReal.ofReal ‖h y‖) =
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ
      (fun x => ENNReal.ofReal ‖(h ∘ u) x‖) at hnorm
  rw [hnorm]
  exact and_congr (iff_of_true hh (hh.comp hu)) Iff.rfl

theorem transport_integral {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (h : Y → 𝕜)
    (hh : scalarIntegrable (pushforward u hu μ) h) :
    ∃ hc : scalarIntegrable μ (h ∘ u),
      scalarIntegral (pushforward u hu μ) h hh = scalarIntegral μ (h ∘ u) hc := by
  refine ⟨(transport_integrable_iff u hu μ h hh.1).mp hh, ?_⟩
  change (∫ y, h y ∂Measure.map u μ) = ∫ x, (h ∘ u) x ∂μ
  exact integral_map hu.aemeasurable hh.1.aestronglyMeasurable

end D11.Ch09.TransportIntegrable
