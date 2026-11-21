import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.LusinRealLine

/-! Independent statement of paper.tex:2349–2361. Lebesgue measurability
uses the completed Borel structure and its trace on `E`. The almost-everywhere
assertion is an ambient completed-measure assertion conditional on membership
in `E`, so it includes all measurable domains without a finite-mass assumption. -/

open Set MeasureTheory Filter
open scoped Topology

namespace Specs.D11.Ch07.ContinuousAeSequence

def continuous_ae_sequence : Prop :=
  ∀ (E : Set ℝ), MeasurableSet[LusinRealLine.realLebesgueSpace] E →
    ∀ (f : E → ℝ),
      @Measurable E ℝ (LusinRealLine.realLebesgueSpace.comap Subtype.val) (borel ℝ) f →
      ∃ g : ℕ → ℝ → ℝ, (∀ n, Continuous (g n)) ∧
        ∀ᵐ x ∂(volume : Measure ℝ).completion,
          ∀ hx : x ∈ E, Tendsto (fun n => g n x) atTop (𝓝 (f ⟨x, hx⟩))

end Specs.D11.Ch07.ContinuousAeSequence
