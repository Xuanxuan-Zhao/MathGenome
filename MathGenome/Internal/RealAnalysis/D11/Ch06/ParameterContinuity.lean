import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ParameterContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral

/-! Continuity of parameter integrals, paper.tex:2043–2057.
The Bochner continuity theorem applies to section measurability and a common
integrable bound on any positive measure space. The scalar bridge supplies
actual measurability and finite absolute integrability before integral evaluation.
The interval subtype retains relative continuity at both endpoints. -/

open Set Filter MeasureTheory
open scoped Topology
universe u
noncomputable section
namespace D11.Ch06.ParameterContinuity
open D11.Ch06.ScalarIntegral

theorem parameter_continuity_at :
    Specs.D11.Ch06.ParameterContinuity.parameter_continuity_at := by
  intro X 𝕜 _ _ _ _ μ a b _hab F g hF hg _hg0 hbound t₀ hcont
  change ContinuousAt (fun t => ∫ x, F x t ∂μ) t₀
  exact continuousAt_of_dominated
    (Eventually.of_forall (fun t =>
      ((scalarIntegrable_iff μ (fun x => F x t)).mp (hF t)).2.aestronglyMeasurable))
    (Eventually.of_forall (fun t => ae_of_all μ (fun x => hbound x t)))
    ((scalarIntegrable_iff μ g).mp hg).2
    (ae_of_all μ hcont)

theorem parameter_continuity :
    Specs.D11.Ch06.ParameterContinuity.parameter_continuity := by
  intro X 𝕜 _ _ _ _ μ a b hab F g hF hg hg0 hbound hcont
  exact continuous_iff_continuousAt.mpr (fun t =>
    parameter_continuity_at μ a b hab F g hF hg hg0 hbound t
      (fun x => (hcont x).continuousAt))

end D11.Ch06.ParameterContinuity
