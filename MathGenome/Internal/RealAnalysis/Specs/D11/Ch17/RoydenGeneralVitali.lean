import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls

/-!
The general positive-measure-space variant of paper.tex:5282–5293.
The limit is explicitly integrable. Small-set control and finite-measure
spatial tails are the shared source predicates; no uniform norm bound,
atomlessness, completeness, or sigma-finiteness is assumed. Scalars include
both real and complex functions. The first conclusion is L1 convergence,
expressed by the nonnegative absolute integral; the second uses the shared
integral with its integrability proof argument.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch17.RoydenGeneralVitali
open Specs.D11.Ch17.UniformControls Specs.D11.Ch06.ScalarIntegral

def general_vitali : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ℕ → X → 𝕜) (f : X → 𝕜)
    (hF : ∀ n, scalarIntegrable_value μ (F n)) (hf : scalarIntegrable_value μ f),
    uiSmall_value μ F → spatialTails_value μ F →
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    Tendsto (fun n => absoluteIntegral_value μ (fun x => F n x - f x) univ)
      atTop (𝓝 0) ∧
    Tendsto (fun n => scalarIntegral_value μ (F n) (hF n))
      atTop (𝓝 (scalarIntegral_value μ f hf))

end Specs.D11.Ch17.RoydenGeneralVitali
