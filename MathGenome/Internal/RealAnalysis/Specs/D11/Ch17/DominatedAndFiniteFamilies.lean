import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls

/-!
Independent specifications for paper.tex:5246–5255. Families consist of
ordinary measurable real or complex representatives on an arbitrary positive
measure space. Domination is memberwise almost everywhere: no common null set
for the whole index type is required. The majorant is nonnegative and integrable.
A finite index type includes the empty type, and indexes any finite subset by
its subtype. Spatial truncation uses measurable sets of finite measure only.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch17.DominatedAndFiniteFamilies
open Specs.D11.Ch06.ScalarIntegral Specs.D11.Ch17.UniformControls

/-- Every measurable family with one integrable nonnegative majorant has both
uniform controls; individual integrability is part of the conclusion. -/
def dominated_controls : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜)
    (g : X → ℝ), (∀ i, Measurable (F i)) →
    scalarIntegrable_value μ g → (∀ᵐ x ∂μ, 0 ≤ g x) →
    (∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ g x) →
    uiSmall_value μ F ∧ spatialTails_value μ F

/-- Finite L1 families, including the empty family, have both controls. -/
def finite_controls : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Finite ι]
    (μ : Measure X) (F : ι → X → 𝕜), integrableFamily_value μ F →
    uiSmall_value μ F ∧ spatialTails_value μ F

end Specs.D11.Ch17.DominatedAndFiniteFamilies
