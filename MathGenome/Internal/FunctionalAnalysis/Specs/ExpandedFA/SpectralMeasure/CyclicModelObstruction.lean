import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalPVM

noncomputable section
open MeasureTheory

namespace ExpandedFA.SpectralMeasure.ArbitraryCyclicSum.Spec

universe u

/-- A single bounded normal operator witnesses both obstructions in
`fa2:p2:cyclic-model`. It has a disjoint-union multiplication model,
but the measure in any such pointwise multiplication representation
fails to be sigma-finite, and its resolution admits no finite scalar
control measure. -/
def CyclicModelObstruction : Prop :=
  ∃ N : lp (fun _ : ℝ => ℂ) 2 →L[ℂ] lp (fun _ : ℝ => ℂ) 2,
    IsStarNormal N ∧ MultiplicationModel N ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℂ),
      Measurable g →
      ∀ (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] lp (fun _ : ℝ => ℂ) 2),
        (∀ f, M f =ᵐ[μ] fun x => g x * f x) →
        (∀ f, U (M f) = N (U f)) → ¬ SigmaFinite μ) ∧
    (∀ E : ProjectionValuedMeasure (spectrum ℂ N) (lp (fun _ : ℝ => ℂ) 2),
      NormalPVM.Spec.Resolves N E →
      ¬ ∃ μ : Measure (spectrum ℂ N), IsFiniteMeasure μ ∧
        ∀ B, MeasurableSet B → (E B = 0 ↔ μ B = 0))

end ExpandedFA.SpectralMeasure.ArbitraryCyclicSum.Spec
