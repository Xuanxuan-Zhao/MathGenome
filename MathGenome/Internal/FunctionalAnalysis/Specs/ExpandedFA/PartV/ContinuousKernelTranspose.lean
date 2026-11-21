import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! The transpose assertion of `fa2:p5:continuous-kernel` (paper.tex,
21677–21685). Scalar measure integration uses multiplication, and the
operator is the canonical operator of the accepted kernel interface.
The last clause identifies the actual Radon representing measure uniquely,
as the native vector measure with density h. All spaces may be empty. -/

open MeasureTheory
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
universe u v w
namespace ExpandedFA.PartV.ContinuousKernelTranspose.Spec

def FullTheorem : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν], PositiveRadon ν →
    ∀ (k : C(X × Y, 𝕜)) (η : VectorMeasure X 𝕜), FiniteScalarRadon η →
    ‖ContinuousKernel.Spec.KernelOperatorValue ν k‖ ≤ ν.real Set.univ * ‖k‖ ∧
    IsCompactOperator (ContinuousKernel.Spec.KernelOperatorValue ν k) ∧
    ∃ h : C(Y, 𝕜),
      (∀ y, h y = scalarIntegral η (fun x => k (x, y))) ∧
      FiniteScalarRadon (ν.withDensityᵥ (h : Y → 𝕜)) ∧
      (∀ u : C(Y, 𝕜),
        Integrable (ContinuousKernel.Spec.KernelOperatorValue ν k u) η.variation ∧
        Integrable (fun y => u y * h y) ν ∧
        scalarIntegral η (ContinuousKernel.Spec.KernelOperatorValue ν k u) =
          ∫ y, u y * h y ∂ν) ∧
      (∀ u : C(Y, 𝕜),
        scalarIntegral (ν.withDensityᵥ (h : Y → 𝕜)) u = ∫ y, u y * h y ∂ν) ∧
      (∀ ρ : VectorMeasure Y 𝕜, FiniteScalarRadon ρ →
        ((∀ u : C(Y, 𝕜), scalarIntegral ρ u =
            scalarIntegral η (ContinuousKernel.Spec.KernelOperatorValue ν k u)) ↔
          ρ = ν.withDensityᵥ (h : Y → 𝕜)))

end ExpandedFA.PartV.ContinuousKernelTranspose.Spec
