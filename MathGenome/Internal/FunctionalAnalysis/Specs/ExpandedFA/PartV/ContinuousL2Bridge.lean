import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent statements for the continuous-to-L² clause of
`fa2:p5:l2-kernel`, paper.tex:21714–21716 and 21740–21744.
The inclusions are maps to ordinary a.e. quotients and need not be injective.
Radon regularity is precisely the explicit upstream source convention.
Product measurability uses the ordinary product of the Borel structures.
No countability, full-support, nonempty-space, or positive-mass assumptions occur. -/

open MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace ExpandedFA.PartV.ContinuousL2Bridge.Spec

/-- The inclusion has its usual representatives and finite-mass bound. -/
def InclusionCorrect : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ f : C(X, 𝕜), (ContinuousMap.toLp 2 μ 𝕜 f : X → 𝕜) =ᵐ[μ] f) ∧
      ‖ContinuousMap.toLp 2 μ 𝕜 (E := 𝕜)‖ ≤ Real.sqrt (μ.real Set.univ)

/-- Applies separately to X and Y, over either scalar field. -/
def ContinuousDensity : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ →
      DenseRange (ContinuousMap.toLp 2 μ 𝕜 (E := 𝕜))

/-- Continuous kernels are measurable for the product sigma algebra and define
ordinary product L² classes, with the finite-mass estimate. -/
def ProductL2 : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [RCLike 𝕜]
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)),
    @Measurable (X × Y) 𝕜 inferInstance (borel 𝕜) k ∧
      ∃ hk : MemLp (fun z => k z) 2 (μ.prod ν),
        ‖hk.toLp (fun z => k z)‖ ≤
          ‖k‖ * Real.sqrt (μ.real Set.univ) * Real.sqrt (ν.real Set.univ)

/-- The square commutes for every continuous input, including without full
support. Membership is established by ProductL2, not postulated globally. -/
def OperatorAgreement : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [RCLike 𝕜]
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)) (hk : MemLp (fun z => k z) 2 (μ.prod ν)),
    (L2KernelSpec.OperatorValue μ ν (hk.toLp (fun z => k z))).comp
        (ContinuousMap.toLp 2 ν 𝕜) =
      (ContinuousMap.toLp 2 μ 𝕜).comp (ContinuousKernel.Spec.KernelOperatorValue ν k)

/-- The canonical L² operator is the unique bounded extension of the
continuous formula through the quotient inclusion. Density makes this an
identity of operators on all of L², not just on continuous representatives. -/
def UniqueExtension : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [RCLike 𝕜]
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (_hν : ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon ν)
    (k : C(X × Y, 𝕜)) (hk : MemLp (fun z => k z) 2 (μ.prod ν)),
    ∀ T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ,
      (∀ f : C(Y, 𝕜), T (ContinuousMap.toLp 2 ν 𝕜 f) =
        ContinuousMap.toLp 2 μ 𝕜 (ContinuousKernel.Spec.KernelOperatorValue ν k f)) ↔
      T = L2KernelSpec.OperatorValue μ ν (hk.toLp (fun z => k z))

end ExpandedFA.PartV.ContinuousL2Bridge.Spec
