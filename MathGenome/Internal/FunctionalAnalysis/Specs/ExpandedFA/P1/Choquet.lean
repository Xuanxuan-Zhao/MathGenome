import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-!
Independent statements of `fa2:p1:choquet`, paper.tex:5438–5445.
All closures and Borel sigma algebras use the original topology. Convexity
and extreme points are real, also for a complex ambient space. Barycenters
are tested against the original scalar-linear continuous dual. Regularity
is regularity of the Borel probability on its displayed compact domain.
No completeness, normability or ambient metrizability is assumed.
-/

namespace ExpandedFA.P1.Choquet.Spec

open Set MeasureTheory TopologicalSpace

universe u v

/-- The first measure lives on the compact closure of the extreme points. -/
def ClosureExtremeRepresentation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E] [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K → ∀ b ∈ K,
      let S := closure (C24FacesSpec.extremePoints K)
      letI : MeasurableSpace S := borel S
      ∃ μ : Measure S, IsProbabilityMeasure μ ∧ μ.Regular ∧
        ∀ ℓ : E →L[𝕜] 𝕜, Integrable (fun x : S => ℓ (x : E)) μ ∧
          ℓ b = ∫ x : S, ℓ (x : E) ∂μ

/-- For metrizable K, its extreme set is Borel and carries mass one.
Only K, not the whole ambient space, is required to be metrizable; the
extreme set is not required to be closed. -/
def ExtremeSupportedRepresentation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E] [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K → ∀ [MetrizableSpace K],
    ∀ b ∈ K,
      letI : MeasurableSpace K := borel K
      MeasurableSet {x : K | (x : E) ∈ C24FacesSpec.extremePoints K} ∧
      ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
        (∀ ℓ : E →L[𝕜] 𝕜, Integrable (fun x : K => ℓ (x : E)) μ ∧
          ℓ b = ∫ x : K, ℓ (x : E) ∂μ) ∧
        μ {x : K | (x : E) ∈ C24FacesSpec.extremePoints K} = 1

end ExpandedFA.P1.Choquet.Spec
