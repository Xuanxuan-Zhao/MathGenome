import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
Independent statements for the metrizable clause of `fa2:p1:choquet`,
paper.tex:5438–5489. The compact set has its original subspace topology;
only this subtype, rather than the whole locally convex space, is metrizable.
The sigma algebra is its Borel sigma algebra. Extreme points are the shared
manuscript definition, with real proper convex combinations.

`Measure.Regular` for a finite Borel measure on a compact Hausdorff space
records the required regularity. The mass-one condition concerns the Borel
extreme-point set itself; it asserts no closedness of that set.
-/

namespace ExpandedFA.P1.ChoquetMetrizable.Spec

open Set MeasureTheory TopologicalSpace

universe u

/-- Borel measurability on `K`, including the empty compact convex set.
The proof in fact needs no local convexity. -/
def ExtremeSetBorel : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (K : Set E), IsCompact K → Convex ℝ K → ∀ [MetrizableSpace K],
    letI : MeasurableSpace K := borel K
    MeasurableSet {x : K | (x : E) ∈ C24FacesSpec.extremePoints K}

/-- Maximizing a continuous real objective over all measures with the prescribed
linear moments. This is a proof ingredient and requires only compactness. -/
def MaximizingRepresentation : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (K : Set E), IsCompact K → ∀ b ∈ K, ∀ q : C(K, ℝ),
      letI : MeasurableSpace K := borel K
      ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
        (∀ ℓ : E →L[ℝ] ℝ, Integrable (fun x : K => ℓ (x : E)) μ ∧
          ℓ b = ∫ x : K, ℓ (x : E) ∂μ) ∧
        ∀ ν : Measure K, IsProbabilityMeasure ν →
          (∀ ℓ : E →L[ℝ] ℝ, ℓ b = ∫ x : K, ℓ (x : E) ∂ν) →
          (∫ x : K, q x ∂ν) ≤ ∫ x : K, q x ∂μ

/-- The full metrizable Choquet conclusion, for every point of every nonempty
compact metrizable convex set in a Hausdorff real LCS. -/
def ExtremeSupportedRepresentation : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K → ∀ [MetrizableSpace K],
    ∀ b ∈ K,
      letI : MeasurableSpace K := borel K
      ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
        (∀ ℓ : E →L[ℝ] ℝ, Integrable (fun x : K => ℓ (x : E)) μ ∧
          ℓ b = ∫ x : K, ℓ (x : E) ∂μ) ∧
        μ {x : K | (x : E) ∈ C24FacesSpec.extremePoints K} = 1

end ExpandedFA.P1.ChoquetMetrizable.Spec
