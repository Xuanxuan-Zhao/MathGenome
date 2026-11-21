import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! Independent statement of the representing-probability clause of
`fa2:p1:barycenters` (paper.tex:2161–2162).
The subtype `K` carries its original subspace topology and its Borel sigma
algebra. Convexity is real; tests are linear over the original scalar field.
There is no metrizability, separability, or local convexity assumption.
For a finite measure on a compact Hausdorff space, `Measure.Regular` gives
exactly the paper's Radon regularity, including compact inner regularity on
Borel sets. The empty compact set is allowed (its closed convex hull is empty).
-/

namespace ExpandedFA.P1.CompactHullMeasureBarycenters.Spec

open Set MeasureTheory

universe u v

/-- Every point of the compact closed convex hull has a regular probability
on the original compact set representing all continuous scalar-linear tests. -/
def RepresentingProbability : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E],
    (∀ x y : E, x ≠ y → ∃ ℓ : E →L[𝕜] 𝕜, ℓ x ≠ ℓ y) →
    ∀ K : Set E, IsCompact K → IsCompact (closure (convexHull ℝ K)) →
    ∀ b ∈ closure (convexHull ℝ K),
      letI : MeasurableSpace K := borel K
      ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
        ∀ ℓ : E →L[𝕜] 𝕜,
          Integrable (fun x : K => ℓ (x : E)) μ ∧
          ℓ b = ∫ x : K, ℓ (x : E) ∂μ

end ExpandedFA.P1.CompactHullMeasureBarycenters.Spec
