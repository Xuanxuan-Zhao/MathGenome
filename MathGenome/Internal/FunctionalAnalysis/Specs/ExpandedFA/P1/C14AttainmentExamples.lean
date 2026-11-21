import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Independent statements of `fa2:p1:c14:attainment-examples`, paper.tex:3022–3028.
Both scalar fields use the continuous scalar-linear dual. Convexity is real
convexity, and closedness and distance refer to the given norm. The zero space,
the zero functional, zero distance, and unbounded closed convex sets are included.
-/
namespace ExpandedFA.P1.C14AttainmentExamples.Spec
universe u v

/-- A functional attains its norm and the real-part norm formula on the
closed unit ball of a canonically reflexive Banach space. -/
def FunctionalNormAttainment : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ f : E →L[𝕜] 𝕜, ∃ x : E,
      ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ ∧ RCLike.re (f x) = ‖f‖

/-- Every nonempty norm-closed real-convex set in a uniformly convex Banach
space has a unique nearest point to each specified vector. -/
def UniqueNearestPoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C → ∀ x : E,
      ∃! z : E, z ∈ C ∧ ‖x - z‖ = Metric.infDist x C ∧
        ∀ y ∈ C, ‖x - z‖ ≤ ‖x - y‖

end ExpandedFA.P1.C14AttainmentExamples.Spec
