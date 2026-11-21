import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import Mathlib.Topology.MetricSpace.Bounded

/-!
Independent specification for normal structure, paper.tex:13081–13085 and
13105–13113. Convexity is over the underlying real space, also for complex
spaces. The supremum is the real supremum of the actual norm distances.
For bounded ambient sets all subsets considered here are bounded; positive
diameter ensures they are nonempty, so this supremum has its usual meaning.
-/

namespace ExpandedFA.Geometry.NormalStructure.Spec

universe u v

def NormalStructureType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → Set E → Prop

/-- The property is meaningful for any ambient set. The theorem below applies
it to bounded convex sets, including empty sets and singletons. -/
def NormalStructureValue : NormalStructureType.{u} :=
  fun {E} _ _ C => ∀ D : Set E, D ⊆ C → Convex ℝ D → 0 < Metric.diam D →
    ∃ z ∈ D, sSup ((fun y => ‖z - y‖) '' D) < Metric.diam D

/-- The proof needs neither completeness nor closedness. This stronger normed
space form includes every uniformly convex Banach space in the source. The
uniform convexity predicate is the accepted shared manuscript predicate. -/
def UniformlyConvexNormalStructure : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    ExpandedFA.P1.C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
      letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
      ∀ C : Set E, Bornology.IsBounded C → Convex ℝ C → NormalStructureValue C

end ExpandedFA.Geometry.NormalStructure.Spec
