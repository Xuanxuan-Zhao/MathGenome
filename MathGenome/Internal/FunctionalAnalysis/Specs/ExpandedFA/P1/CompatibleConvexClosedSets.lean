import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
Independent statement of the compatible-topology clause of the dual-pair
bipolar theorem, paper.tex:2094–2116 (`fa2:p1:general-bipolar`).

The topologies are on the same vector space, with the same scalar action.
Equality of their continuous scalar-linear duals is expressed by continuity
of each algebraic scalar-linear functional in one topology iff in the other.
Convexity is over the reals also when the scalar field is complex. The
chapter's Hausdorff convention is explicit for each topology. No nonemptiness,
boundedness, completeness, metrizability, or comparison of topologies is assumed.
-/
namespace Specs.ExpandedFA.P1.CompatibleConvexClosedSets

/-- Compatible locally convex topologies have precisely the same closed
real-convex sets, over either the real or the complex scalar field. -/
def compatibleConvexClosedSetsType : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (t₁ t₂ : TopologicalSpace E),
    (letI := t₁; ExpandedFA.P1.LCS 𝕜 E) →
    (letI := t₂; ExpandedFA.P1.LCS 𝕜 E) →
    @T2Space E t₁ → @T2Space E t₂ →
    (∀ f : E →ₗ[𝕜] 𝕜,
      @Continuous E 𝕜 t₁ inferInstance f ↔ @Continuous E 𝕜 t₂ inferInstance f) →
    ∀ C : Set E, Convex ℝ C → (@IsClosed E t₁ C ↔ @IsClosed E t₂ C)

end Specs.ExpandedFA.P1.CompatibleConvexClosedSets
