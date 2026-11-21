import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RecessionSets

open Set
open scoped Pointwise
noncomputable section
universe u v
namespace VariationalNotes.ConvexGeometry.Specs

/-- The closed-image criterion of `paper.tex`, Theorem `thm:closed-image`.
The kernel recession directions may be nonzero; they need only be lineality directions.
Both spaces carry their Hausdorff real locally convex vector-space topologies. -/
def closed_linear_image : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
    [LocallyConvexSpace ℝ F] [FiniteDimensional ℝ F],
    ∀ (C : Set E) (A : E →ₗ[ℝ] F),
      C.Nonempty → IsClosed C → Convex ℝ C →
      recession C ∩ (A.ker : Set E) ⊆ lineality C → IsClosed (A '' C)

end VariationalNotes.ConvexGeometry.Specs
