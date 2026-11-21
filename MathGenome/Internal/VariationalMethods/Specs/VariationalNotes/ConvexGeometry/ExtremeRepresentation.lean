import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations

/-!
Independent statement of `paper.tex`, Theorem `thm:extreme-representation`
(lines 308–328). The hull is the ordinary finite convex hull, with no closure.
The hypotheses cover every finite-dimensional Hausdorff real topological vector
space, including zero-dimensional spaces and singleton sets.
-/

open Set
universe u
namespace VariationalNotes.ConvexGeometry.Specs

/-- Every nonempty compact convex set is the convex hull of its extreme points. -/
def extremePoint_representation : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E),
    C.Nonempty → IsCompact C → Convex ℝ C → C = convexHull ℝ (C.extremePoints ℝ)

end VariationalNotes.ConvexGeometry.Specs
