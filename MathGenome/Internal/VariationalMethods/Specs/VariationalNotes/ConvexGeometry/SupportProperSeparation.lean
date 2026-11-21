import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeBoundarySupport
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeInteriorAffine

/-! Independent statements of `paper.tex`, Corollary `thm:proper-separation`
(lines 418–457). A supporting affine hyperplane is represented by a nonzero
linear functional with its maximum at the specified point. Normed spaces cover
all finite-dimensional Euclidean spaces; proper separation is stated for the
full finite-dimensional Hausdorff real topological vector space convention. -/

open Set
universe u
namespace VariationalNotes.ConvexGeometry.Specs

def ambientBoundary_support : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] (C : Set E),
    C.Nonempty → IsClosed C → Convex ℝ C → ∀ x ∈ frontier C,
    ∃ l : E →ₗ[ℝ] ℝ, l ≠ 0 ∧ ∀ y ∈ C, l y ≤ l x

/-- Within the affine hull the support is also nonconstant on C. -/
def relativeBoundary_support_corollary : Prop := relativeBoundary_support.{u}

def proper_separation : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C D : Set E),
    C.Nonempty → D.Nonempty → Convex ℝ C → Convex ℝ D →
    (relativeInterior C ∩ relativeInterior D = ∅ ↔
      ∃ l : E →ₗ[ℝ] ℝ, (∀ c ∈ C, ∀ d ∈ D, l c ≤ l d) ∧
        ∃ c ∈ C, ∃ d ∈ D, l c < l d)

end VariationalNotes.ConvexGeometry.Specs
