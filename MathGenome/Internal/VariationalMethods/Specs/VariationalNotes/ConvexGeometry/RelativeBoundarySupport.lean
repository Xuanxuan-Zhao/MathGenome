import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations

/-!
Independent statement of `paper.tex`, Lemma `lem:euclidean-boundary-support`
(lines 285–306). The direction space is exactly that of the affine hull.
Finite-dimensional real normed spaces include every finite-dimensional Euclidean
space; no full-dimensionality or positive dimension is assumed.
-/

open Set
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry.Specs

/-- Support at a relative boundary point, nonconstant on the original set. -/
def relativeBoundary_support : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (x : E) (hx : x ∈ C), x ∉ relativeInterior C →
    ∃ n : (affineSpan ℝ C).direction →ₗ[ℝ] ℝ,
      n ≠ 0 ∧
      (∀ (y : E) (hy : y ∈ C),
        n ⟨y - x, AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩ ≤ 0) ∧
      ∃ (y : E) (hy : y ∈ C),
        n ⟨y - x, AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hx)⟩ < 0

end VariationalNotes.ConvexGeometry.Specs
