import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Dimension

/-!
Independent specification of Theorem `thm:caratheodory`, paper.tex:269–272.
Affine dimension is the cardinal dimension of the affine span, with bottom
dimension for the empty set. Bounding this by a natural number imposes no
finite-dimensionality requirement on the ambient real vector space.
-/

noncomputable section
universe u

namespace VariationalNotes.ConvexGeometry.Specs

/-- Each convex-hull point has a convex representation on at most `d + 1`
distinct generators when the affine dimension of the generators is at most `d`.
The same statement includes `d = 0` and the vacuous empty-set case. -/
def caratheodory : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (S : Set E) (d : ℕ),
    (affineSpan ℝ S).dim ≤ (d : Cardinal) →
    ∀ x ∈ convexHull ℝ S,
      ∃ (t : Finset E) (w : E → ℝ),
        (↑t : Set E) ⊆ S ∧ t.card ≤ d + 1 ∧
        (∀ y ∈ t, 0 ≤ w y) ∧
        (∑ y ∈ t, w y) = 1 ∧ (∑ y ∈ t, w y • y) = x

end VariationalNotes.ConvexGeometry.Specs
