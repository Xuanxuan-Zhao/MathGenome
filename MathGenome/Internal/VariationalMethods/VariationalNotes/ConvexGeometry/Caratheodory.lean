import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Caratheodory
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

noncomputable section
universe u

namespace VariationalNotes.ConvexGeometry

/-- Carathéodory's theorem with the dimension of the affine hull of `S`,
even when the ambient real vector space is infinite-dimensional. -/
theorem caratheodory :
    ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (S : Set E) (d : ℕ),
      (affineSpan ℝ S).dim ≤ (d : Cardinal) →
      ∀ x ∈ convexHull ℝ S,
        ∃ (t : Finset E) (w : E → ℝ),
          (↑t : Set E) ⊆ S ∧ t.card ≤ d + 1 ∧
          (∀ y ∈ t, 0 ≤ w y) ∧
          (∑ y ∈ t, w y) = 1 ∧ (∑ y ∈ t, w y • y) = x := by
  intro E _ _ S d hdim x hx
  classical
  -- A minimal finite convex representation has affinely independent support.
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (↑t : Set E) ⊆ S :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hi : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hxt : x ∈ convexHull ℝ (↑t : Set E) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  -- Convex-hull membership rules out the empty affine hull.
  have hne : affineSpan ℝ S ≠ ⊥ := by
    intro h
    have hm := convexHull_subset_affineSpan S hx
    simp [h] at hm
  have hrank : Module.rank ℝ (vectorSpan ℝ S) ≤ (d : Cardinal) := by
    rw [AffineSubspace.dim_eq_rank hne, direction_affineSpan] at hdim
    exact_mod_cast hdim
  have hsmall : Module.finrank ℝ (vectorSpan ℝ (↑t : Set E)) ≤ d :=
    Module.finrank_le_of_rank_le ((Submodule.rank_mono (vectorSpan_mono ℝ ht)).trans hrank)
  have hcard : t.card ≤ d + 1 := by
    have hc := hi.card_le_finrank_succ
    have hrange : Set.range ((↑) : t → E) = (↑t : Set E) := by
      ext y
      simp
    rw [hrange, Fintype.card_coe] at hc
    exact hc.trans (Nat.add_le_add_right hsmall 1)
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxt
  exact ⟨t, w, ht, hcard, hw0, hw1, hwx⟩

end VariationalNotes.ConvexGeometry
