import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Foundations
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Radon
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace VariationalNotes.ConvexGeometry

/-- Radon's partition for `d + 2` indexed points, including repetitions and `d = 0`.
The complement block includes all indices not in the first block, including any
unused indices of an affine dependence. -/
theorem radon_partition :
    ∀ (d : ℕ) (p : Fin (d + 2) → (Fin d → ℝ)),
      ∃ I J : Set (Fin (d + 2)),
        I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Set.univ ∧
        (convexHull ℝ (p '' I) ∩ convexHull ℝ (p '' J)).Nonempty := by
  intro d p
  have hdep : ¬ AffineIndependent ℝ p := by
    apply (finrank_vectorSpan_le_iff_not_affineIndependent ℝ p
      (Fintype.card_fin (d + 2))).mp
    exact (Submodule.finrank_le (vectorSpan ℝ (Set.range p))).trans
      (by simp only [Module.finrank_fin_fun]; exact le_rfl)
  obtain ⟨I, x, hxI, hxJ⟩ := Convex.radon_partition hdep
  have hI : I.Nonempty :=
    Set.Nonempty.of_image (convexHull_nonempty_iff.mp ⟨x, hxI⟩)
  have hJ : Iᶜ.Nonempty :=
    Set.Nonempty.of_image (convexHull_nonempty_iff.mp ⟨x, hxJ⟩)
  exact ⟨I, Iᶜ, hI, hJ, disjoint_compl_right, Set.union_compl_self I,
    x, hxI, hxJ⟩

end VariationalNotes.ConvexGeometry
