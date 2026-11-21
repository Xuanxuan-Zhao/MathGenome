import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations

/-!
Independent specification of `paper.tex`, Lemma `lem:radon-partition`
(lines 330–342). Real coordinate space is represented by `Fin d → ℝ`.
The blocks partition the indices, so repeated points are allowed. No positivity
assumption on `d` is imposed, and every index belongs to one of the blocks.
-/

namespace VariationalNotes.ConvexGeometry.Specs

/-- Any indexed family of `d + 2` points in real `d`-space has a Radon partition. -/
def radon_partition : Prop :=
  ∀ (d : ℕ) (p : Fin (d + 2) → (Fin d → ℝ)),
    ∃ I J : Set (Fin (d + 2)),
      I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Set.univ ∧
      (convexHull ℝ (p '' I) ∩ convexHull ℝ (p '' J)).Nonempty

end VariationalNotes.ConvexGeometry.Specs
