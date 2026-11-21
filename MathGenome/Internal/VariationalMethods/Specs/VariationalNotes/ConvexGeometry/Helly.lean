import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations

/-!
Independent specification of `paper.tex`, Theorem `thm:helly` (Finite Helly).
The family is indexed by `Fin m`, so equal sets at different indices count as
different members. Real coordinate space is `Fin d → ℝ`, also when `d = 0`.
The hypothesis concerns subfamilies of exactly `d + 1` indices.
-/

namespace VariationalNotes.ConvexGeometry.Specs

/-- Finite Helly with the manuscript's exact-cardinality hypothesis. -/
def helly : Prop :=
  ∀ (d m : ℕ) (C : Fin m → Set (Fin d → ℝ)),
    d + 1 ≤ m →
    (∀ i, Convex ℝ (C i)) →
    (∀ I : Finset (Fin m), I.card = d + 1 → (⋂ i ∈ I, C i).Nonempty) →
    (⋂ i, C i).Nonempty

end VariationalNotes.ConvexGeometry.Specs
