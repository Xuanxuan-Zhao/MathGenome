import Mathlib.Analysis.LocallyConvex.Separation

/-!
Independent specification of `paper.tex`, Theorem `thm:geometric-separation`
(lines 364–375), with the global real, Hausdorff, locally convex convention.
No normability, completeness, finite dimension, or attainment on the closed
set is assumed. The boundedness clauses ensure that the real supremum and
infimum in the compact–closed conclusion are genuine finite extremal bounds.
-/

open Set

universe u

namespace VariationalNotes.ConvexGeometry.Specs

/-- Open–convex separation with a nonzero continuous real-linear functional. -/
def open_separation : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E],
    ∀ (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
      Disjoint A B → IsOpen A →
      ∃ (l : E →L[ℝ] ℝ) (α : ℝ), l ≠ 0 ∧
        (∀ a ∈ A, l a < α) ∧ (∀ b ∈ B, α ≤ l b)

/-- Compact–closed separation, including finite real extremal bounds. -/
def compact_closed_separation : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E],
    ∀ (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
      Disjoint A B → IsCompact A → IsClosed B →
      ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ BddAbove (l '' A) ∧ BddBelow (l '' B) ∧
        sSup (l '' A) < sInf (l '' B)

end VariationalNotes.ConvexGeometry.Specs
