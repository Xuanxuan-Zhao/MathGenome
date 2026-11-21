import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Compactness.Compact

/-! Independent statement of Schauder's theorem, `paper.tex:4713–4719`.
Relative compactness refers to the image closure in the ambient Banach space.
The closed convex domain itself need not be bounded.
-/

namespace VariationalNotes.FixedPoints.Schauder.Spec

universe u

/-- A continuous self-map of a nonempty closed convex subset of a real Banach
space has a fixed point if its entire image has compact ambient closure. -/
def FixedPoint : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ F : C → C, Continuous F →
      IsCompact (closure (Set.range (fun x : C => (F x : E)))) →
      ∃ x : C, F x = x

end VariationalNotes.FixedPoints.Schauder.Spec
