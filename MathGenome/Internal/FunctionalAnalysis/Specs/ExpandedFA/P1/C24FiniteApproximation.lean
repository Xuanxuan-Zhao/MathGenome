import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Complex.Basic

/-! Independent statement of paper.tex, Lemma fa2:p1:c24:finite-approximation (lines 5051–5057).
The finite family is represented by its nonempty finite set of centers.
All subtypes carry the topologies induced from the original normed space.
Real scalars include the underlying real space of a complex normed space.
-/

namespace ExpandedFA.P1.C24FiniteApproximation.Spec

universe u

def FiniteConvexApproximation : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E), Q.Nonempty → IsCompact Q →
    ∀ ε : ℝ, 0 < ε →
      ∃ s : Set E, s.Finite ∧ s.Nonempty ∧ s ⊆ Q ∧
        ∃ P : Q → convexHull ℝ s,
          Continuous P ∧ ∀ x : Q, ‖(P x : E) - (x : E)‖ < ε

/-- The complex case explicitly uses restriction to real scalars, while keeping
the original norm, metric, and induced subtype topologies. -/
def FiniteConvexApproximationComplex : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    ∀ (Q : Set E), Q.Nonempty → IsCompact Q →
      ∀ ε : ℝ, 0 < ε →
        ∃ s : Set E, s.Finite ∧ s.Nonempty ∧ s ⊆ Q ∧
          ∃ P : Q → convexHull ℝ s,
            Continuous P ∧ ∀ x : Q, ‖(P x : E) - (x : E)‖ < ε

end ExpandedFA.P1.C24FiniteApproximation.Spec
