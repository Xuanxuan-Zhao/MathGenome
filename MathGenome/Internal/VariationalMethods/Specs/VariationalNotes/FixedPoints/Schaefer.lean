import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statement of Schaefer's theorem, paper.tex:4749–4772.
Relative compactness is compactness of the image closure in the ambient
real Banach space. The homotopy parameter ranges over the closed interval.
-/

namespace VariationalNotes.FixedPoints.Schaefer.Spec

universe u

/-- A continuous map compact on bounded sets has a fixed point if its
scaled fixed points, including parameters zero and one, form a bounded set. -/
def FixedPoint : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E → E), Continuous T →
    (∀ B : Set E, Bornology.IsBounded B → IsCompact (closure (T '' B))) →
    Bornology.IsBounded {x : E | ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = t • T x} →
    ∃ x : E, T x = x

end VariationalNotes.FixedPoints.Schaefer.Spec
