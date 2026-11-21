import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Models
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Group.Constructions

/-! The matching clauses of paper.tex W35. Coordinates are precisely the allowed
edges; every vertex in either part has a constraint, including isolated vertices.
No nonemptiness or perfect-matchability assumption is imposed. -/
universe u v
noncomputable section
namespace P205.Matching.HullSpecs
open Specs.P205.Matching

def matching_hull : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R),
    convexHull ℝ {x | ∃ M : Set (Edge G), IsMatching M ∧ x = indicator M} =
      {x | (∀ e, 0 ≤ x e) ∧ ∀ v, load x v ≤ 1}

def perfect_matching_hull : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R),
    convexHull ℝ {x | ∃ M : Set (Edge G), IsPerfectMatching M ∧ x = indicator M} =
      {x | (∀ e, 0 ≤ x e) ∧ ∀ v, load x v = 1}

end P205.Matching.HullSpecs
