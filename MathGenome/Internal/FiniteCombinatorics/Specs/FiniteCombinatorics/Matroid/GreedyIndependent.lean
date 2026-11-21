import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyBasis
import Mathlib.Combinatorics.Matroid.Loop

/-! Independent statements for the independent-set conclusions and negative
one-coloop example in paper.tex W79. No nonemptiness or positive-rank
hypothesis is imposed. Zero weights remain in the nonnegative restriction. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def greedyIndependentOptimal : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E),
    (∀ e, 0 ≤ w e) →
    IndependentOptimal (fromMatroid M) w (greedyOutput (fromMatroid M) w tie)

def nonnegativeGreedyIndependentOptimal : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E),
    IndependentOptimal (fromMatroid M) w
      (nonnegativeGreedyOutput (fromMatroid M) w tie)

/-- The free matroid on one point has a unique basis of weight -1, whereas
empty is an optimal independent set of weight zero. The two algorithms return
these respective sets for every tie order. -/
def negativeColoopExample : Prop :=
  let M : _root_.Matroid Unit := _root_.Matroid.freeOn univ
  let w : M.E → ℝ := fun _ => -1
  M.IsColoop () ∧
    (∀ B, M.IsBase B ↔ B = univ) ∧
    (∀ B, M.IsBase B → subsetWeight (fromMatroid M) w B = -1) ∧
    IndependentOptimal (fromMatroid M) w ∅ ∧
    subsetWeight (fromMatroid M) w ∅ = 0 ∧
    ∀ tie : LinearOrder M.E,
      greedyOutput (fromMatroid M) w tie = univ ∧
      nonnegativeGreedyOutput (fromMatroid M) w tie = ∅

end FiniteCombinatorics.Matroid.Expected
