import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-! Independent statements for paper.tex, Theorem p206:W62 and its cubic example. -/

namespace Specs.NumAnalysis206.Iterations.BracketExistence

/-- Nonpositive endpoint product permits a root at either endpoint. -/
def closedBracket : Prop :=
  ∀ (a b : ℝ) (f : ℝ → ℝ), a < b →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∃ p ∈ Set.Icc a b, f p = 0

/-- Strictly opposite signs imply an interior root; they already imply nonzero endpoints. -/
def openBracket : Prop :=
  ∀ (a b : ℝ) (f : ℝ → ℝ), a < b →
    ContinuousOn f (Set.Icc a b) → f a * f b < 0 →
    ∃ p ∈ Set.Ioo a b, f p = 0

/-- The source's example witnesses the failure of uniqueness in a sign bracket. -/
def cubicExample : Prop :=
  let f : ℝ → ℝ := fun x => x * (x ^ 2 - 1)
  ContinuousOn f (Set.Icc (-2) 2) ∧
    f (-2) = -6 ∧ f 2 = 6 ∧ f (-2) * f 2 < 0 ∧
    ((-1 : ℝ) ∈ Set.Icc (-2) 2 ∧ f (-1) = 0) ∧
    ((0 : ℝ) ∈ Set.Icc (-2) 2 ∧ f 0 = 0) ∧
    ((1 : ℝ) ∈ Set.Icc (-2) 2 ∧ f 1 = 0) ∧
    (-1 : ℝ) ≠ 0 ∧ (-1 : ℝ) ≠ 1 ∧ (0 : ℝ) ≠ 1

end Specs.NumAnalysis206.Iterations.BracketExistence
