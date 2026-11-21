import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.Definitions

open Filter Topology

noncomputable section

namespace NumAnalysis206.Evolution.StepRestriction

/-- The extension to nonpositive steps is immaterial. For positive steps this is
exactly the multiplier in the example following W18. -/
def coefficient (h : ℝ) : ℝ :=
  if h ≤ 1 / 2 ∨ h = 3 / 4 then 1 else 1 / |h - 3 / 4|

/-- Each discrete operator is a bounded real linear map. -/
def operators (h : ℝ) : ℝ →L[ℝ] ℝ :=
  coefficient h • (1 : ℝ →L[ℝ] ℝ)

/-- The identity semigroup, defined at all real times as a harmless extension. -/
def exactSemigroup : StronglyContinuousSemigroup ℝ ℝ where
  toFun := fun _ => 1
  map_zero := rfl
  map_add := by intros; simp
  strong_continuous := fun _ => continuous_const.continuousOn

end NumAnalysis206.Evolution.StepRestriction

namespace Specs.NumAnalysis206.Evolution.StepRestriction

open _root_.NumAnalysis206.Evolution
open _root_.NumAnalysis206.Evolution.StepRestriction

/-- The complete scalar counterexample on horizon one. The penultimate conjunct
exhibits the failure already at n = 1, with steps strictly above 3/4. -/
def exampleProperties : Prop :=
  (∀ h : ℝ, Continuous (operators h)) ∧
  (∀ h : ℝ, 0 < h → h ≤ 1 / 2 → operators h = 1) ∧
  operators (3 / 4) = 1 ∧
  (∀ h : ℝ, 1 / 2 < h → h ≠ 3 / 4 → ∀ x : ℝ,
    operators h x = (1 / |h - 3 / 4|) * x) ∧
  (∀ x h : ℝ, 0 < h → h ≤ 1 / 2 →
    meshError operators exactSemigroup 1 h x = 0) ∧
  StronglyConvergent operators exactSemigroup 1 ∧
  SmallStepStable operators 1 ∧
  (∀ M : ℝ, ∃ h : ℝ, 3 / 4 < h ∧ h ≤ 1 ∧ M < ‖operators h ^ 1‖) ∧
  ¬ (∃ M : ℝ, ∀ h : ℝ, 0 < h → ∀ n : ℕ,
    (n : ℝ) * h ≤ 1 → ‖operators h ^ n‖ ≤ M)

end Specs.NumAnalysis206.Evolution.StepRestriction
