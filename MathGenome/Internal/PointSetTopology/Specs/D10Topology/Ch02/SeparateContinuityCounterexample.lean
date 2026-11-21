import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Field

/-!
Independent specification of the separate-continuity example in
paper.tex, d10:02:cautions. Both copies of ℝ have their usual topology,
and ℝ × ℝ has its usual product topology. There are no extra hypotheses.
-/

namespace Specs.D10Topology.Ch02.SeparateContinuityCounterexample

/-- The paper's function, with its prescribed value at the origin. -/
noncomputable def exampleMap (p : ℝ × ℝ) : ℝ :=
  if p = (0, 0) then 0 else p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)

def mapType := ℝ × ℝ → ℝ
noncomputable def mapValue : mapType := exampleMap

def at_origin : Prop := exampleMap (0, 0) = 0

def off_origin : Prop := ∀ p : ℝ × ℝ, p ≠ (0, 0) →
  exampleMap p = p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)

def horizontal_zero : Prop := ∀ x : ℝ, exampleMap (x, 0) = 0

def vertical_zero : Prop := ∀ y : ℝ, exampleMap (0, y) = 0

/-- Fixing any second coordinate, including zero, gives a continuous function. -/
def horizontal_continuous : Prop :=
  ∀ y : ℝ, Continuous (fun x : ℝ => exampleMap (x, y))

/-- Fixing any first coordinate, including zero, gives a continuous function. -/
def vertical_continuous : Prop :=
  ∀ x : ℝ, Continuous (fun y : ℝ => exampleMap (x, y))

def diagonal_value : Prop :=
  ∀ t : ℝ, t ≠ 0 → exampleMap (t, t) = 1 / 2

def not_continuousAt_origin : Prop := ¬ ContinuousAt exampleMap (0, 0)

def not_continuous : Prop := ¬ Continuous exampleMap

end Specs.D10Topology.Ch02.SeparateContinuityCounterexample
