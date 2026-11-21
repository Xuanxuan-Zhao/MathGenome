import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

/-! Independent statements for `paper.tex`, Example fa2:p1:c24:comparison-example (lines 5181–5191).
The three functions are self-maps of the interval with its induced real topology.
The shared definitions below specify their actual values, including endpoints. -/

noncomputable section

open Filter
open scoped Topology

namespace ExpandedFA.P1.C24ComparisonExample.Spec

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def zeroPoint : UnitInterval := ⟨0, by constructor <;> norm_num⟩
def onePoint : UnitInterval := ⟨1, by constructor <;> norm_num⟩
def midpoint : UnitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

def identityMap : UnitInterval → UnitInterval := id

def reflection : UnitInterval → UnitInterval := fun x =>
  ⟨1 - x.val, sub_nonneg.mpr x.property.2, sub_le_self 1 x.property.1⟩

def halving : UnitInterval → UnitInterval := fun x =>
  ⟨x.val / 2, div_nonneg x.property.1 (by norm_num),
    (div_le_self x.property.1 (by norm_num : (1 : ℝ) ≤ 2)).trans x.property.2⟩

/-- Common Schauder geometry, retaining both endpoints of the interval. -/
def IntervalGeometry : Prop :=
  (Set.Icc (0 : ℝ) 1).Nonempty ∧ IsCompact (Set.Icc (0 : ℝ) 1) ∧
  Convex ℝ (Set.Icc (0 : ℝ) 1)

def IdentityExample : Prop :=
  Continuous identityMap ∧ (∀ x : UnitInterval, identityMap x = x) ∧
  zeroPoint ≠ onePoint

/-- Reflection has optimal Lipschitz constant one. Its two subsequences are
constant, and the whole orbit has no real limit away from the midpoint. -/
def ReflectionExample : Prop :=
  Continuous reflection ∧ Isometry reflection ∧ LipschitzWith 1 reflection ∧
  (∀ q : ℝ, (∀ x y : UnitInterval,
    ‖(reflection x : ℝ) - (reflection y : ℝ)‖ ≤ q * ‖(x : ℝ) - (y : ℝ)‖) → 1 ≤ q) ∧
  reflection midpoint = midpoint ∧
  (∀ x : UnitInterval, reflection x = x → x = midpoint) ∧
  (∀ (x : UnitInterval) (n : ℕ),
    (reflection^[2 * n]) x = x ∧ (reflection^[2 * n + 1]) x = reflection x) ∧
  (∀ x : UnitInterval, (x : ℝ) ≠ 1 / 2 →
    ¬ ∃ l : ℝ, Tendsto (fun n : ℕ => ((reflection^[n]) x : ℝ)) atTop (𝓝 l))

/-- Halving is a strict contraction, including at the endpoints. The exact
orbit and exact geometric norm formula hold also at iteration index zero. -/
def HalvingExample : Prop :=
  Continuous halving ∧ ContractingWith (1 / 2) halving ∧
  halving zeroPoint = zeroPoint ∧
  (∀ x : UnitInterval, halving x = x → x = zeroPoint) ∧
  (∀ (x : UnitInterval) (n : ℕ), ((halving^[n]) x : ℝ) = (x : ℝ) / 2 ^ n) ∧
  (∀ (x : UnitInterval) (n : ℕ),
    ‖((halving^[n]) x : ℝ) - (zeroPoint : ℝ)‖ = (1 / 2 : ℝ) ^ n * ‖(x : ℝ)‖) ∧
  (∀ x : UnitInterval,
    Tendsto (fun n : ℕ => ((halving^[n]) x : ℝ)) atTop (𝓝 (0 : ℝ)))

end ExpandedFA.P1.C24ComparisonExample.Spec
