import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.RotationLimit

/-!
Independent specification of the complete theorem `d13:15:rotation-number`
in `paper.tex`. The shared real rotation number is used without redefining it.
The fraction criterion has no coprimality hypothesis. Positive integer
denominators are expressed both as positive naturals and as integers at least one.
-/
namespace Specs.D13Unified.Ch15.RotationNumber

open Filter
open scoped Topology
open CircleLift RotationLimit

def rotationNumber_tendstoStatement : Prop :=
  ∀ (L : IncreasingLift) (x : ℝ),
    Tendsto (fun n : ℕ => ((L : ℝ → ℝ)^[n] x - x) / (n : ℝ))
      atTop (𝓝 (rotationNumber L))

def rotationNumber_shiftStatement : Prop :=
  ∀ (L : IncreasingLift) (k : ℤ),
    rotationNumber (shiftLift L k) = rotationNumber L + (k : ℝ)

def rotationNumber_eq_rat_iffStatement : Prop :=
  ∀ (L : IncreasingLift) (p : ℤ) (q : ℕ), 0 < q →
    (rotationNumber L = (p : ℝ) / (q : ℝ) ↔
      ∃ x : ℝ, (L : ℝ → ℝ)^[q] x = x + (p : ℝ))

def rotationNumber_eq_int_div_int_iffStatement : Prop :=
  ∀ (L : IncreasingLift) (p q : ℤ), 1 ≤ q →
    (rotationNumber L = (p : ℝ) / (q : ℝ) ↔
      ∃ x : ℝ, (L : ℝ → ℝ)^[q.toNat] x = x + (p : ℝ))

/-- A periodic point has a positive return time; time zero is excluded. -/
def periodicPoint_iff_rationalStatement : Prop :=
  ∀ L : IncreasingLift,
    (∃ y : Circle, ∃ q : ℕ, 0 < q ∧ (circleMap L)^[q] y = y) ↔
      ∃ r : ℚ, rotationNumber L = (r : ℝ)

end Specs.D13Unified.Ch15.RotationNumber
