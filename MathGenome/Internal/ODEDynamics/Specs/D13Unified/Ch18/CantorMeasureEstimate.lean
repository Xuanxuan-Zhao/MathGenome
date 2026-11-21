import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.CantorGeometry
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.BernoulliMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The coding probability and its interval estimate from the proof of
`d13:18:cantor-dimension`. All intervals are closed; monotonicity then covers
any interval with the same endpoints, including degenerate intervals. -/
namespace Specs.D13Unified.Ch18.CantorMeasureEstimate
open Set MeasureTheory
open scoped Classical ENNReal
open Specs.D13Unified.Ch17.CantorGeometry
open Specs.D13Unified.Ch17.ShiftSpaces
noncomputable section

def cantorMeasure (r : ℝ) : Measure ℝ :=
  Measure.map (coding r) Specs.D13Unified.Ch19.BernoulliMeasure.bernoulliPlus

def exponent (r : ℝ) : ℝ := Real.log 2 / Real.log (1 / r)

def intervalConstant (r : ℝ) : ℝ := 2 + 1 / (1 - 2*r)

def meetingWords (r : ℝ) (n : ℕ) (a b : ℝ) : Finset (Fin n → Binary) :=
  Finset.univ.filter fun w => (Icc a b ∩ levelInterval r w).Nonempty

def cantorMeasureType := ℝ → Measure ℝ
def exponentType := ℝ → ℝ
def intervalConstantType := ℝ → ℝ
def meetingWordsType := ℝ → (n : ℕ) → ℝ → ℝ → Finset (Fin n → Binary)

def coding_measurableStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → Measurable (coding r)

def probabilityStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → IsProbabilityMeasure (cantorMeasure r)

def supportedStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → cantorMeasure r (cantorSet r)ᶜ = 0

def cylinder_massStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, ∀ w : Fin n → Binary,
    cantorMeasure r (levelInterval r w) = (2 : ℝ≥0∞) ^ (-(n : ℤ))

def meeting_boundStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ n : ℕ, 1 ≤ n → ∀ a b : ℝ,
    a ≤ b → b-a ≤ r^(n-1) →
    ((meetingWords r n a b).card : ℝ) ≤ intervalConstant r

def interval_boundStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    0 < exponent r ∧ 0 < intervalConstant r ∧
    ∀ a b : ℝ, a ≤ b → b-a ≤ 1 →
      cantorMeasure r (Icc a b) ≤ ENNReal.ofReal (intervalConstant r * (b-a) ^ exponent r)

/-- A stronger diameter formulation, covering all short bounded intervals
irrespective of endpoint conventions. No measurability of the subset is needed. -/
def bounded_set_boundStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ J : Set ℝ,
    Bornology.IsBounded J → Metric.diam J ≤ 1 →
    cantorMeasure r J ≤ ENNReal.ofReal (intervalConstant r * (Metric.diam J) ^ exponent r)

end
end Specs.D13Unified.Ch18.CantorMeasureEstimate
