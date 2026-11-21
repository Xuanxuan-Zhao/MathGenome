import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigProperties
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
K03.07.pi_period (paper.tex:1691–1720). S and C remain the real factorial
series fixed upstream. The first positive zero is represented by the infimum
of its positive zero set; `firstZeroLeast` asserts its positivity and attainment,
so no existence certificate is assumed by either definition. π is twice this
zero. Integer translates in the sign and monotonicity statements cover all
quadrants, with the closed monotonicity intervals retaining their endpoints.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.PiPeriod
open Ch07.SinCos

def firstPositiveCosineZeroType : Type := ℝ
def firstPositiveCosineZeroValue : ℝ :=
  sInf {x : ℝ | 0 < x ∧ realSeriesCosValue x = 0}
def analyticPiType : Type := ℝ
def analyticPiValue : ℝ := 2 * firstPositiveCosineZeroValue

def firstZeroCanonical : Prop :=
  firstPositiveCosineZeroValue = Real.pi / 2

def firstZeroLeast : Prop :=
  IsLeast {x : ℝ | 0 < x ∧ realSeriesCosValue x = 0} firstPositiveCosineZeroValue

def piCanonical : Prop :=
  analyticPiValue = Real.pi

def positive : Prop :=
  0 < firstPositiveCosineZeroValue ∧ 0 < analyticPiValue

def cosinePositiveBefore : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < firstPositiveCosineZeroValue → 0 < realSeriesCosValue x

def firstZeroValues : Prop :=
  realSeriesSinValue firstPositiveCosineZeroValue = 1 ∧ realSeriesCosValue firstPositiveCosineZeroValue = 0

def firstQuadrantMonotonicity : Prop :=
  StrictMonoOn realSeriesSinValue (Set.Icc 0 firstPositiveCosineZeroValue) ∧
    StrictAntiOn realSeriesCosValue (Set.Icc 0 firstPositiveCosineZeroValue)

def firstQuadrantRanges : Prop :=
  realSeriesSinValue '' Set.Icc 0 firstPositiveCosineZeroValue = Set.Icc 0 1 ∧
    realSeriesCosValue '' Set.Icc 0 firstPositiveCosineZeroValue = Set.Icc 0 1

def quarterRelations : Prop :=
  ∀ x : ℝ,
    realSeriesSinValue (x + firstPositiveCosineZeroValue) = realSeriesCosValue x ∧
    realSeriesCosValue (x + firstPositiveCosineZeroValue) = -realSeriesSinValue x ∧
    realSeriesSinValue (x + 2 * firstPositiveCosineZeroValue) = -realSeriesSinValue x ∧
    realSeriesCosValue (x + 2 * firstPositiveCosineZeroValue) = -realSeriesCosValue x

def periodic : Prop :=
  Function.Periodic realSeriesSinValue (2 * analyticPiValue) ∧
    Function.Periodic realSeriesCosValue (2 * analyticPiValue)

def integerPeriods : Prop :=
  ∀ (k : ℤ) (x : ℝ),
    realSeriesSinValue (x + k * (2 * analyticPiValue)) = realSeriesSinValue x ∧
    realSeriesCosValue (x + k * (2 * analyticPiValue)) = realSeriesCosValue x

def quadrantSigns : Prop :=
  ∀ (k : ℤ) (x : ℝ),
    (x ∈ Set.Ioo 0 firstPositiveCosineZeroValue →
      0 < realSeriesSinValue (x + k * (2 * analyticPiValue)) ∧
      0 < realSeriesCosValue (x + k * (2 * analyticPiValue))) ∧
    (x ∈ Set.Ioo firstPositiveCosineZeroValue (2 * firstPositiveCosineZeroValue) →
      0 < realSeriesSinValue (x + k * (2 * analyticPiValue)) ∧
      realSeriesCosValue (x + k * (2 * analyticPiValue)) < 0) ∧
    (x ∈ Set.Ioo (2 * firstPositiveCosineZeroValue) (3 * firstPositiveCosineZeroValue) →
      realSeriesSinValue (x + k * (2 * analyticPiValue)) < 0 ∧
      realSeriesCosValue (x + k * (2 * analyticPiValue)) < 0) ∧
    (x ∈ Set.Ioo (3 * firstPositiveCosineZeroValue) (4 * firstPositiveCosineZeroValue) →
      realSeriesSinValue (x + k * (2 * analyticPiValue)) < 0 ∧
      0 < realSeriesCosValue (x + k * (2 * analyticPiValue)))

def quadrantMonotonicity : Prop :=
  ∀ k : ℤ,
    StrictMonoOn realSeriesSinValue
      (Set.Icc (-firstPositiveCosineZeroValue + k * (2 * analyticPiValue))
        (firstPositiveCosineZeroValue + k * (2 * analyticPiValue))) ∧
    StrictAntiOn realSeriesSinValue
      (Set.Icc (firstPositiveCosineZeroValue + k * (2 * analyticPiValue))
        (3 * firstPositiveCosineZeroValue + k * (2 * analyticPiValue))) ∧
    StrictAntiOn realSeriesCosValue
      (Set.Icc (k * (2 * analyticPiValue)) (2 * firstPositiveCosineZeroValue + k * (2 * analyticPiValue))) ∧
    StrictMonoOn realSeriesCosValue
      (Set.Icc (2 * firstPositiveCosineZeroValue + k * (2 * analyticPiValue))
        (4 * firstPositiveCosineZeroValue + k * (2 * analyticPiValue)))

def sineZeros : Prop :=
  ∀ x : ℝ, realSeriesSinValue x = 0 ↔ ∃ k : ℤ, x = k * analyticPiValue

def cosineZeros : Prop :=
  ∀ x : ℝ, realSeriesCosValue x = 0 ↔
    ∃ k : ℤ, x = firstPositiveCosineZeroValue + k * analyticPiValue

def commonPeriods : Prop :=
  ∀ p : ℝ,
    (Function.Periodic realSeriesSinValue p ∧ Function.Periodic realSeriesCosValue p) ↔
      ∃ k : ℤ, p = k * (2 * analyticPiValue)

def leastPositiveCommonPeriod : Prop :=
  ∀ p : ℝ, 0 < p →
    Function.Periodic realSeriesSinValue p → Function.Periodic realSeriesCosValue p →
      2 * analyticPiValue ≤ p

end Specs.SingleVariableAnalysis.Ch07.PiPeriod
