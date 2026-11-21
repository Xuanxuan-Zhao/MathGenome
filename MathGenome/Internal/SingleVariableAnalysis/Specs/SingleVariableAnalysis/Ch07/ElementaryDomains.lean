import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
K03.07.elementary_domains, paper.tex:1829–1847.

These partial interfaces record the real domains of the existing functions.
The power interface here is the initial positive-base definition; the previously
specified continuous extensions and algebraic negative-base powers are separate.
The square root uses the canonical nonnegative root, with an explicit bridge to
the supremum construction. No inverse-function assertion uses values outside its
domain, and no complex logarithm is introduced.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.ElementaryDomains
open Set Filter
open scoped Topology
open SinCos PiPeriod TrigInverses

def realPartialType : Type := ℝ → Option ℝ
def positivePowerType : Type := ℝ → ℝ → Option ℝ

def logarithmValue : realPartialType := fun x =>
  if 0 < x then some (LogConstruction.seriesLogValue x) else none
def positivePowerValue : positivePowerType := fun x α =>
  if 0 < x then some (RealPowers.realPowerValue x α) else none
def squareRootValue : realPartialType := fun x =>
  if 0 ≤ x then some (Real.sqrt x) else none
def arcsineValue : realPartialType := fun x =>
  if x ∈ Icc (-1 : ℝ) 1 then some (principalArcsinValue x) else none
def arccosineValue : realPartialType := fun x =>
  if x ∈ Icc (-1 : ℝ) 1 then some (principalArccosValue x) else none

abbrev realDomainType : Type := Set ℝ
def cosineDenominatorDomainValue : realDomainType := {x | realSeriesCosValue x ≠ 0}
def sineDenominatorDomainValue : realDomainType := {x | realSeriesSinValue x ≠ 0}

def exactDomains : Prop :=
  (∀ x : ℝ, (logarithmValue x).isSome = true ↔ 0 < x) ∧
  (∀ x α : ℝ, (positivePowerValue x α).isSome = true ↔ 0 < x) ∧
  (∀ x : ℝ, (squareRootValue x).isSome = true ↔ 0 ≤ x) ∧
  (∀ x : ℝ, (arcsineValue x).isSome = true ↔ x ∈ Icc (-1 : ℝ) 1) ∧
  (∀ x : ℝ, (arccosineValue x).isSome = true ↔ x ∈ Icc (-1 : ℝ) 1)

def squareRootBranch : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    squareRootValue x = some (Ch01.PositiveRoots.nonnegativeRootValue 2 x) ∧
    0 ≤ Real.sqrt x ∧ Real.sqrt x ^ 2 = x ∧
    ∀ y : ℝ, 0 ≤ y → y ^ 2 = x → y = Real.sqrt x

def principalRanges : Prop :=
  principalArcsinValue '' Icc (-1 : ℝ) 1 =
    Icc (-(analyticPiValue / 2)) (analyticPiValue / 2) ∧
  principalArccosValue '' Icc (-1 : ℝ) 1 = Icc 0 analyticPiValue ∧
  range principalArctanValue = Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2)

def reciprocalDomains : Prop :=
  (∀ x : ℝ, x ∈ cosineDenominatorDomainValue ↔
    ¬ ∃ k : ℤ, x = analyticPiValue / 2 + k * analyticPiValue) ∧
  (∀ x : ℝ, x ∈ sineDenominatorDomainValue ↔
    ¬ ∃ k : ℤ, x = k * analyticPiValue)

def sineTranslatedSolutions : Prop :=
  ∀ x : ℝ, |x| < 1 → ∀ k : ℤ,
    realSeriesSinValue (principalArcsinValue x + k * (2 * analyticPiValue)) = x ∧
    realSeriesSinValue (analyticPiValue - principalArcsinValue x +
      k * (2 * analyticPiValue)) = x

def sinePrincipalUnique : Prop :=
  ∀ x ∈ Icc (-1 : ℝ) 1, ∃! y : ℝ,
    y ∈ Icc (-(analyticPiValue / 2)) (analyticPiValue / 2) ∧ realSeriesSinValue y = x

def sineDistinctSolutions : Prop :=
  ∀ x : ℝ, |x| < 1 →
    principalArcsinValue x ≠ analyticPiValue - principalArcsinValue x ∧
    ¬ ∃! y : ℝ, realSeriesSinValue y = x

def squareRootDerivative : Prop :=
  ∀ x : ℝ, 0 < x → HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x

def squareRootRightQuotient : Prop :=
  ∀ h : ℝ, 0 < h →
    (Real.sqrt (0 + h) - Real.sqrt 0) / h = 1 / Real.sqrt h

def squareRootRightInfinite : Prop :=
  Tendsto (fun h : ℝ => (Real.sqrt (0 + h) - Real.sqrt 0) / h) (𝓝[>] 0) atTop

end Specs.SingleVariableAnalysis.Ch07.ElementaryDomains
