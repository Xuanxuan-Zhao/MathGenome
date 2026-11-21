import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Sequential
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.PiPeriod

/-!
K03.02.domain_zeros, paper.tex:479–489. The domain is ℝ \ {0}, with
punctured approach to zero. Canonical sine and π are identified with the
upstream factorial-series sine and analytically constructed π explicitly.
The sample formulas are the source formulas, indexed here by natural numbers
starting at zero; their denominators are positive even at that extra index.
Asymptotic equivalence is spelled out as eventual nonvanishing and ratio
limit one, since its separate implementation is not a prerequisite here.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch02.DomainZeros
open Filter
open scoped Topology

abbrev domain : Set ℝ := {0}ᶜ

def numeratorType : Type := ℝ → ℝ
def numeratorValue : numeratorType := fun x => x * Real.sin (1 / x)
def denominatorType : Type := ℝ → ℝ
def denominatorValue : denominatorType := fun x => x
def positiveSampleType : Type := ℕ → ℝ
def positiveSampleValue : positiveSampleType :=
  fun n => 1 / (Real.pi / 2 + 2 * Real.pi * n)
def negativeSampleType : Type := ℕ → ℝ
def negativeSampleValue : negativeSampleType :=
  fun n => 1 / (3 * Real.pi / 2 + 2 * Real.pi * n)

def constructedIdentifications : Prop :=
  (∀ x, numeratorValue x = x * Ch07.SinCos.realSeriesSinValue (1 / x)) ∧
  (∀ n : ℕ, positiveSampleValue n =
    1 / (Ch07.PiPeriod.analyticPiValue / 2 + 2 * Ch07.PiPeriod.analyticPiValue * n)) ∧
  (∀ n : ℕ, negativeSampleValue n =
    1 / (3 * Ch07.PiPeriod.analyticPiValue / 2 + 2 * Ch07.PiPeriod.analyticPiValue * n))

def absoluteBound : Prop := ∀ x ∈ domain, |numeratorValue x| ≤ |denominatorValue x|
def bigO : Prop := BigO.scalarBigOValue
  (BigO.approachFilterValue domain (.punctured 0)) numeratorValue denominatorValue

def numeratorLimit : Prop :=
  RelativeLimit.relativePuncturedLimitValue numeratorValue domain 0 0

def ratioIdentity : Prop := ∀ x ∈ domain,
  numeratorValue x / denominatorValue x = Real.sin (1 / x)

def sampleMembership : Prop := ∀ n,
  positiveSampleValue n ∈ domain ∧ negativeSampleValue n ∈ domain ∧
  0 < positiveSampleValue n ∧ 0 < negativeSampleValue n

def sampleLimits : Prop :=
  Ch01.SequenceLimit.realSequenceConvergesValue positiveSampleValue 0 ∧
  Ch01.SequenceLimit.realSequenceConvergesValue negativeSampleValue 0

def sampleRatioValues : Prop := ∀ n,
  numeratorValue (positiveSampleValue n) / denominatorValue (positiveSampleValue n) = 1 ∧
  numeratorValue (negativeSampleValue n) / denominatorValue (negativeSampleValue n) = -1

def ratioNoLimit : Prop := ¬ ∃ L : ℝ,
  RelativeLimit.relativePuncturedLimitValue
    (fun x => numeratorValue x / denominatorValue x) domain 0 L

def notLittleO : Prop := ¬ BigO.scalarLittleOValue
  (BigO.approachFilterValue domain (.punctured 0)) numeratorValue denominatorValue

def notEquivalent : Prop := ¬ (
  OneSided.approachEventuallyValue domain (.punctured 0) (fun x => denominatorValue x ≠ 0) ∧
  RelativeLimit.relativePuncturedLimitValue
    (fun x => numeratorValue x / denominatorValue x) domain 0 1)

def denominatorNonzero : Prop := ∀ x ∈ domain, denominatorValue x ≠ 0

def denominatorEventuallyNonzero : Prop :=
  OneSided.approachEventuallyValue domain (.punctured 0) (fun x => denominatorValue x ≠ 0)

end Specs.SingleVariableAnalysis.Ch02.DomainZeros
