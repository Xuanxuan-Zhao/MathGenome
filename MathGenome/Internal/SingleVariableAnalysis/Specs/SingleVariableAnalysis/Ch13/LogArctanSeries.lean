import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
K03.13.standard_series, paper.tex:1514–1536, logarithm and arctangent portion.
All sums are limits of the ordinary inclusive partial sums, including the
conditionally convergent endpoints. The log index n here denotes source n+1.
The values are the previously constructed inverse logarithm and principal
arctangent; π is the previously constructed analytic π. No assertion about a
logarithm at a nonpositive argument is made.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch13.LogArctanSeries
open Ch07.LogConstruction Ch07.TrigInverses Ch07.PiPeriod
open Ch11.PartialSums Ch01.SequenceLimit

def logSeriesTermType : Type := ℝ → ℕ → ℝ
def logSeriesTermValue : logSeriesTermType :=
  fun x n => (-1 : ℝ)^n * x^(n+1) / (n+1 : ℝ)

def arctanSeriesTermType : Type := ℝ → ℕ → ℝ
def arctanSeriesTermValue : arctanSeriesTermType :=
  fun x n => (-1 : ℝ)^n * x^(2*n+1) / (2*n+1 : ℝ)

def logIdentity : Prop := ∀ x : ℝ, -1 < x → x ≤ 1 →
  realSeriesHasSumValue (logSeriesTermValue x) (seriesLogValue (1+x))

def arctanIdentity : Prop := ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
  realSeriesHasSumValue (arctanSeriesTermValue x) (principalArctanValue x)

def logDomain : Prop := ∀ x : ℝ,
  realSeriesConvergesValue (logSeriesTermValue x) ↔ -1 < x ∧ x ≤ 1

def arctanDomain : Prop := ∀ x : ℝ,
  realSeriesConvergesValue (arctanSeriesTermValue x) ↔ -1 ≤ x ∧ x ≤ 1

def logEndpoint : Prop :=
  realSeriesHasSumValue (logSeriesTermValue 1) (seriesLogValue 2)

def arctanEndpoints : Prop :=
  realSeriesHasSumValue (arctanSeriesTermValue 1) (analyticPiValue/4) ∧
  realSeriesHasSumValue (arctanSeriesTermValue (-1)) (-(analyticPiValue/4))

def logNegativeEndpoint : Prop :=
  divergesToNegInfinityValue (realPartialSumValue (logSeriesTermValue (-1))) ∧
  ¬ realSeriesConvergesValue (logSeriesTermValue (-1))

def logExteriorTermTest : Prop := ∀ x : ℝ, 1 < |x| →
  ¬ realSequenceConvergesValue (logSeriesTermValue x) 0

def arctanExteriorTermTest : Prop := ∀ x : ℝ, 1 < |x| →
  ¬ realSequenceConvergesValue (arctanSeriesTermValue x) 0

def exteriorDivergence : Prop := ∀ x : ℝ, 1 < |x| →
  ¬ realSeriesConvergesValue (logSeriesTermValue x) ∧
  ¬ realSeriesConvergesValue (arctanSeriesTermValue x)

end Specs.SingleVariableAnalysis.Ch13.LogArctanSeries
