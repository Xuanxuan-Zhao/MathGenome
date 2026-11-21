import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-! K03.10.p_test, paper.tex:3007–3033. All integrals below are limits of
proper Darboux integrals. Only positive bases are sampled; no integrand
value at the singular point zero is used. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch10.PTest
open Ch07.RealPowers Ch07.LogConstruction Ch10.OneEndpoint

def powerInfinityIff : Prop := ∀ p : ℝ,
  rightConvergesValue .real (fun x => realPowerValue x (-p)) 1 ⊤ ↔ 1 < p

def powerInfinityValue : Prop := ∀ p : ℝ, 1 < p →
  rightHasIntegralValue .real (fun x => realPowerValue x (-p)) 1 ⊤ (1 / (p - 1))

def powerInfinityDivergence : Prop := ∀ p : ℝ, p ≤ 1 →
  rightDivergesPosValue (fun x => realPowerValue x (-p)) 1 ⊤

def powerZeroIff : Prop := ∀ p : ℝ,
  leftConvergesValue .real (fun x => realPowerValue x (-p)) (0 : WithBot ℝ) 1 ↔ p < 1

def powerZeroValue : Prop := ∀ p : ℝ, p < 1 →
  leftHasIntegralValue .real (fun x => realPowerValue x (-p)) (0 : WithBot ℝ) 1
    (1 / (1 - p))

def powerZeroDivergence : Prop := ∀ p : ℝ, 1 ≤ p →
  leftDivergesPosValue (fun x => realPowerValue x (-p)) (0 : WithBot ℝ) 1

def logarithmicIff : Prop := ∀ A : ℝ, 1 < A → ∀ q : ℝ,
  rightConvergesValue .real (fun x => 1 / (x * realPowerValue (seriesLogValue x) q))
    A ⊤ ↔ 1 < q

/-- Proper power and logarithmic truncation formulas, including p = 1. -/
def powerTruncations : Prop := ∀ (p u v : ℝ), 0 < u → u < v →
  ∃ h : Ch08.Integral.realIntegrableValue (fun x => realPowerValue x (-p)) u v,
    Ch08.Integral.realIntegralValue _ h =
      if p = 1 then seriesLogValue v - seriesLogValue u
      else (realPowerValue v (1-p) - realPowerValue u (1-p)) / (1-p)

end Specs.SingleVariableAnalysis.Ch10.PTest
