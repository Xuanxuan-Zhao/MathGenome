import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.BinomialInterior

/-! K03.13.binomial, paper.tex:1452–1477. Ordinary convergence is the
inclusive partial-sum limit. The nonterminating endpoint tests exclude precisely
nonnegative integer exponents. Natural exponents use algebraic powers at every
real base; at α=0 the value at -1 is 1. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch13.Binomial
open Ch13.BinomialInterior Ch13.PowerSeries Ch11.PartialSums

def endpointOneConverges : Prop := ∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
  (RealPowerSeriesConvergesValue (binomialCoefficientValue α) 0 1 ↔ -1 < α)

def endpointOneSum : Prop := ∀ α : ℝ, -1 < α →
  RealPowerSeriesHasSumValue (binomialCoefficientValue α) 0 1
    (Ch07.RealPowers.realPowerValue 2 α)

def endpointNegOneConverges : Prop := ∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
  (RealPowerSeriesConvergesValue (binomialCoefficientValue α) 0 (-1) ↔ 0 < α)

def endpointNegOneSum : Prop := ∀ α : ℝ, 0 < α →
  RealPowerSeriesHasSumValue (binomialCoefficientValue α) 0 (-1) 0

def endpointsAbsolute : Prop := ∀ α : ℝ, 0 < α →
  RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue α) 0 1 ∧
  RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue α) 0 (-1)

def endpointOneConditional : Prop := ∀ α : ℝ, -1 < α → α < 0 →
  RealPowerSeriesConvergesValue (binomialCoefficientValue α) 0 1 ∧
  ¬ RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue α) 0 1

def naturalAllArguments : Prop := ∀ (m : ℕ) (x : ℝ),
  (∀ n : ℕ, m < n → binomialCoefficientValue (m : ℝ) n = 0) ∧
  RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue (m : ℝ)) 0 x ∧
  RealPowerSeriesHasSumValue (binomialCoefficientValue (m : ℝ)) 0 x ((1+x)^m)

def naturalEndpoints : Prop := ∀ m : ℕ,
  RealPowerSeriesHasSumValue (binomialCoefficientValue (m : ℝ)) 0 1 ((2 : ℝ)^m) ∧
  RealPowerSeriesHasSumValue (binomialCoefficientValue (m : ℝ)) 0 (-1)
    (if m = 0 then 1 else 0)

/-- Retain the complete interior and radius conclusion from the prerequisite. -/
def interiorAndRadius : Prop :=
  (∀ (α x : ℝ), |x| < 1 → RealPowerSeriesHasSumValue
    (binomialCoefficientValue α) 0 x (Ch07.RealPowers.realPowerValue (1+x) α)) ∧
  (∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
    realPowerSeriesRadiusValue (binomialCoefficientValue α) = 1)
end Specs.SingleVariableAnalysis.Ch13.Binomial
