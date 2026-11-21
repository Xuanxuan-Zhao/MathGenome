import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-!
Independent specification for K03.02.growth_scale, paper.tex:465–475.
The powers, logarithm and exponential are the Chapter 7 constructions.
The filter `atTop` expresses the real approach to positive infinity.
Eventually `x > 1`, so both bases `x` and `log x` are positive; no
interpretation of a power at a nonpositive base is required by these claims.
The exponents are fixed real numbers, including zero.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch02.GrowthScale

open Filter

def logPowerLittleOPower : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ ε : ℝ, 0 < ε →
    BigO.scalarLittleOValue atTop
      (fun x : ℝ => Ch07.RealPowers.realPowerValue (Ch07.LogConstruction.seriesLogValue x) m)
      (fun x : ℝ => Ch07.RealPowers.realPowerValue x ε)

def powerLittleOExp : Prop :=
  ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 < c →
    BigO.scalarLittleOValue atTop
      (fun x : ℝ => Ch07.RealPowers.realPowerValue x k)
      (fun x : ℝ => Ch07.ExpConstruction.realSeriesExpValue (c * x))

end Specs.SingleVariableAnalysis.Ch02.GrowthScale
