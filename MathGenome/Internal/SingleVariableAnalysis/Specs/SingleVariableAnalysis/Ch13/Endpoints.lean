import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries

/-!
Independent propositions for K03.13.endpoints, paper.tex:1382–1385.
All series have real coefficients and center zero. The coefficients 1/n
and 1/n² have value zero at degree zero (division by zero in ℝ), so
these are exactly the series starting at n=1. Convergence means an
ordinary limit of inclusive partial sums, including conditional sums.
The reflected coefficients (-1)^n/n represent substitution x ↦ -x.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Endpoints
open Specs.SingleVariableAnalysis.Ch13.PowerSeries
open scoped ENNReal

def geometricRadius : Prop :=
  realPowerSeriesRadiusValue (fun _ => 1) = 1

def harmonicRadius : Prop :=
  realPowerSeriesRadiusValue (fun n => 1 / (n : ℝ)) = 1

def reciprocalSquareRadius : Prop :=
  realPowerSeriesRadiusValue (fun n => 1 / (n : ℝ)^2) = 1

def reflectedHarmonicRadius : Prop :=
  realPowerSeriesRadiusValue (fun n => (-1 : ℝ)^n / (n : ℝ)) = 1

def geometricEndpoints : Prop :=
  ¬ RealPowerSeriesConvergesValue (fun _ => 1) 0 (-1) ∧
  ¬ RealPowerSeriesConvergesValue (fun _ => 1) 0 1

def harmonicEndpoints : Prop :=
  RealPowerSeriesConvergesValue (fun n => 1 / (n : ℝ)) 0 (-1) ∧
  ¬ RealPowerSeriesConvergesValue (fun n => 1 / (n : ℝ)) 0 1 ∧
  ¬ RealPowerSeriesAbsolutelyConvergesValue (fun n => 1 / (n : ℝ)) 0 (-1)

def reciprocalSquareEndpoints : Prop :=
  RealPowerSeriesAbsolutelyConvergesValue (fun n => 1 / (n : ℝ)^2) 0 (-1) ∧
  RealPowerSeriesAbsolutelyConvergesValue (fun n => 1 / (n : ℝ)^2) 0 1

def reflectedHarmonicEndpoints : Prop :=
  RealPowerSeriesConvergesValue (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 1 ∧
  ¬ RealPowerSeriesConvergesValue (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 (-1) ∧
  ¬ RealPowerSeriesAbsolutelyConvergesValue
    (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 1

end Specs.SingleVariableAnalysis.Ch13.Endpoints
