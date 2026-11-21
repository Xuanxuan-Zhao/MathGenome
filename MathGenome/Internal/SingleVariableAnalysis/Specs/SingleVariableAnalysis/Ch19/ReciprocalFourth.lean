import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.QuadraticFourier
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Parseval

/-! K03.19.examples, paper.tex:5049–5055. The norm is the proper Darboux
integral of the actual continuous periodic quadratic. Positive integers are
indexed by k+1; the series conclusion asserts convergence as well as its value. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.ReciprocalFourth
open Ch08.Integral QuadraticFourier
open scoped BigOperators

def normIntegral : Prop :=
  ∃ h : realIntegrableValue (fun x => |quadraticValue x| ^ 2) (-Real.pi) Real.pi,
    realIntegralValue _ h = 2 * Real.pi ^ 5 / 5 ∧
    (1 / (2 * Real.pi)) * realIntegralValue _ h = Real.pi ^ 4 / 5

def parsevalIdentity : Prop :=
  Real.pi ^ 4 / 5 = Real.pi ^ 4 / 9 +
    8 * ∑' k : ℕ, 1 / (((k+1 : ℕ) : ℝ) ^ 4)

def reciprocalFourthSum : Prop :=
  HasSum (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ) ^ 4)) (Real.pi ^ 4 / 90)

def reciprocalFourthTsum : Prop :=
  (∑' k : ℕ, 1 / (((k+1 : ℕ) : ℝ) ^ 4)) = Real.pi ^ 4 / 90

end Specs.SingleVariableAnalysis.Ch19.ReciprocalFourth
