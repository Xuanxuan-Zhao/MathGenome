import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos

/-!
Independent specification for K03.07.trig_properties, paper.tex:1668–1697.
Every argument is real. S and C are the factorial-series functions fixed in
the upstream specification, rather than arbitrary solutions of an ODE.
The bounds hold on all of ℝ, including zero and negative inputs.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.TrigProperties

open Ch07.SinCos

def sineOdd : Prop :=
  ∀ x : ℝ, realSeriesSinValue (-x) = -realSeriesSinValue x

def cosineEven : Prop :=
  ∀ x : ℝ, realSeriesCosValue (-x) = realSeriesCosValue x

def sineAddition : Prop := ∀ x y : ℝ,
  realSeriesSinValue (x + y) =
    realSeriesSinValue x * realSeriesCosValue y +
      realSeriesCosValue x * realSeriesSinValue y

def cosineAddition : Prop := ∀ x y : ℝ,
  realSeriesCosValue (x + y) =
    realSeriesCosValue x * realSeriesCosValue y -
      realSeriesSinValue x * realSeriesSinValue y

def pythagoreanIdentity : Prop :=
  ∀ x : ℝ, realSeriesSinValue x ^ 2 + realSeriesCosValue x ^ 2 = 1

def sineBound : Prop := ∀ x : ℝ, |realSeriesSinValue x| ≤ 1

def cosineBound : Prop := ∀ x : ℝ, |realSeriesCosValue x| ≤ 1

def sineAbsoluteBound : Prop := ∀ x : ℝ, |realSeriesSinValue x| ≤ |x|

def cosineQuadraticBound : Prop :=
  ∀ x : ℝ, |realSeriesCosValue x - 1| ≤ x ^ 2 / 2

end Specs.SingleVariableAnalysis.Ch07.TrigProperties
