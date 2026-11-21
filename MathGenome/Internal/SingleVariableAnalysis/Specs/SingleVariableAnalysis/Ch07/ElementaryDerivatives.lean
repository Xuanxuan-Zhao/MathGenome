import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos

/-!
Independent propositions for K03.07.elementary_derivatives, paper.tex:1809–1826.
The powers, logarithm, sine and cosine are the upstream series constructions.
`HasDerivAt` asserts existence and the value of the real-variable derivative.
Secant, tangent and cotangent are expanded as their defining quotients; all
denominator conditions are retained. The exponent variable of a positive-base
exponential ranges over all of ℝ.
-/
namespace Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives

def powerDerivative : Prop :=
  ∀ (α x : ℝ), 0 < x →
    HasDerivAt (fun t => RealPowers.realPowerValue t α)
      (α * RealPowers.realPowerValue x (α - 1)) x

def exponentialDerivative : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ x : ℝ,
    HasDerivAt (fun t => RealPowers.realPowerValue a t)
      (LogConstruction.seriesLogValue a * RealPowers.realPowerValue a x) x

def secantDerivative : Prop :=
  ∀ x : ℝ, SinCos.realSeriesCosValue x ≠ 0 →
    HasDerivAt (fun t => 1 / SinCos.realSeriesCosValue t)
      ((1 / SinCos.realSeriesCosValue x) *
        (SinCos.realSeriesSinValue x / SinCos.realSeriesCosValue x)) x

def cotangentDerivative : Prop :=
  ∀ x : ℝ, SinCos.realSeriesSinValue x ≠ 0 →
    HasDerivAt (fun t => SinCos.realSeriesCosValue t / SinCos.realSeriesSinValue t)
      (-1 / SinCos.realSeriesSinValue x ^ 2) x

end Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives
