import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.Euler
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.PiPeriod

/-!
Independent specification of the complex counterexample in K03.05.lagrange,
paper.tex:821. The sine, cosine and π are the upstream series constructions.
The domain is real, including in every derivative statement. The two final
statements rule out both the displacement and secant-slope versions of the
exact mean value theorem on [0, 2π].
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch05.ComplexMvtFailure

open Ch07.SinCos Ch07.PiPeriod

def unitCirclePathType : Type := ℝ → ℂ
def unitCirclePathValue : unitCirclePathType := fun t =>
  (realSeriesCosValue t : ℂ) + Complex.I * (realSeriesSinValue t : ℂ)

def unitCircleVelocityType : Type := ℝ → ℂ
def unitCircleVelocityValue : unitCircleVelocityType := fun t =>
  -(realSeriesSinValue t : ℂ) + Complex.I * (realSeriesCosValue t : ℂ)

def endpointDifference : Prop :=
  unitCirclePathValue (2 * analyticPiValue) - unitCirclePathValue 0 = 0

def realParameterDerivative : Prop := ∀ t : ℝ,
  HasDerivAt unitCirclePathValue (unitCircleVelocityValue t) t

def continuousOnInterval : Prop :=
  ContinuousOn unitCirclePathValue (Set.Icc 0 (2 * analyticPiValue))

def derivativeModulus : Prop := ∀ t : ℝ,
  ‖deriv unitCirclePathValue t‖ = 1

def noMeanValuePoint : Prop :=
  ¬ ∃ c ∈ Set.Ioo 0 (2 * analyticPiValue),
    unitCirclePathValue (2 * analyticPiValue) - unitCirclePathValue 0 =
      deriv unitCirclePathValue c * ((2 * analyticPiValue - 0 : ℝ) : ℂ)

def noMeanValueSlope : Prop :=
  ¬ ∃ c ∈ Set.Ioo 0 (2 * analyticPiValue),
    HasDerivAt unitCirclePathValue
      ((unitCirclePathValue (2 * analyticPiValue) - unitCirclePathValue 0) /
        ((2 * analyticPiValue - 0 : ℝ) : ℂ)) c

end Specs.SingleVariableAnalysis.Ch05.ComplexMvtFailure
