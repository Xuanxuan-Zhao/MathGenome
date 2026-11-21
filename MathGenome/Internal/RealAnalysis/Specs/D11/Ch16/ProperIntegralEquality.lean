import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.RiemannCriterion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Proper one-dimensional Riemann integrals on ordered finite intervals,
including singletons. The integrand is extended by zero outside the interval.
The Lebesgue structure is explicitly the completion of Borel volume; scalar
integrability includes actual measurability and finite integral of the norm.
The integral value is used only with that integrability proof. -/

open Set MeasureTheory
noncomputable section
namespace Specs.D11.Ch16.ProperIntegralEquality

local notation "mL" => Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)
local notation "μL" => Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)

/-- Absolute integrability and equality for the original bounded real
representative, with no regularity imposed outside `[a,b]`. -/
def real_proper_equality : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ)
    (hR : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a b),
    ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ ℝ mL _
      (borel ℝ) inferInstance μL ((Icc a b).indicator f),
      Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue f hR =
        @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ ℝ mL _
          (borel ℝ) inferInstance μL ((Icc a b).indicator f) hL

/-- The complex Riemann value uses the separate proper integrals of the two
components. No hypothesis about Riemann integrability of a.e. classes is used. -/
def complex_proper_equality : Prop :=
  ∀ (f : ℝ → ℂ) (a b : ℝ)
    (hR : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a b),
    ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ ℂ mL _
      (borel ℂ) inferInstance μL ((Icc a b).indicator f),
      Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue f hR =
        @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ ℂ mL _
          (borel ℂ) inferInstance μL ((Icc a b).indicator f) hL

/-- All values on a singleton are allowed, and both proper integrals are zero. -/
def real_degenerate : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ),
    ∃ hR : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a a,
    ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ ℝ mL _
      (borel ℝ) inferInstance μL ((Icc a a).indicator f),
      Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue f hR = 0 ∧
        @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ ℝ mL _
          (borel ℝ) inferInstance μL ((Icc a a).indicator f) hL = 0

def complex_degenerate : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ),
    ∃ hR : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a a,
    ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ ℂ mL _
      (borel ℂ) inferInstance μL ((Icc a a).indicator f),
      Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue f hR = 0 ∧
        @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ ℂ mL _
          (borel ℂ) inferInstance μL ((Icc a a).indicator f) hL = 0

end Specs.D11.Ch16.ProperIntegralEquality
