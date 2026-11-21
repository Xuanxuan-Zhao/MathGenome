import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented

/-! K03.07.log_derivative and the integral comparison in
K03.07.construction_bridges. The logarithm is the inverse of the factorial
series exponential, and the integral is the proper oriented Darboux integral.
The witnesses below assert integrability, rather than assuming it. -/
namespace Specs.SingleVariableAnalysis.Ch07.LogIntegral
open Specs.SingleVariableAnalysis.Ch08

/-- Reciprocal integrability on every positive compact interval, including
singletons. -/
def reciprocalIntegrable : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → Integral.realIntegrableValue (fun t => 1 / t) a b

/-- A primitive of the reciprocal on a positive interval containing 1 agrees
with the inverse logarithm after subtraction of its value at 1. Only interior
derivatives are required; continuity handles any included endpoints. -/
def primitiveComparison : Prop :=
  ∀ (F : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → I ⊆ Set.Ioi 0 → 1 ∈ I →
    ContinuousOn F I →
    (∀ t ∈ interior I, HasDerivAt F (1 / t) t) →
    ∀ x ∈ I, F x - F 1 = LogConstruction.seriesLogValue x

/-- The integral exists in either orientation and equals the originally
constructed logarithm at every positive argument. -/
def integralComparison : Prop :=
  ∀ x : ℝ, 0 < x →
    ∃ h : Oriented.realIntegrableValue (fun t => 1 / t) 1 x,
      LogConstruction.seriesLogValue x = Oriented.realIntegralValue (fun t => 1 / t) h

end Specs.SingleVariableAnalysis.Ch07.LogIntegral
