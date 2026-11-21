import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.ProperIntegralEquality
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.Order.Field

/-! The precise alternating harmonic step function in paper.tex:5152–5167.
The floor is the natural floor, so its quotient is zero below one, including
at negative arguments. All Lebesgue integrals use completed Borel volume.
The improper limit quantifies over arbitrary real upper endpoints and uses
the original Darboux integral, never a totalized nonintegrable scalar integral. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Specs.D11.Ch16.ConditionalImproperCounterexample

def stepFunction_type := ℝ → ℝ

def stepFunction_value : stepFunction_type := fun x =>
  (-1 : ℝ) ^ ⌊x⌋₊ / (⌊x⌋₊ : ℝ)

local notation "mL" => Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)
local notation "μL" => Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)

def exact_values : Prop :=
  (∀ x : ℝ, x < 1 → stepFunction_value x = 0) ∧
  ∀ (n : ℕ), 1 ≤ n → ∀ x ∈ Ico (n : ℝ) ((n : ℝ) + 1),
    stepFunction_value x = (-1 : ℝ) ^ n / (n : ℝ)

def local_riemann_integrable : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue stepFunction_value a b

def improper_converges : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℝ, A ≤ R →
      ∀ hR : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
        stepFunction_value 0 R,
      |Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue stepFunction_value hR - L| < ε

def divergent_parts : Prop :=
  @Measurable ℝ ℝ mL (borel ℝ) stepFunction_value ∧
  @Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ℝ mL
    ((μL).restrict (Ici 0)) (fun x => ENNReal.ofReal |stepFunction_value x|) = ∞ ∧
  @Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ℝ mL
    ((μL).restrict (Ici 0)) (fun x => ENNReal.ofReal
      (Specs.D11.Ch06.ScalarIntegral.positivePart_value stepFunction_value x)) = ∞ ∧
  @Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ℝ mL
    ((μL).restrict (Ici 0)) (fun x => ENNReal.ofReal
      (Specs.D11.Ch06.ScalarIntegral.negativePart_value stepFunction_value x)) = ∞

def not_scalar_integrable : Prop :=
  ¬ @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ ℝ mL _
    (borel ℝ) inferInstance ((μL).restrict (Ici 0)) stepFunction_value

end Specs.D11.Ch16.ConditionalImproperCounterexample
