import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Monotone
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Nonnegative

/-! K03.10.integral_test, paper.tex:3031–3052. The function is only
constrained on [1,∞). Series use ordinary inclusive partial-sum limits,
with n=0 representing the first term f(1). All integrals are the shared
proper Darboux truncations and their finite improper limits. -/
namespace Specs.SingleVariableAnalysis.Ch10.IntegralTest
open scoped BigOperators
open OneEndpoint

def localIntegrability : Prop :=
  ∀ (f : ℝ → ℝ), (∀ x, 1 ≤ x → 0 ≤ f x) → AntitoneOn f (Set.Ici 1) →
    ∀ a b : ℝ, 1 ≤ a → a ≤ b → Ch08.Integral.realIntegrableValue f a b

def integralTest : Prop :=
  ∀ (f : ℝ → ℝ), (∀ x, 1 ≤ x → 0 ≤ f x) → AntitoneOn f (Set.Ici 1) →
    (Ch11.PartialSums.realSeriesConvergesValue (fun n => f ((n : ℝ) + 1)) ↔
      rightConvergesValue .real f 1 ⊤)

/-- The remainder is itself an ordinary convergent series, starting at N+1.
The two integrals are required to exist, rather than assigned default values. -/
def remainderBounds : Prop :=
  ∀ (f : ℝ → ℝ), (∀ x, 1 ≤ x → 0 ≤ f x) → AntitoneOn f (Set.Ici 1) →
    Ch11.PartialSums.realSeriesConvergesValue (fun n => f ((n : ℝ) + 1)) →
    ∀ N : ℕ, 1 ≤ N →
      ∃ (R : ℝ), Ch11.PartialSums.realSeriesHasSumValue
        (fun n => f ((N : ℝ) + 1 + (n : ℝ))) R ∧
      ∃ (hN : rightConvergesValue .real f (N : ℝ) ⊤)
        (hN1 : rightConvergesValue .real f ((N : ℝ) + 1) ⊤),
        (show ℝ from rightIntegralValue .real f ((N : ℝ) + 1) ⊤ hN1) ≤ R ∧
        R ≤ (show ℝ from rightIntegralValue .real f (N : ℝ) ⊤ hN)

end Specs.SingleVariableAnalysis.Ch10.IntegralTest
