import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Alternating
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.IntegralTest

/-! K03.11.acceleration, paper.tex:1168–1190. Index `n=0` represents
n=1 in the paper. A corrected approximation has exactly N terms and
includes the initial constant 2. All series below are ordinary limits. -/
namespace SingleVariableAnalysis

noncomputable def reciprocalSquareTerm (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)^2

noncomputable def reciprocalSquareCorrection (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)^2 - 1 / ((n : ℝ) + 1 - 1/2) +
    1 / ((n : ℝ) + 1 + 1/2)

end SingleVariableAnalysis

namespace Specs.SingleVariableAnalysis.Ch11.Acceleration
open scoped BigOperators
open PartialSums Ch10.OneEndpoint
open _root_.SingleVariableAnalysis

def alternatingRemainder : Prop := Alternating.alternatingSeriesRemainder

def integralTailBounds : Prop :=
  ∀ f : ℝ → ℝ, (∀ x, 1 ≤ x → 0 ≤ f x) → AntitoneOn f (Set.Ici 1) →
    rightConvergesValue .real f 1 ⊤ → ∀ N : ℕ, 1 ≤ N →
    ∃ R : ℝ, realSeriesHasSumValue (fun n => f ((N : ℝ) + 1 + (n : ℝ))) R ∧
      ∃ (hN : rightConvergesValue .real f (N : ℝ) ⊤)
        (hN1 : rightConvergesValue .real f ((N : ℝ) + 1) ⊤),
        (show ℝ from rightIntegralValue .real f ((N : ℝ) + 1) ⊤ hN1) ≤ R ∧
        R ≤ (show ℝ from rightIntegralValue .real f (N : ℝ) ⊤ hN)

def correctedConvergence : Prop :=
  realSeriesConvergesValue reciprocalSquareTerm ∧
  realSeriesConvergesValue reciprocalSquareCorrection ∧
  realSeriesConvergesValue (fun n => |reciprocalSquareCorrection n|)

def correctedIdentity : Prop :=
  ∀ S C : ℝ, realSeriesHasSumValue reciprocalSquareTerm S →
    realSeriesHasSumValue reciprocalSquareCorrection C → S = 2 + C

def correctedError : Prop :=
  ∀ S : ℝ, realSeriesHasSumValue reciprocalSquareTerm S → ∀ N : ℕ, 1 ≤ N →
    |S - (2 + ∑ n ∈ Finset.range N, reciprocalSquareCorrection n)| ≤
      1 / (9 * (N : ℝ)^3)

end Specs.SingleVariableAnalysis.Ch11.Acceleration
