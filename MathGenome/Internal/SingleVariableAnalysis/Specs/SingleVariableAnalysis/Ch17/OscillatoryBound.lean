import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic

/-! K03.17.oscillatory_bound, paper.tex:4635–4650.
All integral predicates and values are the upstream proper Darboux ones.
`ContDiffOn ℝ 1` uses real increments and includes the continuous one-sided
endpoint derivatives. `derivWithin` supplies that extension on [a,b].
The interval is ordered, including the degenerate case. -/
namespace Specs.SingleVariableAnalysis.Ch17.OscillatoryBound
open Set
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- The exponential phase has its derivative with respect to a real variable. -/
def phaseDerivative : Prop := ∀ (lam x : ℝ),
  HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (lam : ℂ) * (t : ℂ)))
    (Complex.I * (lam : ℂ) * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) x

/-- Both proper integrals exist as part of the conclusion, not as extra assumptions. -/
def oscillatoryBound : Prop :=
  ∀ (h : ℝ → ℂ) (a b lam : ℝ), a ≤ b →
    ContDiffOn ℝ 1 h (Icc a b) → lam ≠ 0 →
    ∃ _hd : complexIntegrableValue (derivWithin h (Icc a b)) a b,
    ∃ hi : complexIntegrableValue
      (fun x => h x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b,
    ∃ hn : realIntegrableValue (fun x => ‖derivWithin h (Icc a b) x‖) a b,
      ‖complexIntegralValue _ hi‖ ≤
        (‖h a‖ + ‖h b‖ + realIntegralValue _ hn) / |lam|

end Specs.SingleVariableAnalysis.Ch17.OscillatoryBound
