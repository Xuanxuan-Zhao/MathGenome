import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! K03.19.coefficient_decay, paper.tex:4879–4901.
Derivatives are real-variable derivatives within the closed reference interval.
`ContDiffOn` imposes no smoothness outside this interval, including at its ends.
Only orders strictly below k have matching endpoint values. The integral is the
proper Darboux integral from Ch08, with explicit existence witnesses.
The last assertion says |n|^k |c_n(f)| → 0 in both integer directions; since
|n| is eventually positive, this is precisely c_n(f) = o(|n|^(-k)). -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.CoefficientDecay
open Ch08.Integral Ch19.PeriodicSetup

def derivativeDecay : Prop :=
  ∀ (f : ℝ → ℂ) (k : ℕ), 1 ≤ k →
    ContDiffOn ℝ k f (Set.Icc (-Real.pi) Real.pi) →
    (∀ j : ℕ, j < k →
      iteratedDerivWithin j f (Set.Icc (-Real.pi) Real.pi) (-Real.pi) =
      iteratedDerivWithin j f (Set.Icc (-Real.pi) Real.pi) Real.pi) →
    ∃ H₀ : ∀ n : ℤ, complexIntegrableValue
      (fun x => f x * modeValue (-n) x) (-Real.pi) Real.pi,
    ∃ Hₖ : ∀ n : ℤ, complexIntegrableValue
      (fun x => iteratedDerivWithin k f (Set.Icc (-Real.pi) Real.pi) x *
        modeValue (-n) x) (-Real.pi) Real.pi,
    ∃ hnorm : realIntegrableValue
      (fun x => ‖iteratedDerivWithin k f (Set.Icc (-Real.pi) Real.pi) x‖)
      (-Real.pi) Real.pi,
      (∀ n : ℤ,
        coefficientValue (iteratedDerivWithin k f (Set.Icc (-Real.pi) Real.pi)) n (Hₖ n) =
          (Complex.I * (n : ℂ)) ^ k * coefficientValue f n (H₀ n)) ∧
      (∀ n : ℤ, n ≠ 0 →
        ‖coefficientValue f n (H₀ n)‖ ≤
          (1 / (2 * Real.pi * |(n : ℝ)| ^ k)) * realIntegralValue _ hnorm) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
        |(n : ℝ)| ^ k * ‖coefficientValue f n (H₀ n)‖ < ε)

end Specs.SingleVariableAnalysis.Ch19.CoefficientDecay
