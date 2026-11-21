import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup

/-! K03.19.riemann_lebesgue, paper.tex:4741–4764 (proper part).
Every integral below is the upstream proper Darboux integral, with its
integrability witness. Real frequencies escape in both directions. The
integer conclusion uses natAbs, so includes both signs of the frequency.
The improper extension is allocated to RiemannLebesgueImproper. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue
open Ch08.Integral
open Ch19.PeriodicSetup

/-- Integrability of every weighted proper integral is a conclusion. -/
def complexRiemannLebesgue : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, complexIntegrableValue f a b →
    ∃ H : ∀ lam : ℝ, complexIntegrableValue
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b,
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ lam : ℝ, R ≤ |lam| →
          ‖complexIntegralValue _ (H lam)‖ < ε

/-- The real scalar case uses the canonical embedding into ℂ. -/
def realRiemannLebesgue : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, realIntegrableValue f a b →
    ∃ H : ∀ lam : ℝ, complexIntegrableValue
      (fun x => (f x : ℂ) * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b,
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ lam : ℝ, R ≤ |lam| →
          ‖complexIntegralValue _ (H lam)‖ < ε

/-- This stronger form needs only integrability on the reference interval.
In particular it applies to every periodic Riemann-integrable function.
All choices of the integrability witnesses give the same coefficients. -/
def complexCoefficientDecay : Prop :=
  ∀ (f : ℝ → ℂ), complexIntegrableValue f (-Real.pi) Real.pi →
    ∀ H : ∀ n : ℤ, complexIntegrableValue
      (fun x => f x * modeValue (-n) x) (-Real.pi) Real.pi,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
        ‖coefficientValue f n (H n)‖ < ε

def realCoefficientDecay : Prop :=
  ∀ (f : ℝ → ℝ), realIntegrableValue f (-Real.pi) Real.pi →
    ∃ H : ∀ n : ℤ, complexIntegrableValue
      (fun x => (f x : ℂ) * modeValue (-n) x) (-Real.pi) Real.pi,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
        ‖coefficientValue (fun x => (f x : ℂ)) n (H n)‖ < ε

end Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue
