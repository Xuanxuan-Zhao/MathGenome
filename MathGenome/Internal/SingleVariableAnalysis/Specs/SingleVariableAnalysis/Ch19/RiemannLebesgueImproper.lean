import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Absolute

/-! The improper extension in K03.19.riemann_lebesgue, paper.tex:4746–4767.
The endpoints are finite, but no boundedness or endpoint values of f are assumed.
All integrals are the independent-endpoint limits of proper Darboux integrals
specified in Chapter 10. Absolute convergence and existence at every real
frequency are conclusions, followed by decay in both frequency directions. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper
open Ch10.OneEndpoint Ch10.SeveralEndpoints Ch10.Absolute

/-- The complex-valued oscillatory integral on a bounded open interval. -/
def complexRiemannLebesgueImproper : Prop :=
  ∀ (f : ℝ → ℂ) (a b : ℝ),
    locallyIntegrableValue .complex f (a : WithBot ℝ) (b : WithTop ℝ) →
    absoluteValue .complex f (a : WithBot ℝ) (b : WithTop ℝ) →
    ∃ H : ∀ lam : ℝ, convergesValue .complex
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
      (a : WithBot ℝ) (b : WithTop ℝ),
      (∀ lam : ℝ, absoluteValue .complex
        (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
        (a : WithBot ℝ) (b : WithTop ℝ)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ lam : ℝ, R ≤ |lam| →
        ‖integralValue .complex _ (a : WithBot ℝ) (b : WithTop ℝ) (H lam)‖ < ε

/-- Real amplitudes are embedded canonically into ℂ; the input assumptions
are on the original real function and its real absolute integral. -/
def realRiemannLebesgueImproper : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ),
    locallyIntegrableValue .real f (a : WithBot ℝ) (b : WithTop ℝ) →
    absoluteValue .real f (a : WithBot ℝ) (b : WithTop ℝ) →
    ∃ H : ∀ lam : ℝ, convergesValue .complex
      (fun x => (f x : ℂ) * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
      (a : WithBot ℝ) (b : WithTop ℝ),
      (∀ lam : ℝ, absoluteValue .complex
        (fun x => (f x : ℂ) * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
        (a : WithBot ℝ) (b : WithTop ℝ)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ lam : ℝ, R ≤ |lam| →
        ‖integralValue .complex _ (a : WithBot ℝ) (b : WithTop ℝ) (H lam)‖ < ε

end Specs.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper
