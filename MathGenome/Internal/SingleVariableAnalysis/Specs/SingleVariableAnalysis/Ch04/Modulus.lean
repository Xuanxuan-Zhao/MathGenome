import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specification of K03.04.modulus, paper.tex:757–767.
All inputs and increments are real. Complex absolute values are the canonical
norm on ℂ. The interval statements use the upstream ambient representation
at an interior point, as stipulated at the beginning of Chapter 4. No endpoint
or complex-increment derivative is asserted.
-/

namespace Specs.SingleVariableAnalysis.Ch04.Modulus

def absDerivativePositive : Prop :=
  ∀ a : ℝ, 0 < a → Derivative.hasRealIncrementDerivativeValue (fun x : ℝ => |x|) 1 a

def absDerivativeNegative : Prop :=
  ∀ a : ℝ, a < 0 → Derivative.hasRealIncrementDerivativeValue (fun x : ℝ => |x|) (-1) a

def absNotDifferentiableZero : Prop :=
  ¬ ∃ L : ℝ, Derivative.hasRealIncrementDerivativeValue (fun x : ℝ => |x|) L 0

def modulusDerivativeNonzero : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a → f a ≠ 0 →
    Derivative.hasRealIncrementDerivativeValue (fun x => ‖f x‖)
      ((star (f a) * L).re / ‖f a‖) a

def modulusDerivNonzero : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ), DifferentiableAt ℝ f a → f a ≠ 0 →
    deriv (fun x => ‖f x‖) a = (star (f a) * deriv f a).re / ‖f a‖

def modulusDifferentiableZeroIff : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a → f a = 0 →
    (DifferentiableAt ℝ (fun x => ‖f x‖) a ↔ L = 0)

def modulusDerivativeZero : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f 0 a → f a = 0 →
    Derivative.hasRealIncrementDerivativeValue (fun x => ‖f x‖) 0 a

def withinModulusDerivativeNonzero : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a → f a ≠ 0 →
    Derivative.hasRealIncrementDerivativeWithinValue (fun x => ‖f x‖)
      ((star (f a) * L).re / ‖f a‖) I a

def withinModulusDifferentiableZeroIff : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a → f a = 0 →
    ((∃ M : ℝ, Derivative.hasRealIncrementDerivativeWithinValue
      (fun x => ‖f x‖) M I a) ↔ L = 0)

def withinModulusDerivativeZero : Prop :=
  ∀ (f : ℝ → ℂ) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f 0 I a → f a = 0 →
    Derivative.hasRealIncrementDerivativeWithinValue (fun x => ‖f x‖) 0 I a

end Specs.SingleVariableAnalysis.Ch04.Modulus
