import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specification of K03.04.product, paper.tex:680–695.
The input is real, including for complex-valued functions. The real normed
field algebra formulation includes the canonical targets ℝ and ℂ. Only
pointwise differentiability is required; no continuity of derivatives is assumed.
Functions on an interval use the established ambient-extension representation
and an interior base point. Nonvanishing is asserted on a positive-radius,
unpunctured neighborhood, with the lower modulus bound used in the source proof.
-/

namespace Specs.SingleVariableAnalysis.Ch04.Product

universe u

/-- Product rule, including existence of the derivative. -/
def incrementDerivativeMul : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (f g : ℝ → K) (L M : K) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a →
    Derivative.hasRealIncrementDerivativeValue g M a →
    Derivative.hasRealIncrementDerivativeValue (fun x => f x * g x)
      (L * g a + f a * M) a

def incrementDerivativeInv : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (g : ℝ → K) (M : K) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue g M a → g a ≠ 0 →
    Derivative.hasRealIncrementDerivativeValue (fun x => 1 / g x) (-M / g a ^ 2) a

def incrementDerivativeDiv : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (f g : ℝ → K) (L M : K) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a →
    Derivative.hasRealIncrementDerivativeValue g M a → g a ≠ 0 →
    Derivative.hasRealIncrementDerivativeValue (fun x => f x / g x)
      ((L * g a - f a * M) / g a ^ 2) a

def derivMul : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (f g : ℝ → K) (a : ℝ),
    DifferentiableAt ℝ f a → DifferentiableAt ℝ g a →
    deriv (fun x => f x * g x) a = deriv f a * g a + f a * deriv g a

def derivInv : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (g : ℝ → K) (a : ℝ), DifferentiableAt ℝ g a → g a ≠ 0 →
    deriv (fun x => 1 / g x) a = -deriv g a / g a ^ 2

def derivDiv : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (f g : ℝ → K) (a : ℝ),
    DifferentiableAt ℝ f a → DifferentiableAt ℝ g a → g a ≠ 0 →
    deriv (fun x => f x / g x) a =
      (deriv f a * g a - f a * deriv g a) / g a ^ 2

def incrementDerivativeLocalNonzero : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (g : ℝ → K) (M : K) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue g M a → g a ≠ 0 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - a| < δ →
      ‖g a‖ / 2 ≤ ‖g x‖ ∧ g x ≠ 0

def withinDerivativeMul : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (f g : ℝ → K) (L M : K) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a →
    Derivative.hasRealIncrementDerivativeWithinValue g M I a →
    Derivative.hasRealIncrementDerivativeWithinValue (fun x => f x * g x)
      (L * g a + f a * M) I a

def withinDerivativeInv : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (g : ℝ → K) (M : K) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue g M I a → g a ≠ 0 →
    Derivative.hasRealIncrementDerivativeWithinValue (fun x => 1 / g x)
      (-M / g a ^ 2) I a

def withinDerivativeDiv : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (f g : ℝ → K) (L M : K) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a →
    Derivative.hasRealIncrementDerivativeWithinValue g M I a → g a ≠ 0 →
    Derivative.hasRealIncrementDerivativeWithinValue (fun x => f x / g x)
      ((L * g a - f a * M) / g a ^ 2) I a

def withinDerivativeLocalNonzero : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (g : ℝ → K) (M : K) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue g M I a → g a ≠ 0 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ I, |x - a| < δ →
      ‖g a‖ / 2 ≤ ‖g x‖ ∧ g x ≠ 0

end Specs.SingleVariableAnalysis.Ch04.Product
