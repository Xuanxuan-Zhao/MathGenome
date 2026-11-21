import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO

/-!
Independent specification of K03.04.peano (paper.tex:660–671).
Increments are real for both real and complex values. The generic real normed
target includes the two scalar targets without imposing extra hypotheses on them.
Little-o is taken along the punctured real neighborhood of zero. In the domain
version only increments staying in I are tested in the identity; a is interior,
so this gives precisely the same local approximation for any ambient extension.
The real/complex specializations use the previously specified scalar little-o.
-/

namespace Specs.SingleVariableAnalysis.Ch04.Peano

open scoped Topology
universe u

def derivativeIffRemainderLittleO : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a ↔
      Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
        (fun h => f (a + h) - f a - h • L) (fun h : ℝ => h)

def derivativeIffPeano : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a ↔
      ∃ r : ℝ → F, (∀ h : ℝ, f (a + h) = f a + h • L + r h) ∧
        Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => h)

def withinDerivativeInteriorIffPeano : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    (Derivative.hasRealIncrementDerivativeWithinValue f L I a ↔
      ∃ r : ℝ → F, (∀ h : ℝ, a + h ∈ I → f (a + h) = f a + h • L + r h) ∧
        Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => h))

def realDerivativeIffPeano : Prop :=
  ∀ (f : ℝ → ℝ) (L a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a ↔
      ∃ r : ℝ → ℝ, (∀ h : ℝ, f (a + h) = f a + L * h + r h) ∧
        Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => h)

def complexDerivativeIffPeano : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a ↔
      ∃ r : ℝ → ℂ, (∀ h : ℝ, f (a + h) = f a + L * (h : ℂ) + r h) ∧
        Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => (h : ℂ))

def incrementDerivativeContinuousAt : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a → ContinuousAt f a

def withinDerivativeInteriorContinuousAt : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a → ContinuousAt f a

def differentiableAtContinuousAt : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a : ℝ), DifferentiableAt ℝ f a → ContinuousAt f a

/-- Explicit nontrivial one-sided limits: the quotient is 1 on the right and
-1 on the left. Thus this continuous function has no finite derivative. -/
def absZeroCounterexample : Prop :=
  ContinuousAt (abs : ℝ → ℝ) 0 ∧
    Ch02.OneSided.rightRelativeLimitValue
      (Derivative.realIncrementQuotientValue (abs : ℝ → ℝ) 0) Set.univ 0 1 ∧
    Ch02.OneSided.leftRelativeLimitValue
      (Derivative.realIncrementQuotientValue (abs : ℝ → ℝ) 0) Set.univ 0 (-1) ∧
    (1 : ℝ) ≠ -1 ∧
    (¬ ∃ L : ℝ, Derivative.hasRealIncrementDerivativeValue (abs : ℝ → ℝ) L 0) ∧
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0

end Specs.SingleVariableAnalysis.Ch04.Peano
