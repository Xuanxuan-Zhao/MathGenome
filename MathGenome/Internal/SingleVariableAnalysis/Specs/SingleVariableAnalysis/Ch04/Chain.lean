import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specification of K03.04.chain, paper.tex:695–707.
The inner map and both increments are real; the outer target can in particular
be ℝ or ℂ. Domain functions are represented by ambient extensions, using the
upstream domain-restricted difference quotient. Interiority is the chapter's
ordinary-derivative convention. No avoidance of f(a) is assumed.

The local mapping hypothesis is retained explicitly. It is also a consequence
of the inner derivative and the outer interior hypothesis. The scalar results
assert existence of the composite derivative as well as its value; thus total
`deriv` does not supply an existence assumption.
-/
namespace Specs.SingleVariableAnalysis.Ch04.Chain

open scoped Topology
universe u

def incrementDerivativeChain : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → ℝ) (g : ℝ → F) (f' a : ℝ) (g' : F),
    Derivative.hasRealIncrementDerivativeValue f f' a →
    Derivative.hasRealIncrementDerivativeValue g g' (f a) →
    Derivative.hasRealIncrementDerivativeValue (g ∘ f) (f' • g') a

def withinDerivativeChain : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → ℝ) (g : ℝ → F) (I J : Set ℝ) (f' a : ℝ) (g' : F),
    a ∈ interior I → f a ∈ interior J →
    (∀ᶠ x in 𝓝 a, f x ∈ J) →
    Derivative.hasRealIncrementDerivativeWithinValue f f' I a →
    Derivative.hasRealIncrementDerivativeWithinValue g g' J (f a) →
    Derivative.hasRealIncrementDerivativeWithinValue (g ∘ f) (f' • g') I a ∧
      HasDerivAt (g ∘ f) (f' • g') a

def realChain : Prop :=
  ∀ (f g : ℝ → ℝ) (I J : Set ℝ) (f' g' a : ℝ),
    a ∈ interior I → f a ∈ interior J →
    (∀ᶠ x in 𝓝 a, f x ∈ J) →
    Derivative.hasRealIncrementDerivativeWithinValue f f' I a →
    Derivative.hasRealIncrementDerivativeWithinValue g g' J (f a) →
    Derivative.hasRealIncrementDerivativeWithinValue (g ∘ f) (g' * f') I a ∧
      deriv (g ∘ f) a = g' * f'

def complexChain : Prop :=
  ∀ (f : ℝ → ℝ) (g : ℝ → ℂ) (I J : Set ℝ) (f' a : ℝ) (g' : ℂ),
    a ∈ interior I → f a ∈ interior J →
    (∀ᶠ x in 𝓝 a, f x ∈ J) →
    Derivative.hasRealIncrementDerivativeWithinValue f f' I a →
    Derivative.hasRealIncrementDerivativeWithinValue g g' J (f a) →
    Derivative.hasRealIncrementDerivativeWithinValue (g ∘ f) (g' * (f' : ℂ)) I a ∧
      deriv (g ∘ f) a = g' * (f' : ℂ)

end Specs.SingleVariableAnalysis.Ch04.Chain
