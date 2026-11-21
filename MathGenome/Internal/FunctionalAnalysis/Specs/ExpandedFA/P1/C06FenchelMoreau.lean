import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! Independent propositions for Theorem `fa2:p1:c06:fenchel-moreau (paper.tex:1287–1344)`.
The original function has values in ℝ ∪ {+∞}; its conjugates have values
in EReal. Convexity is the finite-endpoint inequality, including zero
weights. Properness includes exclusion of −∞ and a nonempty finite domain.
Weak-star closedness uses the native `WeakDual` topology σ(E′,E),
the coarsest topology making all evaluations continuous. The canonical
linear equivalence `WeakDual.toStrongDual` preserves every value f(x).
No completeness or interior assumption is imposed. -/
namespace ExpandedFA.P1.C06FenchelMoreau.Spec
open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates.Spec ExpandedFA.P1.ExtendedConvexFunctions.Spec

def FenchelInequality : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E), ProperValue E φ →
    ∀ (x : E) (f : E →L[ℝ] ℝ),
      (f x : EReal) ≤ ExtendedRealValueValue (φ x) + ConvexConjugateValue E φ f

def ConjugateProper : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E), ProperValue E φ → ExtendedConvexValue E φ →
    LowerSemicontinuousValue E φ →
    (∀ f : E →L[ℝ] ℝ, ConvexConjugateValue E φ f ≠ ⊥) ∧
      ∃ (f : E →L[ℝ] ℝ) (r : ℝ), ConvexConjugateValue E φ f = (r : EReal)

/-- Convexity holds for every proper input, without regularity assumptions. -/
def ConjugateConvex : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E), ProperValue E φ →
    ∀ (f g : E →L[ℝ] ℝ) (r s a b : ℝ),
      ConvexConjugateValue E φ f = (r : EReal) →
      ConvexConjugateValue E φ g = (s : EReal) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      ConvexConjugateValue E φ (a • f + b • g) ≤ ((a * r + b * s : ℝ) : EReal)

/-- All real sublevels are closed in the specified weak-star topology. -/
def ConjugateWeakStarLowerSemicontinuous : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E), ProperValue E φ → ∀ r : ℝ,
    IsClosed {f : WeakDual ℝ E |
      ConvexConjugateValue E φ (WeakDual.toStrongDual f) ≤ (r : EReal)}

def BiconjugateEquality : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E), ProperValue E φ → ExtendedConvexValue E φ →
    LowerSemicontinuousValue E φ →
    ∀ x : E, ConvexBiconjugateValue E φ x = ExtendedRealValueValue (φ x)

end ExpandedFA.P1.C06FenchelMoreau.Spec
