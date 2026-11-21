import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ExtendedConvexFunctions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Data.EReal.Operations

/-! Independent specification of Definition `fa2:p1:c06:conjugates`, paper.tex
1276–1286. The input is the shared `ExtendedConvexFunctions.ExtendedFunction E = E → WithTop ℝ`.
Suprema are taken in `EReal`, so unbounded suprema and −∞ contributions
are retained. Properness excludes −∞ from the conjugate, but by itself
does not exclude an identically −∞ biconjugate. No convexity, continuity
of the input function, or completeness of the space is assumed.
-/
namespace ExpandedFA.P1.C06Conjugates.Spec

open ExtendedConvexFunctions

/-- Include the input's half-extended values in the full extended real line. -/
def ExtendedRealValueType := WithTop ℝ → EReal
def ExtendedRealValueValue : ExtendedRealValueType := WithBot.some

/-- The test functions are precisely the continuous real-linear dual. -/
def ConvexConjugateType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ExtendedFunction E → (E →L[ℝ] ℝ) → EReal

noncomputable def ConvexConjugateValue : ConvexConjugateType :=
  fun _ _ _ φ f => ⨆ x, (f x : EReal) - ExtendedRealValueValue (φ x)

def ConvexBiconjugateType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ExtendedFunction E → E → EReal

noncomputable def ConvexBiconjugateValue : ConvexBiconjugateType :=
  fun E _ _ φ x => ⨆ f : E →L[ℝ] ℝ, (f x : EReal) - ConvexConjugateValue E φ f

/-- The representation preserves finite values, +∞, order, and exclusion of −∞. -/
def ExtendedRealValueConventions : Prop :=
  (∀ r : ℝ, ExtendedRealValueValue (r : WithTop ℝ) = (r : EReal)) ∧
  ExtendedRealValueValue ⊤ = ⊤ ∧
  (∀ a : WithTop ℝ, ExtendedRealValueValue a ≠ ⊥) ∧
  (∀ a b : WithTop ℝ, ExtendedRealValueValue a ≤ ExtendedRealValueValue b ↔ a ≤ b)

/-- Subtraction agrees with real subtraction at finite values. In each
supremum a +∞ subtrahend contributes −∞; the minuend is always finite. -/
def SubtractionConventions : Prop :=
  (∀ r s : ℝ,
    (r : EReal) - ExtendedRealValueValue (s : WithTop ℝ) = ((r - s : ℝ) : EReal)) ∧
  (∀ r : ℝ, (r : EReal) - ExtendedRealValueValue ⊤ = ⊥) ∧
  (∀ r : ℝ, (r : EReal) - ⊤ = ⊥)

/-- Nonempty finite domain ensures that every conjugate value is > −∞. -/
def ConjugateNeverBottom : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E), ExtendedConvexFunctions.Spec.ProperValue E φ →
    ∀ f : E →L[ℝ] ℝ, ConvexConjugateValue E φ f ≠ ⊥

/-- The displayed formula is an actual least upper bound, even if unbounded. -/
def ConjugateIsLUB : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (f : E →L[ℝ] ℝ),
    IsLUB (Set.range fun x => (f x : EReal) - ExtendedRealValueValue (φ x))
      (ConvexConjugateValue E φ f)

def BiconjugateIsLUB : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (x : E),
    IsLUB (Set.range fun f : E →L[ℝ] ℝ => (f x : EReal) - ConvexConjugateValue E φ f)
      (ConvexBiconjugateValue E φ x)

end ExpandedFA.P1.C06Conjugates.Spec
