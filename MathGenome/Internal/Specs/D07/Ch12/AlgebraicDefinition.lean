import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
Independent specification for K07.12.algebraic_definition
(paper.tex:3570–3574; chapters/M07.12.tex:29–33).

We reuse the canonical predicates `IsAlgebraic`, `Transcendental`, and
`Algebra.IsAlgebraic`, rather than introducing competing definitions.
`Algebra K L` specifies the field embedding, and `aeval` evaluates formal
polynomials using that embedding (its underlying formula is
`eval₂ (algebraMap K L) α`). The coefficient field is explicit in every
assertion; neither finite degree nor algebraic closedness is assumed.

The last two statements use the same element `RatFunc.X` of the rational
function field K(t), first over K and then over K(t) with its identity
structure map. Thus the example is in fields, not just polynomial rings.
-/

universe u v

namespace Specs.D07.Ch12.AlgebraicDefinition

/-- Signature of the element predicates, including the chosen embedding. -/
def ElementPredicateType :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], L → Prop

/-- Independently specified value of the algebraic-element predicate. -/
def AlgebraicElementValue : ElementPredicateType.{u, v} :=
  fun K _ _ _ _ α =>
    ∃ f : Polynomial K, f ≠ 0 ∧ Polynomial.aeval α f = 0

/-- Independently specified value of the transcendental-element predicate. -/
def TranscendentalElementValue : ElementPredicateType.{u, v} :=
  fun K _ _ _ _ α =>
    ¬ ∃ f : Polynomial K, f ≠ 0 ∧ Polynomial.aeval α f = 0

/-- Signature of a predicate on field extensions with specified structure maps. -/
def ExtensionPredicateType :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Prop

/-- The canonical algebraicity class. Its sole field asserts algebraicity
of every element; `AlgebraicExtensionCharacterization` unfolds that condition
to the full polynomial-witness formulation. -/
def AlgebraicExtensionValue : ExtensionPredicateType.{u, v} :=
  fun K L _ _ _ => Algebra.IsAlgebraic K L

/-- Algebraicity means the existence of a nonzero annihilating polynomial. -/
def AlgebraicElementCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α ↔
      ∃ f : Polynomial K, f ≠ 0 ∧ Polynomial.aeval α f = 0

/-- Transcendence is the negation of algebraicity over the specified base. -/
def TranscendentalElementCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    Transcendental K α ↔
      ¬ ∃ f : Polynomial K, f ≠ 0 ∧ Polynomial.aeval α f = 0

/-- An extension is algebraic exactly when every element is algebraic. -/
def AlgebraicExtensionCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Algebra.IsAlgebraic K L ↔
      ∀ α : L, ∃ f : Polynomial K, f ≠ 0 ∧ Polynomial.aeval α f = 0

/-- The indeterminate in the rational function field is transcendental over K. -/
def IndeterminateTranscendentalOverBase : Prop :=
  ∀ (K : Type u) [Field K], Transcendental K (RatFunc.X : RatFunc K)

/-- That same element is algebraic over the entire rational function field. -/
def IndeterminateAlgebraicOverRationalFunctions : Prop :=
  ∀ (K : Type u) [Field K],
    IsAlgebraic (RatFunc K) (RatFunc.X : RatFunc K)

end Specs.D07.Ch12.AlgebraicDefinition
