import MathGenome.Internal.Specs.D07.Ch12.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
Independent specification for K07.12.simple_classification,
paper.tex:3623–3629 (chapters/M07.12.tex:82–88).

The specified embedding is `Algebra K L`. The generated field is the same
`IntermediateField.adjoin K {α}` as in the upstream Specs. `AdjoinRoot f`
is defined as `Polynomial K ⧸ Ideal.span {f}`, and `AdjoinRoot.mk f` is its
quotient map. `RatFunc K` is the fraction field of the formal polynomial ring.
Both equivalences preserve K, send the class/image of X to α, and are uniquely
determined by this condition. Their formulas specify evaluation on all
polynomial classes and all fractions with nonzero polynomial denominator.

Only the displayed element is assumed algebraic or transcendental. No
finiteness, algebraicity, or algebraic closedness of the ambient extension
is assumed, and the base and ambient fields may have different universes.
-/

universe u v

namespace Specs.D07.Ch12.SimpleClassification

/-- Evaluation identifies the quotient by the minimal polynomial with the
simple intermediate field. The image of X determines the isomorphism. -/
def AlgebraicClassification : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α →
      ∃ e : AdjoinRoot (minpoly K α) ≃ₐ[K] IntermediateField.adjoin K {α},
        e (AdjoinRoot.root (minpoly K α)) = IntermediateField.AdjoinSimple.gen K α ∧
        (∀ p : Polynomial K,
          (e (AdjoinRoot.mk (minpoly K α) p) : L) = Polynomial.aeval α p) ∧
        ∀ e' : AdjoinRoot (minpoly K α) ≃ₐ[K] IntermediateField.adjoin K {α},
          e' (AdjoinRoot.root (minpoly K α)) = IntermediateField.AdjoinSimple.gen K α →
          e' = e

/-- At a transcendental element, evaluation identifies the rational function
field with the simple intermediate field, uniquely with X sent to α. -/
def TranscendentalClassification : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    Transcendental K α →
      ∃ e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {α},
        e RatFunc.X = IntermediateField.AdjoinSimple.gen K α ∧
        (∀ p q : Polynomial K, q ≠ 0 →
          (e (algebraMap (Polynomial K) (RatFunc K) p /
            algebraMap (Polynomial K) (RatFunc K) q) : L) =
            Polynomial.aeval α p / Polynomial.aeval α q) ∧
        ∀ e' : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {α},
          e' RatFunc.X = IntermediateField.AdjoinSimple.gen K α → e' = e

end Specs.D07.Ch12.SimpleClassification
