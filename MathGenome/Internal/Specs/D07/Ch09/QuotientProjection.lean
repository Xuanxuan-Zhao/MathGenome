import MathGenome.Internal.Specs.D07.Ch09.QuotientConstruction
import Mathlib.RingTheory.Ideal.Maps

/-!
Independent specifications for K07.09.quotient_projection,
paper.tex:1534–1545. The quotient and its classes are exactly those in
`QuotientConstruction`: `Ideal.Quotient.mk I a` is the additive coset of `a`.
Rings are associative and unital, with no commutativity or nontriviality
assumption, and `I` is two-sided but need not be proper.
-/

universe u

namespace Specs.D07.Ch09.QuotientProjection

/-- The natural class map is a unital ring homomorphism: it preserves
addition, multiplication, and one (and hence also zero and negatives). -/
def ProjectionHomomorphism : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    (∀ a b : R, Ideal.Quotient.mk I (a + b) =
      Ideal.Quotient.mk I a + Ideal.Quotient.mk I b) ∧
    (∀ a b : R, Ideal.Quotient.mk I (a * b) =
      Ideal.Quotient.mk I a * Ideal.Quotient.mk I b) ∧
    Ideal.Quotient.mk I 1 = 1 ∧
    Ideal.Quotient.mk I 0 = 0 ∧
    (∀ a : R, Ideal.Quotient.mk I (-a) = -(Ideal.Quotient.mk I a))

/-- Every additive coset has a representative in the original ring. -/
def ProjectionSurjective : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    Function.Surjective (Ideal.Quotient.mk I)

/-- Equality of ideals, not just containment of the ideal in the kernel. -/
def ProjectionKernel : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    RingHom.ker (Ideal.Quotient.mk I) = I

def QuotientEqIffSubMem : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided] (a b : R),
    Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ a - b ∈ I

def QuotientZeroIffMem : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided] (a : R),
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I

/-- Every two-sided ideal is the kernel of a surjective unital ring map
into a ring; the target is allowed to be the zero ring. -/
def EveryTwoSidedIdealIsKernel : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    ∃ (S : Type u) (_ : Ring S) (f : R →+* S),
      Function.Surjective f ∧ RingHom.ker f = I

end Specs.D07.Ch09.QuotientProjection
