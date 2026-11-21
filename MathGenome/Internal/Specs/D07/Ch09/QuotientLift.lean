import MathGenome.Internal.Specs.D07.Ch08.RingHomomorphism
import MathGenome.Internal.Specs.D07.Ch09.QuotientProjection

/-!
Independent specifications for K07.09.quotient_lift,
paper.tex:1556–1569 (Universal factorization).

The source rings are associative and unital, without commutativity or
nontriviality assumptions. The ideal is two-sided but need not be proper.
The quotient and projection are the canonical additive-coset quotient
and `Ideal.Quotient.mk` fixed in the upstream construction and projection
specifications. All maps below are unital ring homomorphisms.
-/

universe u v

namespace Specs.D07.Ch09.QuotientLift

/-- A ring homomorphism factors through the natural projection precisely
when the given ideal is contained in its kernel. -/
def FactorizationIff : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (I : Ideal R) [I.IsTwoSided] (f : R →+* S),
    (∃ g : R ⧸ I →+* S, g.comp (Ideal.Quotient.mk I) = f) ↔
      I ≤ RingHom.ker f

/-- Any two factorizations of the same homomorphism are equal. -/
def FactorizationUnique : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (I : Ideal R) [I.IsTwoSided] (f : R →+* S)
    (g h : R ⧸ I →+* S),
    g.comp (Ideal.Quotient.mk I) = f →
    h.comp (Ideal.Quotient.mk I) = f → g = h

/-- Every factorization has the source's formula on every representative. -/
def FactorizationOnClasses : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (I : Ideal R) [I.IsTwoSided] (f : R →+* S)
    (g : R ⧸ I →+* S),
    g.comp (Ideal.Quotient.mk I) = f →
      ∀ a : R, g (Ideal.Quotient.mk I a) = f a

end Specs.D07.Ch09.QuotientLift
