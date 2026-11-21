import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic

/-!
Independent statements for the prime-intersection assertion of Theorem 6.7
(`paper.tex:1100–1101,1110`). The base field is arbitrary. Prime and maximal
ideals are proper by definition. The original algebra may be the zero ring;
in that case there are no prime ideals to which these statements apply.
-/
namespace P103.Specs.Ch06.AffineJacobson

universe u v

/-- The principal localization used in the source is nonzero and remains affine. -/
def localization_nontrivial_finiteTypeType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (P : Ideal A), P.IsPrime → ∀ a : A, a ∉ P →
      Nontrivial (Localization.Away (Ideal.Quotient.mk P a)) ∧
        Algebra.FiniteType k (Localization.Away (Ideal.Quotient.mk P a))

/-- Every element outside a prime is avoided by some maximal ideal above it. -/
def maximal_separationType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (P : Ideal A), P.IsPrime → ∀ a : A, a ∉ P →
      ∃ m : Ideal A, m.IsMaximal ∧ P ≤ m ∧ a ∉ m

/-- The intersection is over all maximal ideals containing the given prime. -/
def prime_eq_intersectionType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (P : Ideal A), P.IsPrime →
      P = sInf {m : Ideal A | P ≤ m ∧ m.IsMaximal}

end P103.Specs.Ch06.AffineJacobson
