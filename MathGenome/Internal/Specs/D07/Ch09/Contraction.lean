import MathGenome.Internal.Specs.D07.Ch09.IdealCorrespondence
import MathGenome.Internal.Specs.D07.Ch09.MaximalQuotient
import MathGenome.Internal.Specs.D07.Ch09.PrimeIdeal
import Mathlib.Algebra.Ring.Hom.Defs

/-!
Independent specifications for K07.09.contraction, paper.tex:1699–1707.
The chapter has assumed commutative rings since paper.tex:1631. Rings
may be trivial; primality and maximality themselves require properness.
`comap` is the actual inverse image under the given unital homomorphism.
The final two statements retain both warnings in the source, using the
specified integer-to-rational inclusion and a nonunital zero map.
-/

universe u v

namespace Specs.D07.Ch09.Contraction

/-- Identify the canonical contraction with its set-theoretic meaning. -/
def ContractionCarrier : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S),
    (I.comap f : Set R) = f ⁻¹' (I : Set S)

/-- Identity preservation guarantees properness of the inverse image. -/
def PrimeContractionProper : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S) (P : Ideal S),
    P.IsPrime → (1 : R) ∉ P.comap f ∧ P.comap f ≠ ⊤

/-- No surjectivity hypothesis is needed for prime ideals. -/
def PrimeContraction : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S) (P : Ideal S),
    P.IsPrime → (P.comap f).IsPrime

/-- Surjectivity does suffice for contraction of a maximal ideal. -/
def MaximalContraction : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S), Function.Surjective f → ∀ M : Ideal S,
    M.IsMaximal → (M.comap f).IsMaximal

/-- The inclusion Z → Q contracts the maximal zero ideal to the
nonmaximal zero ideal, and is injective but not surjective. -/
def IntegerRationalCounterexample : Prop :=
  Function.Injective (Int.castRingHom ℚ) ∧
    ¬ Function.Surjective (Int.castRingHom ℚ) ∧
    (⊥ : Ideal ℚ).IsMaximal ∧
    (⊥ : Ideal ℚ).comap (Int.castRingHom ℚ) = (⊥ : Ideal ℤ) ∧
    ¬ ((⊥ : Ideal ℚ).comap (Int.castRingHom ℚ)).IsMaximal

/-- A map preserving addition and multiplication but not one can have
the whole source as the inverse image of the prime zero ideal of Z. -/
def NonunitalCounterexample : Prop :=
  ∃ f : ℤ →ₙ+* ℤ, f 1 ≠ 1 ∧ (⊥ : Ideal ℤ).IsPrime ∧
    (f : ℤ → ℤ) ⁻¹' (↑(⊥ : Ideal ℤ) : Set ℤ) = Set.univ

end Specs.D07.Ch09.Contraction
