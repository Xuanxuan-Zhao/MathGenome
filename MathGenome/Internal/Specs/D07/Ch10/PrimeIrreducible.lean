import Mathlib.Algebra.Prime.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Prime

/-!
Independent specifications for K07.10.prime_irreducible
(paper.tex:1843–1851). The chapter assumes a commutative nontrivial
domain. We use the canonical element predicates, and explicitly compare
their full meanings with the source definitions. In particular, zero
is excluded from both element predicates.

The principal-ideal criterion includes properness through the nonunit
condition. Element primality additionally requires the generator to be
nonzero; primality of the ideal alone does not enforce this.
-/

universe u

namespace Specs.D07.Ch10.PrimeIrreducible

def IrreducibleCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (p : R),
    Irreducible p ↔
      p ≠ 0 ∧ ¬IsUnit p ∧
        ∀ a b : R, p = a * b → IsUnit a ∨ IsUnit b

def PrimeCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (p : R),
    Prime p ↔
      p ≠ 0 ∧ ¬IsUnit p ∧
        ∀ a b : R, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- The ideal criterion retains the nonunit condition, including for `p = 0`. -/
def PrincipalIdealPrimeCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (p : R),
    (Ideal.span {p}).IsPrime ↔
      ¬IsUnit p ∧ ∀ a b : R, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- Unconditional formulation of the source's equivalence for nonzero elements. -/
def PrimeIffNonzeroPrimePrincipalIdeal : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (p : R),
    Prime p ↔ p ≠ 0 ∧ (Ideal.span {p}).IsPrime

/-- The zero ideal is prime in a domain, although zero is neither kind of element. -/
def ZeroBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    ¬Prime (0 : R) ∧ ¬Irreducible (0 : R) ∧
      Ideal.span ({0} : Set R) = ⊥ ∧
      (Ideal.span ({0} : Set R)).IsPrime

end Specs.D07.Ch10.PrimeIrreducible
