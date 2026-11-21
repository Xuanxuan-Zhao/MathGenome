import MathGenome.Internal.Specs.D07.Ch10.UfdDefinition
import MathGenome.Internal.Specs.D07.Ch10.PrimeImpliesIrreducible

/-!
Independent statements for K07.10.ufd_prime_irreducible
(paper.tex:2020–2027). The ambient ring is commutative and nontrivial.
`Prime` excludes zero and units and includes divisibility of one factor
of every divisible product. No nonzero assumption is placed on that
product or on its factors.

The first statement uses the paper's existence and uniqueness hypotheses
explicitly, with the conventions of the upstream UFD characterization.
The other statements use its equivalent canonical UFD predicate.
-/

universe u

namespace Specs.D07.Ch10.UfdPrimeIrreducible

/-- Existence and uniqueness of irreducible factorizations imply that
each irreducible element is prime, without assuming a UFD instance. -/
def IrreducibleIsPrimeOfFactorizations : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    (∀ a : R, a ≠ 0 → ¬IsUnit a →
      ∃ s : Multiset R, s ≠ 0 ∧ (∀ p ∈ s, Irreducible p) ∧ s.prod = a) →
    (∀ s t : Multiset R, (∀ p ∈ s, Irreducible p) →
      (∀ p ∈ t, Irreducible p) → Associated s.prod t.prod →
      Multiset.Rel Associated s t) →
    ∀ p : R, Irreducible p → Prime p

def IrreducibleIsPrime : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (p : R), Irreducible p → Prime p

def PrimeIffIrreducible : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (p : R), Prime p ↔ Irreducible p

end Specs.D07.Ch10.UfdPrimeIrreducible
