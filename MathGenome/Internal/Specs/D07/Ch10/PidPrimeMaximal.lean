import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import MathGenome.Internal.Specs.D07.Ch10.PrimeIrreducible
import Mathlib.RingTheory.Ideal.Maximal

/-!
Independent specifications for K07.10.pid_prime_maximal,
paper.tex:1946–1963. The PID hypothesis is exactly the upstream predicate:
a commutative nontrivial domain in which every ideal has one generator.
The ideals and element predicates are the canonical objects used upstream.
The subsequent ascending-chain lemma has its own goal, support.pid_ascending_chain.
-/

universe u

namespace Specs.D07.Ch10.PidPrimeMaximal

/-- The zero ideal is excluded; no generator is chosen in the statement. -/
def NonzeroPrimeIdealMaximal : Prop :=
  ∀ (R : Type u) [CommRing R], PidDefinition.pidPredicateValue R →
    ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal

/-- In a PID the two nonzero, nonunit element predicates coincide. -/
def IrreducibleIffPrime : Prop :=
  ∀ (R : Type u) [CommRing R], PidDefinition.pidPredicateValue R →
    ∀ p : R, p ≠ 0 → (Irreducible p ↔ Prime p)

/-- An irreducible element generates a maximal ideal, and conversely. -/
def IrreducibleIffMaximal : Prop :=
  ∀ (R : Type u) [CommRing R], PidDefinition.pidPredicateValue R →
    ∀ p : R, p ≠ 0 → (Irreducible p ↔ (Ideal.span {p}).IsMaximal)

/-- The same maximality criterion for prime elements. -/
def PrimeIffMaximal : Prop :=
  ∀ (R : Type u) [CommRing R], PidDefinition.pidPredicateValue R →
    ∀ p : R, p ≠ 0 → (Prime p ↔ (Ideal.span {p}).IsMaximal)

/-- The source's example showing why the nonzero ideal hypothesis is needed. -/
def IntegerZeroPrimeNotMaximal : Prop :=
  (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal

end Specs.D07.Ch10.PidPrimeMaximal
