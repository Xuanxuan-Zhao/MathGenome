import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
Independent specifications for K07.10.pid_ufd, paper.tex:2002–2018.
The PID predicate is the upstream domain-and-principal-ideals predicate.
The explicit factorization conclusion records existence and uniqueness up
to units and reordering, retaining multiplicities and allowing empty products.

The Euclidean consequence uses exactly the source's well-founded remainder
relation and existential division property. In particular, it imposes no
multiplicative monotonicity condition on that relation.
-/

universe u

namespace Specs.D07.Ch10.PidUfd

/-- The usual factorization conclusion, without any normalization of units.
Existence is required for every nonzero element (including units), while
uniqueness matches occurrences of irreducibles, not merely sets of factors. -/
def FactorizationProperty (R : Type u) [CommRing R] : Prop :=
  (∀ a : R, a ≠ 0 → ∃ f : Multiset R,
    (∀ p ∈ f, Irreducible p) ∧ Associated f.prod a) ∧
  (∀ f g : Multiset R,
    (∀ p ∈ f, Irreducible p) → (∀ q ∈ g, Irreducible q) →
    Associated f.prod g.prod →
    f.card = g.card ∧ Multiset.Rel Associated f g)

/-- Every PID is a UFD, both as the standard library class and with the
full finite-factorization conclusion displayed explicitly. Nontriviality
and the domain laws are already included in the PID hypothesis. -/
def PIDIsUFD : Prop :=
  ∀ (R : Type u) [CommRing R], PidDefinition.pidPredicateValue R →
    UniqueFactorizationMonoid R ∧ FactorizationProperty R

/-- Every Euclidean domain in the sense stated in the paper is a UFD.
The domain and commutativity assumptions are the chapter's standing ones.
Quotients and remainders need neither be unique nor be supplied by an algorithm. -/
def EuclideanIsUFD : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (r : R → R → Prop),
    WellFounded r →
    (∀ a b : R, b ≠ 0 → ∃ q t : R,
      a = q * b + t ∧ (t = 0 ∨ r t b)) →
    UniqueFactorizationMonoid R ∧ FactorizationProperty R

end Specs.D07.Ch10.PidUfd
