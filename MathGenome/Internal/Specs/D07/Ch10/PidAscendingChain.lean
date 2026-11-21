import MathGenome.Internal.Specs.D07.Ch10.PidDefinition

/-!
Independent specifications for `support.pid_ascending_chain`, the lemma
`lem:pid-acc` at paper.tex:1965–1976.

The PID hypothesis is the canonical predicate from the preceding definition:
a commutative nontrivial domain in which every ideal is principal. Ideals are
ordered by inclusion. A maximal member of a collection need not be a maximal
proper ideal of the ambient ring.
-/

universe u

namespace Specs.D07.Ch10.PidAscendingChain

/-- Every increasing sequence of ideals in a PID is eventually constant. -/
def AscendingChainsStabilize : Prop :=
  ∀ (R : Type u) [CommRing R],
    Specs.D07.Ch10.PidDefinition.pidPredicateValue R →
      ∀ I : ℕ → Ideal R, Monotone I →
        ∃ n : ℕ, ∀ m : ℕ, n ≤ m → I m = I n

/-- Every nonempty collection of ideals in a PID has a member maximal for
inclusion within that collection. No properness or chain condition is imposed
on the collection. -/
def NonemptyCollectionHasMaximalMember : Prop :=
  ∀ (R : Type u) [CommRing R],
    Specs.D07.Ch10.PidDefinition.pidPredicateValue R →
      ∀ S : Set (Ideal R), S.Nonempty →
        ∃ I ∈ S, ∀ J ∈ S, I ≤ J → J = I

end Specs.D07.Ch10.PidAscendingChain
