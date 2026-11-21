import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

/-! The coloring domain is exactly the finite subsets of cardinality `k`.
Homogeneity includes a color witness, including for sets with no `k`-subsets. -/

universe u

namespace P205.Ramsey

abbrev KSubsets (X : Type u) (k : ℕ) := {s : Finset X // s.card = k}

def Homogeneous {X : Type u} {k r : ℕ}
    (c : KSubsets X k → Fin r) (H : Set X) : Prop :=
  ∃ a : Fin r, ∀ s : KSubsets X k, (↑s.val : Set X) ⊆ H → c s = a

namespace Specs

def InfiniteRamseyNat : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → 1 ≤ r → ∀ c : KSubsets ℕ k → Fin r,
    ∃ H : Set ℕ, H.Infinite ∧ Homogeneous c H

/-- The set `S` is an arbitrary infinite ground set inside any ambient type. -/
def InfiniteRamsey : Prop :=
  ∀ (X : Type u) (k r : ℕ), 1 ≤ k → 1 ≤ r →
    ∀ (c : KSubsets X k → Fin r) (S : Set X), S.Infinite →
      ∃ H : Set X, H ⊆ S ∧ H.Infinite ∧ Homogeneous c H

def HomogeneousOfCardLt : Prop :=
  ∀ (X : Type u) (k r : ℕ), 1 ≤ r →
    ∀ (c : KSubsets X k → Fin r) (t : Finset X), t.card < k →
      Homogeneous c (↑t : Set X)

end Specs
end P205.Ramsey
