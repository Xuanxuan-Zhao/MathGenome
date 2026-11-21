import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The finite graph-counting step of the Kővári–Sós–Turán argument
in paper.tex, proof of W02. Copies are not required to be induced. -/
namespace P205.Extremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two disjoint parts of the stated sizes, with every cross-edge present.
Edges within either part are allowed in the ambient graph. -/
def ContainsCompleteBipartite (G : SimpleGraph V) (s t : ℕ) : Prop :=
  ∃ A B : Finset V, A.card = s ∧ B.card = t ∧ Disjoint A B ∧
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

/-- All vertices adjacent to every vertex of `S`. -/
def commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  univ.filter fun v => ∀ u ∈ S, G.Adj v u

namespace KSTStarCountSpec

universe u

/-- Looplessness excludes the selected vertices from their common neighbors. -/
def commonNeighborsDisjoint : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V],
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
    Disjoint S (commonNeighborFinset G S)

/-- Every s-set has at most t-1 common neighbors in a K_(s,t)-free graph. -/
def commonNeighborsBound : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V],
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (s t : ℕ),
    1 ≤ s → s ≤ t → ¬ ContainsCompleteBipartite G s t →
    ∀ S : Finset V, S.card = s → (commonNeighborFinset G S).card ≤ t - 1

/-- Counting stars by their center and then by their s-element leaf set. -/
def starCountBound : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V],
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (s t : ℕ),
    1 ≤ s → s ≤ t → ¬ ContainsCompleteBipartite G s t →
    (∑ v : V, Nat.choose (G.degree v) s) ≤ (t - 1) * Nat.choose (Fintype.card V) s

end KSTStarCountSpec
end P205.Extremal
