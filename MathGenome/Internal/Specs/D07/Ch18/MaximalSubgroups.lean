import Mathlib.GroupTheory.Nilpotent

/-!
Independent specification of K07.18.maximal_subgroups, paper.tex:5155–5181.

`IsCoatom M` means that M is proper and every subgroup strictly containing
M is the whole group. `Group.IsNilpotent` means that the upper central
series reaches the whole group, not a bound on a default class value.
The first assertion includes the trivial finite group. In the second,
the finite p-group hypothesis is its cardinality p^a, with p prime;
nontriviality is explicit. The index is the number of cosets of M in G.
-/

namespace Specs.D07.Ch18.MaximalSubgroups

universe u

def NilpotentIffMaximalNormal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Group.IsNilpotent G ↔ ∀ M : Subgroup G, IsCoatom M → M.Normal

def PGroupMaximalNormalIndex : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Nontrivial G]
    (p a : ℕ), p.Prime → Nat.card G = p ^ a →
    ∀ M : Subgroup G, IsCoatom M → M.Normal ∧ M.index = p

end Specs.D07.Ch18.MaximalSubgroups
