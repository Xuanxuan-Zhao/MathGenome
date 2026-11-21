import MathGenome.Internal.Specs.D07.Ch02.PermutationConvention
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Perm.Basic

/-!
Independent specification of `K07.02.cycle_decomposition`
(paper.tex:510–518, chapters/M07.02.tex:88–96).

A written cycle is a list of distinct entries of length at least two.
`List.formPerm` is definitionally the accepted `cycleConstructorValue` (and
`D07.Ch02.PermutationConvention.listedCycle`), with rightmost-first products.
Disjointness here is disjointness of the lists of entries, not just inequality
of the cycles. Singleton cycles and fixed points are omitted.

Uniqueness is stated on the actual lists of entries: one may reorder the
outer list and cyclically rotate each corresponding inner list. The iff also
records that these changes preserve the represented permutation.
-/

namespace Specs.D07.Ch02.CycleDecomposition

universe u

/-- A product of pairwise disjoint nontrivial cycles, written using entries. -/
def Decomposition {X : Type u} (σ : Equiv.Perm X) (L : List (List X)) : Prop := by
  classical
  exact (∀ l ∈ L, l.Nodup ∧ 2 ≤ l.length) ∧
    L.Pairwise List.Disjoint ∧ (L.map List.formPerm).prod = σ

/-- Finiteness of the ambient set is the only hypothesis on a permutation. -/
def ExistsDecomposition : Prop :=
  ∀ (X : Type u) [Finite X] (σ : Equiv.Perm X),
    ∃ L : List (List X), Decomposition σ L

/-- Equality of decomposed permutations is exactly reordering their cycles
and rotating the entries of each cycle. No preferred starting point is chosen. -/
def UniqueDecomposition : Prop :=
  ∀ (X : Type u) [Finite X] (σ τ : Equiv.Perm X)
    (L M : List (List X)), Decomposition σ L → Decomposition τ M →
    (σ = τ ↔ ∃ M' : List (List X), M'.Perm M ∧ List.Forall₂ List.IsRotated L M')

/-- The accepted notation has precisely cyclic rotation as its ambiguity for
nontrivial cycles, on any set, even an infinite one. -/
def CycleRotation : Prop :=
  ∀ (X : Type u) (l m : List X) (hl : l.Nodup) (hm : m.Nodup),
    2 ≤ l.length → 2 ≤ m.length →
    (PermutationConvention.cycleConstructorValue X l hl =
      PermutationConvention.cycleConstructorValue X m hm ↔ l.IsRotated m)

/-- Permutations with disjoint supports commute, without a finiteness hypothesis. -/
def DisjointCommute : Prop :=
  ∀ (X : Type u) (σ τ : Equiv.Perm X), σ.Disjoint τ → σ * τ = τ * σ

/-- In particular, cycles whose lists of entries are disjoint commute. -/
def DisjointListedCyclesCommute : Prop :=
  ∀ (X : Type u) (l m : List X) (hl : l.Nodup) (hm : m.Nodup),
    l.Disjoint m →
    PermutationConvention.cycleConstructorValue X l hl *
        PermutationConvention.cycleConstructorValue X m hm =
      PermutationConvention.cycleConstructorValue X m hm *
        PermutationConvention.cycleConstructorValue X l hl

end Specs.D07.Ch02.CycleDecomposition
