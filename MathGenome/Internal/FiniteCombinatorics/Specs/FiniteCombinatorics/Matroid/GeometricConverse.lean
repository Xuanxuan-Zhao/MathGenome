import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.LatticeRank

/-! W72, the converse for finite geometric lattices. The ground consists of
all atoms, including the empty atom type of the one-element lattice. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u

/-- The ground of the canonical matroid. -/
abbrev LatticeAtom (L : Type u) [CompleteLattice L] := {a : L // IsAtom a}

/-- The empty join is bottom. -/
noncomputable def atomJoin {L : Type u} [CompleteLattice L]
    (A : Set (LatticeAtom L)) : L := ⨆ a ∈ A, a.1

def atomsBelow {L : Type u} [CompleteLattice L] (x : L) : Set (LatticeAtom L) :=
  {a | a.1 ≤ x}

/-- The integer-valued rank prescribed by the lattice, before a matroid
has been constructed. -/
noncomputable def atomRank {L : Type u} [CompleteLattice L]
    (A : Set (LatticeAtom L)) : ℤ := (Expected.latticeHeight (atomJoin A) : ℤ)

/-- A realization includes simplicity (every singleton and every pair is
independent), the complete rank and closure formulas, all flats, and an
order/lattice isomorphism with both maps prescribed explicitly. -/
def GeometricRealization {L : Type u} [CompleteLattice L]
    (M : _root_.Matroid (LatticeAtom L)) : Prop :=
  M.E = univ ∧ ∃ hM : M.Finite,
    (∀ A, @Expected.rank _ M hM A = atomRank A) ∧
    (∀ a b : LatticeAtom L, M.Indep {a, b}) ∧
    (∀ A (a : LatticeAtom L), a ∈ M.closure A ↔ a.1 ≤ atomJoin A) ∧
    (∀ F, M.IsFlat F ↔ ∃ x : L, F = atomsBelow x) ∧
    (∃ e : L ≃o Flat M,
      (∀ x, (e x).1 = atomsBelow x) ∧ (∀ F, e.symm F = atomJoin F.1))

namespace Expected

def atomRankPresentation : Prop :=
  ∀ {L : Type u} [CompleteLattice L], GeometricLattice L →
    RankPresentation (univ : Set (LatticeAtom L)) atomRank

/-- Uniqueness makes the construction canonical and independent of any
field, representation, or choice of bases. -/
def existsUniqueGeometricMatroid : Prop :=
  ∀ {L : Type u} [CompleteLattice L], GeometricLattice L →
    ∃! M : _root_.Matroid (LatticeAtom L), GeometricRealization M

end Expected
end FiniteCombinatorics.Matroid
