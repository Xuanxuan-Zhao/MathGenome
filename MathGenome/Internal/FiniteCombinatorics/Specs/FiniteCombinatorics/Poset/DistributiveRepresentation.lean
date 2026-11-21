import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.UpperLower.CompleteLattice

/-! The objects and full statement of paper.tex, Chapter 1, W06. -/
namespace FiniteCombinatorics.Poset

/-- Nonzero join-irreducibility, with the equality convention of the source. -/
def JoinIrreducible {L : Type*} [SemilatticeSup L] [OrderBot L] (j : L) : Prop :=
  j ≠ ⊥ ∧ ∀ u v : L, j = u ⊔ v → j = u ∨ j = v

/-- The poset inherits the order from the original lattice. -/
abbrev JoinIrreducibles (L : Type*) [SemilatticeSup L] [OrderBot L] :=
  {j : L // JoinIrreducible j}

end FiniteCombinatorics.Poset

namespace Specs.FiniteCombinatorics.Poset
open _root_.FiniteCombinatorics.Poset

/-- The representation includes both prescribed maps and preservation of the
lattice operations. Finiteness is a property, not a chosen enumeration; there
is no nontriviality assumption on the lattice or nonemptiness assumption on J. -/
def DistributiveRepresentation : Prop :=
  ∀ (L : Type*) [DistribLattice L] [OrderBot L] [Finite L],
    ∃ e : L ≃o LowerSet (JoinIrreducibles L),
      (∀ (x : L) (j : JoinIrreducibles L), j ∈ e x ↔ (j : L) ≤ x) ∧
      (∀ S : LowerSet (JoinIrreducibles L),
        e.symm S = (S : Set (JoinIrreducibles L)).toFinite.toFinset.sup
          (fun j => (j : L))) ∧
      (∀ x y : L, e (x ⊔ y) = e x ⊔ e y) ∧
      (∀ x y : L, e (x ⊓ y) = e x ⊓ e y)

end Specs.FiniteCombinatorics.Poset
