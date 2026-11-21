import MathGenome.Internal.Specs.D07.Ch02.PermutationConvention
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent specification of `K07.02.symmetric_order` (paper.tex:502–509).
The permutations are the canonical bijections with rightmost-first composition.
Only counting requires finiteness; relabelling applies to arbitrary types.
-/

namespace Specs.D07.Ch02.SymmetricOrder

universe u v

/-- A finite set of size `n` has precisely `n!` permutations, including `n = 0`.
Finiteness of the permutation type is explicit, so `Nat.card` is used only
for genuinely finite cardinalities. -/
def SymmetricCardinality : Prop :=
  ∀ (X : Type u) [Finite X] (n : ℕ), Nat.card X = n →
    Finite (Equiv.Perm X) ∧ Nat.card (Equiv.Perm X) = n.factorial

/-- The relabelling map is a group isomorphism with the precise conjugation
formula from the source. No finiteness or nonemptiness is assumed. -/
def RelabellingIso : Prop :=
  ∀ (X : Type u) (Y : Type v) (b : X ≃ Y),
    ∃ e : Equiv.Perm X ≃* Equiv.Perm Y,
      ∀ (σ : Equiv.Perm X) (y : Y), e σ y = b (σ (b.symm y))

end Specs.D07.Ch02.SymmetricOrder
