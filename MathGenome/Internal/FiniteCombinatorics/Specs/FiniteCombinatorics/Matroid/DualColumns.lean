import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Duality
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! W75, first assertion. The sum index lists the identity columns first, then
all columns of A. Both representations use exactly this same index type.
No positive cardinality or nonsingularity assumption is imposed. -/
namespace FiniteCombinatorics.Matroid
open Set
open scoped _root_.Matroid
universe u v w

/-- The columns of `[I | A]`, retaining their indices. -/
def standardColumns {K : Type u} [Field K] {R : Type v} {C : Type w}
    [DecidableEq R] (A : Matrix R C K) : R ⊕ C → (R → K) :=
  Sum.elim (fun i => Pi.single i 1) (fun j i => A i j)

/-- The columns of `[-Aᵀ | I]` in the original column order. -/
def standardDualColumns {K : Type u} [Field K] {R : Type v} {C : Type w}
    [DecidableEq C] (A : Matrix R C K) : R ⊕ C → (C → K) :=
  Sum.elim (fun i j => -A i j) (fun j => Pi.single j 1)

/-- Identify the block order with the original `Fin n` order. -/
def blockColumnOrder {r n : ℕ} (h : r ≤ n) : Fin r ⊕ Fin (n-r) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

namespace Expected

def dualColumns : Prop := ∀ {K : Type u} [Field K]
  {R : Type v} {C : Type w} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
  (A : Matrix R C K) (M : _root_.Matroid (R ⊕ C)), M.E = univ →
  Represents K M (standardColumns A) → Represents K M✶ (standardDualColumns A)

def complementaryColumnBases : Prop := ∀ {K : Type u} [Field K]
  {R : Type v} {C : Type w} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
  (A : Matrix R C K) (B : Set (R ⊕ C)),
  (vectorMatroid K univ (toFinite _) (standardColumns A)).IsBase B ↔
  (vectorMatroid K univ (toFinite _) (standardDualColumns A)).IsBase (univ \ B)

def dualColumnsOrdered : Prop := ∀ {K : Type u} [Field K]
  {r n : ℕ} (h : r ≤ n) (A : Matrix (Fin r) (Fin (n-r)) K)
  (M : _root_.Matroid (Fin n)), M.E = univ →
  Represents K M (standardColumns A ∘ (blockColumnOrder h).symm) →
  Represents K M✶ (standardDualColumns A ∘ (blockColumnOrder h).symm)

end Expected
end FiniteCombinatorics.Matroid
