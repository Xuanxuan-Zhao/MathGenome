import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.SetTheory.Cardinal.Finite

/-! Independent statements for `cor:integer-presentation-cokernel`,
`paper.tex:3177–3189`. A matrix acts on column vectors. Finite products
are finite direct sums; both versions of the cokernel are included.
Positive natural moduli denote the positive integers in the source.
No nonempty-index or nonzero-rank hypothesis is imposed. -/

namespace Specs.D07.Ch16.IntegerPresentationCokernel
open scoped DirectSum

/-- A cyclic integer factor vanishes exactly when its positive modulus is one.
The statement also distinguishes the infinite zero-modulus case. -/
def UnitFactorZero : Prop :=
  ∀ d : ℕ, Subsingleton (ZMod d) ↔ d = 1

/-- Delete all factors of modulus one by restriction to the retained coordinates. -/
def UnitFactorDeletion : Prop :=
  ∀ (s : ℕ) (d : Fin s → ℕ),
    ∃ E : (∀ i : Fin s, ZMod (d i)) ≃ₗ[ℤ]
      (∀ i : {i : Fin s // d i ≠ 1}, ZMod (d i.val)),
      ∀ x i, E x i = x i.val

/-- The full integer matrix corollary: positive divisibility-ordered moduli,
the free part of rank n-s, deletion of unit factors, and actual finiteness
with its cardinality or infinitude as appropriate. -/
def CokernelDecomposition : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin m) ℤ),
    ∃ (s : ℕ) (d : Fin s → ℕ),
      s ≤ m ∧ s ≤ n ∧
      (∀ i, 0 < d i) ∧ (∀ i j, i ≤ j → d i ∣ d j) ∧
      Nonempty (((Fin n → ℤ) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[ℤ]
        ((Fin (n - s) → ℤ) × (∀ i : Fin s, ZMod (d i)))) ∧
      Nonempty (((Fin n → ℤ) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[ℤ]
        ((Fin (n - s) → ℤ) × (⨁ i : Fin s, ZMod (d i)))) ∧
      Nonempty (((Fin n → ℤ) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[ℤ]
        ((Fin (n - s) → ℤ) × (∀ i : {i : Fin s // d i ≠ 1}, ZMod (d i.val)))) ∧
      (s = n → Finite ((Fin n → ℤ) ⧸ LinearMap.range A.mulVecLin) ∧
        Nat.card ((Fin n → ℤ) ⧸ LinearMap.range A.mulVecLin) = ∏ i, d i) ∧
      (s < n → Infinite ((Fin n → ℤ) ⧸ LinearMap.range A.mulVecLin))

end Specs.D07.Ch16.IntegerPresentationCokernel
