import MathGenome.Internal.Specs.D07.Ch16.IntegerPresentationCokernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independent statement of K07.07.integer_presentations_smith_bridge,
paper.tex:3526–3541. Matrices act on integer column vectors. `IsUnit` is
invertibility in the integer matrix ring, and the determinant clauses make
the unimodularity explicit. All dimensions and the number of nonzero
diagonal entries may be zero. The same positive moduli occur in the
matrix and in each version of its cokernel. -/

namespace Specs.D07.Ch07.IntegerPresentationsSmithBridge
open scoped DirectSum

def IntegerPresentationSmithBridge : Prop :=
  ∀ (m n : ℕ) (B : Matrix (Fin n) (Fin m) ℤ),
    ∃ (r : ℕ) (d : Fin r → ℕ)
      (P : Matrix (Fin n) (Fin n) ℤ) (Q : Matrix (Fin m) (Fin m) ℤ),
      r ≤ m ∧ r ≤ n ∧
      (∀ i, 0 < d i) ∧ (∀ i j, i ≤ j → d i ∣ d j) ∧
      IsUnit P ∧ IsUnit Q ∧
      (P.det = 1 ∨ P.det = -1) ∧ (Q.det = 1 ∨ Q.det = -1) ∧
      (∀ i j, (P * B * Q) i j =
        if h : i.val = j.val ∧ i.val < r then (d ⟨i.val, h.2⟩ : ℤ) else 0) ∧
      Nonempty (((Fin n → ℤ) ⧸ LinearMap.range B.mulVecLin) ≃ₗ[ℤ]
        ((Fin (n - r) → ℤ) × (∀ i : Fin r, ZMod (d i)))) ∧
      Nonempty (((Fin n → ℤ) ⧸ LinearMap.range B.mulVecLin) ≃ₗ[ℤ]
        ((Fin (n - r) → ℤ) × (⨁ i : Fin r, ZMod (d i)))) ∧
      Nonempty (((Fin n → ℤ) ⧸ LinearMap.range B.mulVecLin) ≃ₗ[ℤ]
        ((Fin (n - r) → ℤ) × (∀ i : {i : Fin r // d i ≠ 1}, ZMod (d i.val))))

/-- A modulus-one factor is the zero additive group. -/
def UnitFactorZero : Prop :=
  ∀ d : ℕ, Subsingleton (ZMod d) ↔ d = 1

end Specs.D07.Ch07.IntegerPresentationsSmithBridge
