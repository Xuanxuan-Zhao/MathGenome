import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedSlTwo
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedMatrices
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.FinCases

/-! The standard basis of `sl₂` with its matrix restricted powers. -/

namespace LieNotes.SuperRestricted.RestrictedSlTwo

open LieAlgebrasAndRepresentations (sl2 sl2_e sl2_f sl2_h sl2_h_val sl2_basis sl2_relations)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedSlTwo

universe u

theorem basis : basisType.{u} :=
  sl2_basis

theorem brackets : bracketsType.{u} :=
  sl2_relations

/-- The matrix restricted powers of the standard basis, valid in positive characteristic. -/
theorem basis_powers {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p] :
    (RestrictedMatrices.restrictedPower (p := p) 2).val (sl2_e k) = 0 ∧
    (RestrictedMatrices.restrictedPower (p := p) 2).val (sl2_f k) = 0 ∧
    (RestrictedMatrices.restrictedPower (p := p) 2).val (sl2_h k) = sl2_h k := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have offDiagonal_pow (i j : Fin 2) (hij : i ≠ j) :
      (Matrix.single i j (1 : k)) ^ p = 0 := by
    apply pow_eq_zero_of_le (Fact.out : p.Prime).two_le
    rw [pow_two, Matrix.single_mul_single_of_ne (1 : k) i j i hij.symm]
  have hDiag : (sl2_h k).val = Matrix.diagonal ![(1 : k), -1] := by
    rw [sl2_h_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  refine ⟨?_, ?_, ?_⟩ <;> apply Subtype.ext <;>
    rw [RestrictedMatrices.coe_restrictedPower_apply]
  · exact offDiagonal_pow 0 1 (by decide)
  · exact offDiagonal_pow 1 0 (by decide)
  · rw [hDiag, Matrix.diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> simp [neg_one_pow_char k]

theorem matrixRestrictedPowers : matrixRestrictedPowersType.{u} := by
  intro k _ _ p _ hp
  let : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
  exact ⟨RestrictedMatrices.restrictedPower (p := p) 2,
    RestrictedMatrices.coe_restrictedPower_apply, basis_powers⟩

end LieNotes.SuperRestricted.RestrictedSlTwo
