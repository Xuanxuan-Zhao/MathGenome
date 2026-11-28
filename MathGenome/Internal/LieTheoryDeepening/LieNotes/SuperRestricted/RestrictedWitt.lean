import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedWitt
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedMatrices
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedDerivations
import Mathlib.Algebra.CharP.Lemmas

namespace LieNotes.SuperRestricted.RestrictedWitt

open LieAlgebrasAndRepresentations.Witt
open _root_.Specs.LieNotes.SuperRestricted.RestrictedWitt

universe u v

variable {k : Type u} [Field k] {p : ℕ} [CharP k p]

private theorem basis_monomial (j : Fin p) (m : ℕ) :
    basis k p j (t k p ^ m) = (m : k) • t k p ^ ((j : ℕ) + m - 1) := by
  rw [basis_apply, Derivation.smul_apply, smul_eq_mul, mul_derivative_pow]

/-- Iterating a basis derivation with positive index increases the exponent by
`j - 1` at each step, with a scalar coefficient in the ground field. -/
private theorem basis_iterate_t (j : Fin p) (hj : 1 ≤ (j : ℕ)) (n : ℕ) :
    ∃ c : k, ((basis k p j : Module.End k (Truncated k p)) ^ n) (t k p) =
      c • t k p ^ (1 + n * ((j : ℕ) - 1)) := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    let m := 1 + n * ((j : ℕ) - 1)
    refine ⟨c * (m : k), ?_⟩
    rw [pow_succ', Module.End.mul_apply, hc, map_smul]
    change c • basis k p j (t k p ^ m) =
      (c * (m : k)) • t k p ^ (1 + (n + 1) * ((j : ℕ) - 1))
    rw [basis_monomial, smul_smul, Nat.succ_mul]
    congr 2
    dsimp only [m]
    omega

private theorem basis_pow_t [NeZero p] (j : Fin p) :
    ((basis k p j : Module.End k (Truncated k p)) ^ p) (t k p) =
      if (j : ℕ) = 1 then t k p else 0 := by
  let D : Module.End k (Truncated k p) := basis k p j
  change (D ^ p) (t k p) = _
  have hD : D (t k p) = t k p ^ (j : ℕ) := basis_apply_t k p j
  by_cases hzero : (j : ℕ) = 0
  · have hp : 2 ≤ p := (CharP.char_is_prime_of_pos k p).out.two_le
    have hsq : (D ^ 2) (t k p) = 0 := by
      rw [pow_two, Module.End.mul_apply, hD, hzero, pow_zero]
      exact (basis k p j).map_one_eq_zero
    simpa [hzero] using Module.End.pow_map_zero_of_le hp hsq
  by_cases hone : (j : ℕ) = 1
  · have hfix : D (t k p) = t k p := by simpa [hone] using hD
    simpa [hone, Module.End.pow_apply] using Function.iterate_fixed hfix p
  · obtain ⟨c, hc⟩ := basis_iterate_t (k := k) j (by omega) p
    have hle : p ≤ 1 + p * ((j : ℕ) - 1) :=
      le_trans (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_add_left _ _)
    have hnil := t_pow_eq_zero k p hle
    simpa [hone, hnil, D] using hc

/-- Composition induces the restricted operation on the truncated Witt algebra.
In the basis `t^j ∂ₜ`, the basis element at `j = 1` is fixed and the others
have zero restricted power. -/
theorem witt_admits_restrictedPower : witt_admits_restrictedPowerType.{u} := by
  intro k _ p _ _
  obtain ⟨power, hpower⟩ := RestrictedDerivations.derivations_admit_restrictedPower
    (k := k) (p := p) (A := Truncated k p)
  refine ⟨basis k p, basis_apply k p, power, hpower, ?_⟩
  intro j
  apply ext_t k p
  have h := LinearMap.congr_fun (hpower (basis k p j)) (t k p)
  change power.val (basis k p j) (t k p) = _ at h
  rw [h, basis_pow_t]
  split_ifs with hj
  · simp [hj]
  · simp

/-- Proposition SR07, with the matrix and general derivation conclusions
provided by the corresponding upstream theorems. -/
theorem proposition_SR07 : proposition_SR07Type.{u, v} :=
  ⟨RestrictedMatrices.pow_mem_sl, RestrictedMatrices.sl_admits_restrictedPower,
    RestrictedDerivations.derivations_admit_restrictedPower, witt_admits_restrictedPower⟩

end LieNotes.SuperRestricted.RestrictedWitt
