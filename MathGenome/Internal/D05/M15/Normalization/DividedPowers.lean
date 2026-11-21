import MathGenome.Internal.Specs.D05.M15.Normalization.DividedPowers
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp

/-! Factorial normalization of ordinary powers in any unital K-algebra.
Only the binomial identity requires two elements to commute. -/
noncomputable section

namespace D05.M15.Normalization.DividedPowers

namespace Spec
export D05.Specs.M15.Normalization.DividedPowers
  (dividedPowerType dividedPowerValue boundaryDegrees dividedPower_mul dividedPower_add)
end Spec

/-- Ordinary algebra powers divided by the scalar factorial. -/
def dividedPower : Spec.dividedPowerType := Spec.dividedPowerValue

private theorem inverse_factorials (K : Type*) [Field K] [CharZero K] (r s : ℕ) :
    (r.factorial : K)⁻¹ * (s.factorial : K)⁻¹ =
      ((r + s).choose r : K) * ((r + s).factorial : K)⁻¹ := by
  rw [Nat.cast_add_choose]
  have hr : (r.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hs : (s.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  have hrs : ((r + s).factorial : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (r + s))
  field_simp

theorem boundaryDegrees : Spec.boundaryDegrees := by
  intro K A _ _ _ _ u
  simp [Spec.dividedPowerValue]

theorem dividedPower_mul : Spec.dividedPower_mul := by
  intro K A _ _ _ _ u r s
  simp only [Spec.dividedPowerValue, smul_mul_smul_comm, ← pow_add, smul_smul]
  rw [inverse_factorials K r s]

theorem dividedPower_add : Spec.dividedPower_add := by
  intro K A _ _ _ _ u v huv k
  simp only [Spec.dividedPowerValue]
  rw [huv.add_pow', Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro rs hrs
  have hsum : rs.1 + rs.2 = k := Finset.mem_antidiagonal.mp hrs
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inverse_factorials K rs.1 rs.2, hsum, mul_comm]

end D05.M15.Normalization.DividedPowers
