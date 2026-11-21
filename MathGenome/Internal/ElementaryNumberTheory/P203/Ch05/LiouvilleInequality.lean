import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.LiouvilleInequality
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.RingTheory.Localization.Integral

namespace P203

open Polynomial

/-- Clearing the denominators of the rational minimal polynomial preserves
its degree and its root. -/
theorem integer_polynomial_of_algebraic {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ f : ℤ[X], f ≠ 0 ∧ f.natDegree = (minpoly ℚ x).natDegree ∧
      (f.map (algebraMap ℤ ℝ)).eval x = 0 := by
  let f := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hf : f ≠ 0 := by
    exact mt IsFractionRing.integerNormalization_eq_zero_iff.mp
      (minpoly.ne_zero hx.isIntegral)
  obtain ⟨b, hb, hmap⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hdeg : f.natDegree = (minpoly ℚ x).natDegree := by
    rw [← natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ)
      (Int.cast_injective (α := ℚ)) f]
    rw [hmap, natDegree_smul _ hb0]
  refine ⟨f, hf, hdeg, ?_⟩
  rw [eval_map_algebraMap]
  exact IsLocalization.integerNormalization_aeval_eq_zero
    (nonZeroDivisors ℤ) (minpoly ℚ x) (minpoly.aeval ℚ x)

/-- Liouville's lower bound for every reduced rational with positive
denominator, at the exact algebraic degree of `x`. -/
theorem liouville_inequality : P203Specs.LiouvilleInequality := by
  intro x d hx hi hdegree _hd
  obtain ⟨f, hf, hdeg, hroot⟩ := integer_polynomial_of_algebraic hx
  obtain ⟨A, hA, hbound⟩ := Liouville.exists_pos_real_of_irrational_root hi hf hroot
  refine ⟨1 / A, one_div_pos.mpr hA, ?_⟩
  intro p q hq _hcoprime
  lift q to ℕ using hq.le
  have hqpos : 0 < q := by exact_mod_cast hq
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
  have h := hbound p (q - 1)
  have hpred : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hqpos
  rw [hpred, hdeg, hdegree] at h
  simp only [Int.cast_natCast]
  apply (div_le_iff₀ (pow_pos hqR d)).mpr
  apply (div_le_iff₀ hA).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end P203
