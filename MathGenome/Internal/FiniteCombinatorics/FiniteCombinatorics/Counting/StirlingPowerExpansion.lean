import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Counting.StirlingSecond
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Counting.StirlingFallingExpansion
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingPowerExpansion
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

namespace FiniteCombinatorics.StirlingPowerExpansion

open Polynomial
open scoped BigOperators

/-- Bridge from the library's descending Pochhammer polynomial to the original product. -/
theorem descPochhammer_eq_product (n : ℕ) :
    descPochhammer ℤ n = ∏ i ∈ Finset.range n, (X - C (i : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, Finset.prod_range_succ, ih]
    simp

/-- The map-counting identity at all nonnegative integers determines the polynomial. -/
theorem power_eq_sum (n : ℕ) :
    (X : ℤ[X]) ^ n = ∑ k ∈ Finset.range (n + 1),
      C (StirlingSecond.count n k : ℤ) * ∏ i ∈ Finset.range k, (X - C (i : ℤ)) := by
  have hc (a b : ℕ) : StirlingSecond.count a b = Nat.stirlingSecond a b :=
    StirlingSecond.count_eq_stirlingSecond a b
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range (Nat.cast : ℕ → ℤ)) ?_
    (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ)))
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C,
    ← descPochhammer_eq_product, descPochhammer_eval_eq_descFactorial,
    hc]
  exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m n

/-- A monic polynomial sequence with exactly one polynomial in each degree. -/
noncomputable def fallingSequence : Polynomial.Sequence ℤ where
  elems' n := ∏ i ∈ Finset.range n, (X - C (i : ℤ))
  degree_eq' n := by
    rw [← descPochhammer_eq_product, degree_eq_natDegree (monic_descPochhammer ℤ n).ne_zero,
      descPochhammer_natDegree]

theorem fallingSequence_unit (n : ℕ) : IsUnit (fallingSequence n).leadingCoeff := by
  change IsUnit (∏ i ∈ Finset.range n, (X - C (i : ℤ))).leadingCoeff
  rw [← descPochhammer_eq_product, (monic_descPochhammer ℤ n).leadingCoeff]
  exact isUnit_one

/-- The descending factorials of orders `0,...,d` are a basis of degree at most `d`. -/
theorem finite_degree_basis : StirlingPowerExpansionSpec.FiniteDegreeBasis := by
  intro d
  constructor
  · exact fallingSequence.linearIndependent.comp (fun k : Fin (d + 1) => k.val)
      Fin.val_injective
  · have hset : Set.range (fun k : Fin (d + 1) => fallingSequence k.val) =
        fallingSequence '' Set.Iic d := by
      ext p
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k.val, by simpa using Nat.le_of_lt_succ k.isLt, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
    change Submodule.span ℤ (Set.range (fun k : Fin (d + 1) => fallingSequence k.val)) = _
    rw [hset]
    exact fallingSequence.span_degreeLE (fun i _ => fallingSequence_unit i)

/-- Enlarging the finite sum only adds out-of-range zero entries. -/
theorem power_eq_sum_of_le (n d : ℕ) (hnd : n ≤ d) :
    (X : ℤ[X]) ^ n = ∑ k ∈ Finset.range (d + 1),
      C (StirlingSecond.count n k : ℤ) * ∏ i ∈ Finset.range k, (X - C (i : ℤ)) := by
  rw [power_eq_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hnd 1))
  intro k _ hk
  have hnk : n < k := by simp only [Finset.mem_range] at hk; omega
  rw [StirlingSecond.count_out_of_range n k hnk]
  simp

/-- Coefficients of the second change of basis give one matrix product. -/
theorem second_mul_first (d : ℕ) :
    StirlingPowerExpansionSpec.secondMatrix d *
      StirlingPowerExpansionSpec.signedFirstMatrix d = 1 := by
  ext n k
  have h := congrArg (fun p : ℤ[X] => p.coeff k.val)
    (power_eq_sum_of_le n.val d (Nat.le_of_lt_succ n.isLt))
  simp only [finsetSum_coeff, coeff_C_mul,
    StirlingFallingExpansion.coeff_fallingFactorial] at h
  simp only [Matrix.mul_apply, Matrix.one_apply]
  change (∑ j : Fin (d + 1), (StirlingSecond.count n.val j.val : ℤ) *
    ((-1 : ℤ) ^ (j.val - k.val) * (StirlingFirstSpec.stirlingFirst j.val k.val : ℤ))) = if n = k then 1 else 0
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (StirlingSecond.count n.val j : ℤ) *
    ((-1 : ℤ) ^ (j - k.val) * (StirlingFirstSpec.stirlingFirst j k.val : ℤ)))]
  change (∑ j ∈ Finset.range (d + 1), (StirlingSecond.count n.val j : ℤ) *
    ((-1 : ℤ) ^ (j - k.val) * (StirlingFirst.stirlingFirst j k.val : ℤ))) = _
  rw [← h]
  simp [coeff_X_pow, Fin.ext_iff, eq_comm]

/-- Square matrices over the commutative ring ℤ have the reverse inverse too. -/
theorem mutual_inverses : StirlingPowerExpansionSpec.MutualInverses := by
  intro d
  have h := second_mul_first d
  exact ⟨mul_eq_one_comm.mp h, h⟩

/-- Every entry strictly above the diagonal vanishes. -/
theorem out_of_range : StirlingPowerExpansionSpec.OutOfRange := by
  intro d n k hnk
  have hnk' : n.val < k.val := hnk
  dsimp [StirlingPowerExpansionSpec.signedFirstMatrix,
    StirlingPowerExpansionSpec.secondMatrix]
  change (-1 : ℤ) ^ (n.val - k.val) * (StirlingFirst.stirlingFirst n.val k.val : ℤ) = 0 ∧ _
  rw [StirlingFirst.stirlingFirst_eq_zero_of_lt n.val k.val hnk',
    StirlingSecond.count_out_of_range n.val k.val hnk']
  simp

end FiniteCombinatorics.StirlingPowerExpansion
