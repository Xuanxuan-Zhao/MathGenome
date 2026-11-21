import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Monotone
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.ESequence
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace SingleVariableAnalysis

/-- The manuscript's u_(n+1); every positive-indexed term is represented. -/
noncomputable def eSequence (n : ℕ) : ℝ :=
  (1 + 1 / (n + 1 : ℝ)) ^ (n + 1)

/-- Strict Bernoulli inequality, proved by finite induction. -/
private lemma strict_bernoulli (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) (k : ℕ) :
    1 + (k + 2 : ℝ) * x < (1 + x) ^ (k + 2) := by
  induction k with
  | zero =>
    have := sq_pos_of_ne_zero hx0
    norm_num
    nlinarith
  | succ k ih =>
    have h := mul_lt_mul_of_pos_right ih (show 0 < 1 + x by linarith)
    have hs : 0 ≤ (k + 2 : ℝ) * x ^ 2 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, pow_succ] at *
    nlinarith

/-- Strict increase uses Bernoulli on the ratio of consecutive bases. -/
theorem eSequence_strictMono : StrictMono eSequence := by
  apply strictMono_nat_of_lt_succ
  intro n
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : 0 < m + 1 := by linarith
  let a : ℝ := 1 + 1 / m
  let b : ℝ := 1 + 1 / (m + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hratio : b / a = 1 + -(1 / (m + 1) ^ 2) := by
    dsimp [a, b]
    field_simp
    ring
  have hx : -1 < -(1 / (m + 1) ^ 2) := by
    have hmge : 1 ≤ m := by dsimp [m]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    have hp : 1 < (m + 1) ^ 2 := by nlinarith
    have := (div_lt_one (by positivity : 0 < (m + 1) ^ 2)).mpr hp
    linarith
  have h := strict_bernoulli (-(1 / (m + 1) ^ 2)) hx (by
    exact neg_ne_zero.mpr (one_div_ne_zero (pow_ne_zero _ (ne_of_gt hm1)))) n
  have hid : 1 + (n + 2 : ℝ) * -(1 / (m + 1) ^ 2) = 1 / a := by
    dsimp [a, m]
    field_simp
    ring
  rw [hid, ← hratio, div_pow] at h
  have hp := (div_lt_div_iff₀ ha (pow_pos ha (n + 2))).mp h
  have hc : a ^ (n + 1) < b ^ (n + 2) := by
    rw [pow_succ] at hp
    nlinarith
  simpa [eSequence, a, b, m, Nat.cast_add, Nat.cast_one, Nat.add_assoc] using hc

/-- The elementary factorial majorant makes every finite sum strictly below 3. -/
private lemma sum_inv_factorial_le (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (1 : ℝ) / j.factorial) ≤
      3 - 2 * (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hfac : (2 : ℝ) ^ m ≤ ((m + 1).factorial : ℝ) := by
      exact_mod_cast (show 2 ^ m ≤ (m + 1).factorial by
        simpa [Nat.add_comm] using (Nat.factorial_mul_pow_le_factorial (m := 1) (n := m)))
    have hdiv : (1 : ℝ) / (m + 1).factorial ≤ (1 / 2 : ℝ) ^ m := by
      simpa only [one_div_pow] using
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ m) hfac)
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- The finite binomial expansion is bounded termwise by reciprocal factorials. -/
theorem eSequence_lt_three (n : ℕ) : eSequence n < 3 := by
  have hm : (0 : ℝ) < n + 1 := by positivity
  have hbound : eSequence n ≤ ∑ j ∈ Finset.range (n + 1 + 1),
      (1 : ℝ) / j.factorial := by
    unfold eSequence
    rw [add_comm (1 : ℝ), add_pow]
    apply Finset.sum_le_sum
    intro j hj
    simp only [one_pow, mul_one]
    calc
      (1 / (n + 1 : ℝ)) ^ j * ((n + 1).choose j : ℝ) ≤
          (1 / (n + 1 : ℝ)) ^ j * ((n + 1 : ℝ) ^ j / j.factorial) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.choose_le_pow_div (α := ℝ) j (n + 1))
      _ = 1 / j.factorial := by
        rw [one_div_pow]
        field_simp
  exact hbound.trans_lt (lt_of_le_of_lt (sum_inv_factorial_le (n + 1)) (by
    have : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    linarith))

/-- The first term equals 2, and all later terms are larger. -/
theorem two_le_eSequence (n : ℕ) : 2 ≤ eSequence n := by
  have h := eSequence_strictMono.monotone (Nat.zero_le n)
  norm_num [eSequence] at h
  simpa only [eSequence, one_div] using h

/-- Construct the limit using completeness of the real numbers. -/
noncomputable def eSequenceLimit : ℝ := sSup (Set.range eSequence)

private lemma eSequence_bddAbove : BddAbove (Set.range eSequence) := by
  refine ⟨3, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (eSequence_lt_three n).le

theorem eSequence_converges : RealSequenceConverges eSequence eSequenceLimit :=
  monotone_converges_to_supremum eSequence eSequence_strictMono.monotone eSequence_bddAbove

theorem eSequenceLimit_bounds : 2 ≤ eSequenceLimit ∧ eSequenceLimit ≤ 3 := by
  constructor
  · exact (two_le_eSequence 0).trans (le_csSup eSequence_bddAbove (Set.mem_range_self 0))
  · exact csSup_le (Set.range_nonempty eSequence) (by
      rintro x ⟨n, rfl⟩
      exact (eSequence_lt_three n).le)

theorem eSequence_finite_positive_limit :
    ∃ L : ℝ, 0 < L ∧ RealSequenceConverges eSequence L :=
  ⟨eSequenceLimit, lt_of_lt_of_le (by norm_num) eSequenceLimit_bounds.1, eSequence_converges⟩

end SingleVariableAnalysis
