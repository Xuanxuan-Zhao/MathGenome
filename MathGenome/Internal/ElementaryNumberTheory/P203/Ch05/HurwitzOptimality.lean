import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.HurwitzOptimality
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.RationalRoots
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace P203.Ch05.HurwitzOptimality
open P203Specs.Ch05.HurwitzOptimality

theorem golden_irrational : GoldenIrrational := by
  have hs : Irrational (Real.sqrt (5 : ℝ)) :=
    P203.Ch05.RationalRoots.irrational_sqrt 5 (by
      rintro ⟨n, hn⟩
      have : n < 3 := by nlinarith
      interval_cases n <;> norm_num at hn)
  constructor
  · simpa [golden] using (hs.ratCast_add 1).div_natCast (by decide : (2 : ℕ) ≠ 0)
  · simpa [conjugate] using (hs.ratCast_sub 1).div_natCast (by decide : (2 : ℕ) ≠ 0)

lemma factorization (p q : ℤ) (hq : q ≠ 0) :
    ((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ) =
    (q : ℝ) ^ 2 * ((p : ℝ) / q - golden) * ((p : ℝ) / q - conjugate) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  push_cast
  dsimp [golden, conjugate]
  field_simp
  nlinarith

theorem integer_obstruction : IntegerObstruction := by
  intro p q hq
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hf := factorization p q hq0
  have hn : p ^ 2 - p * q - q ^ 2 ≠ 0 := by
    intro hz
    have hzero : (q : ℝ) ^ 2 * ((p : ℝ) / q - golden) *
        ((p : ℝ) / q - conjugate) = 0 := by rw [← hf, hz]; norm_num
    have hqr : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq0)
    rcases mul_eq_zero.mp hzero with h | h
    · have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hqr)
      exact golden_irrational.1 ⟨(p : ℚ) / q, by push_cast; exact he⟩
    · have he := sub_eq_zero.mp h
      exact golden_irrational.2 ⟨(p : ℚ) / q, by push_cast; exact he⟩
  refine ⟨hn, ?_, ?_⟩
  · have habs : (1 : ℤ) ≤ |p ^ 2 - p * q - q ^ 2| := by
      have := abs_pos.mpr hn
      omega
    exact_mod_cast habs
  · rw [hf, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]

/-- The obstruction gives a uniform denominator bound for each improved constant. -/
lemma denominator_bound (C : ℝ) (hC : Real.sqrt 5 < C) (p q : ℤ) (hq : 0 < q)
    (happrox : |golden - (p : ℝ) / q| < 1 / (C * (q : ℝ) ^ 2)) :
    (q : ℝ) ^ 2 < 1 / (C * (C - Real.sqrt 5)) := by
  have hCpos : 0 < C := lt_of_le_of_lt (Real.sqrt_nonneg _) hC
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq2 : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqr
  have hden : 0 < C * (q : ℝ) ^ 2 := mul_pos hCpos hq2
  have he : |(p : ℝ) / q - golden| < 1 / (C * (q : ℝ) ^ 2) := by
    simpa only [abs_sub_comm] using happrox
  have hsmall := (lt_div_iff₀ hden).mp he
  have hnorm := (integer_obstruction p q hq).2.1
  rw [(integer_obstruction p q hq).2.2] at hnorm
  have ht : 0 ≤ (q : ℝ) ^ 2 * |(p : ℝ) / q - golden| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hdist : C < |(p : ℝ) / q - conjugate| := by
    by_contra! h
    have := mul_le_mul_of_nonneg_left h ht
    nlinarith [hnorm]
  have hroots : |golden - conjugate| = Real.sqrt 5 := by
    have : golden - conjugate = Real.sqrt 5 := by dsimp [golden, conjugate]; ring
    rw [this, abs_of_nonneg (Real.sqrt_nonneg _)]
  have htriangle := abs_sub_le ((p : ℝ) / q) golden conjugate
  rw [hroots] at htriangle
  have hgap : C - Real.sqrt 5 < 1 / (C * (q : ℝ) ^ 2) := by
    linarith
  have hprod := (lt_div_iff₀ hden).mp hgap
  apply (lt_div_iff₀ (mul_pos hCpos (sub_pos.mpr hC))).mpr
  nlinarith

theorem finite_approximations : FiniteApproximations := by
  intro C hC
  have hCpos : 0 < C := lt_of_le_of_lt (Real.sqrt_nonneg _) hC
  let B : ℝ := 1 / (C * (C - Real.sqrt 5))
  let K : ℝ := |golden| + 1 / C
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N, hN⟩ := exists_int_gt (max (K * B) B)
  have hNB : B < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNM : K * B < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  apply ((Set.finite_Icc (-N) N).prod (Set.finite_Icc 1 N)).subset
  rintro ⟨p, q⟩ ⟨hq, _hcop, happrox⟩
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqsq : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hqb : (q : ℝ) < B := by
    have := denominator_bound C hC p q hq happrox
    dsimp [B]
    nlinarith
  have herr : |golden - (p : ℝ) / q| < 1 / C := by
    apply lt_of_lt_of_le happrox
    apply one_div_le_one_div_of_le hCpos
    nlinarith [mul_le_mul_of_nonneg_left hqsq hCpos.le]
  have htriangle := abs_sub_le ((p : ℝ) / q) golden 0
  have hrat : |(p : ℝ) / q| < K := by
    dsimp [K]
    simp only [sub_zero, abs_sub_comm] at htriangle
    linarith
  have hp : |(p : ℝ)| < K * B := calc
    |(p : ℝ)| = |(p : ℝ) / q| * q := by
      rw [abs_div, abs_of_pos hqr, div_mul_cancel₀ _ (ne_of_gt hqr)]
    _ < K * q := mul_lt_mul_of_pos_right hrat hqr
    _ < K * B := mul_lt_mul_of_pos_left hqb hK
  have hpN : |p| ≤ N := by
    have : |(p : ℝ)| < (N : ℝ) := lt_trans hp hNM
    exact_mod_cast this.le
  have hqN : q ≤ N := by exact_mod_cast (lt_trans hqb hNB).le
  exact ⟨abs_le.mp hpN, ⟨hq, hqN⟩⟩

theorem not_infinite_approximations : NotInfiniteApproximations := by
  intro C hC
  exact (finite_approximations C hC).not_infinite

end P203.Ch05.HurwitzOptimality
