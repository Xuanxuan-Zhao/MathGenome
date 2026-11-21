import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.SquarefreeAverage
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.ClassicalFunctions
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.MobiusReciprocalSquares
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Ring

open scoped BigOperators
open P203Specs.ClassicalFunctions
open P203Specs.Ch03.SquarefreeAverage

namespace P203.Ch03.SquarefreeAverage

/-- The finite square-divisor sum, extended by zero at zero. -/
def squareDivisorSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if d ^ 2 ∣ n then mu d else 0

lemma square_dvd_mul_iff {a b d e : ℕ} (hab : a.Coprime b)
    (hd : d ∣ a) (he : e ∣ b) :
    (d * e) ^ 2 ∣ a * b ↔ d ^ 2 ∣ a ∧ e ^ 2 ∣ b := by
  constructor
  · intro h
    have hd2 : d ^ 2 ∣ a * b := (dvd_mul_right (d ^ 2) (e ^ 2)).trans (by simpa [mul_pow] using h)
    have he2 : e ^ 2 ∣ a * b := (dvd_mul_left (e ^ 2) (d ^ 2)).trans (by simpa [mul_pow] using h)
    exact ⟨((hab.coprime_dvd_left hd).pow_left 2).dvd_of_dvd_mul_right hd2,
      ((hab.symm.coprime_dvd_left he).pow_left 2).dvd_of_dvd_mul_left he2⟩
  · rintro ⟨hd, he⟩
    simpa [mul_pow] using Nat.mul_dvd_mul hd he

lemma squareDivisorSum_mul {a b : ℕ} (hab : a.Coprime b) :
    squareDivisorSum (a * b) = squareDivisorSum a * squareDivisorSum b := by
  classical
  unfold squareDivisorSum
  rw [Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image hab.mul_injOn_divisors, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hd' := Nat.dvd_of_mem_divisors hd
  have he' := Nat.dvd_of_mem_divisors he
  have hcop := (hab.coprime_dvd_left hd').coprime_dvd_right he'
  simp only [square_dvd_mul_iff hab hd' he',
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  split_ifs <;> simp_all

lemma squareDivisorSum_prime_pow {p k : ℕ} (hp : p.Prime) :
    squareDivisorSum (p ^ k) = mu (p ^ k) ^ 2 := by
  classical
  unfold squareDivisorSum
  rw [Nat.sum_divisors_prime_pow hp]
  have hterm (i : ℕ) (hi : 2 ≤ i) : mu (p ^ i) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
  rcases k with _ | _ | k
  · simp [mu]
  · simp [Finset.sum_range_succ, mu, ArithmeticFunction.moebius_apply_prime hp,
      show ¬ p ^ 2 ∣ p from by
        simpa only [pow_one] using (not_congr (Nat.pow_dvd_pow_iff_le_right (k := 2) (l := 1) hp.one_lt)).mpr (by omega)]
  · rw [hterm _ (by omega), zero_pow (by norm_num : 2 ≠ 0)]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_pow, one_dvd, ite_true, ArithmeticFunction.moebius_apply_one]
    rw [Finset.sum_eq_single 0]
    · have hdiv : p ^ 2 ∣ p ^ (k + 1 + 1) :=
        (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr (by omega)
      simp [hdiv, ArithmeticFunction.moebius_apply_prime hp]
    · intro i hi hi0
      rw [hterm _ (by omega)]
      simp
    · intro h
      exact (h (by simp)).elim

/-- paper.tex:1189: the identity includes n=1 and uses positive divisors. -/
theorem mobius_square_divisor_identity (n : ℕ) :
    mu n ^ 2 = squareDivisorSum n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [squareDivisorSum]
  | one => simp [squareDivisorSum]
  | prime_pow p k hp hk => exact (squareDivisorSum_prime_pow hp).symm
  | coprime a b ha hb hab ia ib =>
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab,
      mul_pow, ia, ib, squareDivisorSum_mul hab]

/-- A square divisor of a positive n ≤ x has its positive root ≤ √x. -/
lemma square_divisor_le_cutoff {x : ℝ} (hx : 0 ≤ x) {n d : ℕ}
    (hn : 0 < n) (hnx : (n : ℝ) ≤ x) (hd : d ^ 2 ∣ n) :
    d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊ := by
  have hdpos : 0 < d := by
    by_contra h
    have : d = 0 := by omega
    simp [this, hn.ne'] at hd
  have hsq : (d : ℝ) ^ 2 ≤ x := by
    have := Nat.le_of_dvd hn hd
    exact (by exact_mod_cast this : (d : ℝ) ^ 2 ≤ (n : ℝ)).trans hnx
  exact Finset.mem_Icc.mpr ⟨hdpos,
    (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr
      ((Real.le_sqrt (by positivity) hx).mpr hsq)⟩

lemma squareDivisorSum_cutoff {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : 0 < n) (hnx : (n : ℝ) ≤ x) :
    squareDivisorSum n = ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
      if d ^ 2 ∣ n then mu d else 0 := by
  classical
  unfold squareDivisorSum
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact ⟨square_divisor_le_cutoff hx hn hnx hd, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨Nat.mem_divisors.mpr ⟨(dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hd, hn.ne'⟩, hd⟩

/-- Exact finite rearrangement before making any estimates. -/
theorem squarefreeSum_eq_floor_sum (x : ℝ) (hx : 0 ≤ x) :
    squarefreeSum x = ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
      (mu d : ℝ) * (⌊x / (d : ℝ) ^ 2⌋₊ : ℝ) := by
  classical
  unfold squarefreeSum
  have hreal (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
      ((mu n ^ 2 : ℤ) : ℝ) = ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
        if d ^ 2 ∣ n then (mu d : ℝ) else 0 := by
    rw [mobius_square_divisor_identity, squareDivisorSum_cutoff hx
      (Finset.mem_Icc.mp hn).1
      ((Nat.le_floor_iff hx).mp (Finset.mem_Icc.mp hn).2)]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hreal, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div, ← Nat.cast_pow,
    Nat.floor_div_natCast]

/-- The accumulated floor error is bounded by the number of square roots used. -/
lemma floor_sum_error (x : ℝ) (hx : 0 ≤ x) :
    |squarefreeSum x - x *
      (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (mu d : ℝ) / (d : ℝ) ^ 2)| ≤
      Real.sqrt x := by
  rw [squarefreeSum_eq_floor_sum x hx, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hrewrite (d : ℕ) :
      (mu d : ℝ) * (⌊x / (d : ℝ) ^ 2⌋₊ : ℝ) - x * ((mu d : ℝ) / (d : ℝ) ^ 2) =
        (mu d : ℝ) * ((⌊x / (d : ℝ) ^ 2⌋₊ : ℝ) - x / (d : ℝ) ^ 2) := by ring
  simp_rw [hrewrite]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
        |(mu d : ℝ) * ((⌊x / (d : ℝ) ^ 2⌋₊ : ℝ) - x / (d : ℝ) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      simpa using mul_le_mul
        (P203.Ch03.MobiusReciprocalSquares.abs_mu_le d)
        (Nat.abs_floor_sub_le (div_nonneg hx (sq_nonneg _)))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = (⌊Real.sqrt x⌋₊ : ℝ) := by simp
    _ ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)

lemma partial_mobius_eq (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, (mu d : ℝ) / (d : ℝ) ^ 2) =
      6 / Real.pi ^ 2 - P203Specs.Ch03.MobiusReciprocalSquares.mobiusTail y := by
  classical
  let f : ℕ → ℝ := fun n => (mu n : ℝ) / (n : ℝ) ^ 2
  let t : ℕ → ℝ := fun n => if y < (n : ℝ) then f n else 0
  have hs : Summable f := (summable_nat_add_iff 1).mp
    P203.Ch03.MobiusReciprocalSquares.mobius_summable
  have ht : Summable t := (P203.Ch03.MobiusReciprocalSquares.mobius_tail_bound y hy).1
  have htotal : (∑' n, f n) = 6 / Real.pi ^ 2 := by
    have heq : (∑' n, f n) = f 0 + ∑' n, f (n + 1) :=
      tsum_eq_zero_add' (f := f) P203.Ch03.MobiusReciprocalSquares.mobius_summable
    rw [heq]
    simpa [f, P203Specs.Ch03.MobiusReciprocalSquares.mobiusTerm] using
      P203.Ch03.MobiusReciprocalSquares.mobius_hasSum.tsum_eq
  have hfinite : (∑' n, (f n - t n)) = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, f d := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊) (fun n hn => ?_)]
    · apply Finset.sum_congr rfl
      intro d hd
      have hdy : (d : ℝ) ≤ y :=
        (Nat.le_floor_iff (by linarith : 0 ≤ y)).mp (Finset.mem_Icc.mp hd).2
      simp [t, not_lt.mpr hdy]
    · by_cases hn0 : n = 0
      · simp [f, t, hn0, show ¬y < 0 by linarith]
      · have hyn : y < (n : ℝ) := by
          by_contra h
          have hnle : n ≤ ⌊y⌋₊ :=
            (Nat.le_floor_iff (by linarith : 0 ≤ y)).mpr (not_lt.mp h)
          exact hn (Finset.mem_Icc.mpr ⟨by omega, hnle⟩)
        simp [t, hyn]
  rw [← hfinite, hs.tsum_sub ht, htotal]
  rfl

/-- A uniform explicit error bound for every real cutoff x ≥ 1. -/
theorem squarefree_error_bound (x : ℝ) (hx : 1 ≤ x) :
    |squarefreeSum x - (6 / Real.pi ^ 2) * x| ≤ 3 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa)
  have hspos : 0 < Real.sqrt x := by linarith
  have htail := (P203.Ch03.MobiusReciprocalSquares.mobius_tail_bound (Real.sqrt x) hs1).2
  have hb : |x * P203Specs.Ch03.MobiusReciprocalSquares.mobiusTail (Real.sqrt x)| ≤
      2 * Real.sqrt x := by
    rw [abs_mul, abs_of_nonneg hx0]
    calc
      _ ≤ x * (2 / Real.sqrt x) := mul_le_mul_of_nonneg_left htail hx0
      _ = 2 * Real.sqrt x := by
        rw [← mul_div_assoc]
        apply (div_eq_iff hspos.ne').mpr
        nlinarith [Real.sq_sqrt hx0]
  have hf := floor_sum_error x hx0
  rw [partial_mobius_eq (Real.sqrt x) hs1] at hf
  have hid : squarefreeSum x - (6 / Real.pi ^ 2) * x =
      (squarefreeSum x - x * (6 / Real.pi ^ 2 -
        P203Specs.Ch03.MobiusReciprocalSquares.mobiusTail (Real.sqrt x))) -
        x * P203Specs.Ch03.MobiusReciprocalSquares.mobiusTail (Real.sqrt x) := by ring
  rw [hid]
  exact (abs_sub _ _).trans ((add_le_add hf hb).trans_eq (by ring))

theorem squarefree_asymptotic : SquarefreeAsymptotic := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)] using
    squarefree_error_bound x hx

end P203.Ch03.SquarefreeAverage
