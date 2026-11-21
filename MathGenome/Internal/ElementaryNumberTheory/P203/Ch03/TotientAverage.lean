import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.TotientAverage
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.MobiusInversion
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.MobiusReciprocalSquares
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.HarmonicBasel
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped BigOperators Asymptotics
open P203Specs.ClassicalFunctions P203Specs.Ch03.TotientAverage

namespace P203.Ch03.TotientAverage

/-- The floor cutoff is exactly the source's positive-integer real cutoff,
including empty sums when x is negative. -/
lemma mem_summatory_indices (x : ℝ) (n : ℕ) :
    n ∈ Finset.Ioc 0 ⌊x⌋₊ ↔ 0 < n ∧ (n : ℝ) ≤ x := by
  by_cases hx : 0 ≤ x
  · simp only [Finset.mem_Ioc, Nat.le_floor_iff hx]
  · have hn : ¬(n : ℝ) ≤ x :=
      not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hx) (Nat.cast_nonneg n))
    simp [Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hx)), hn]

lemma sum_id (N : ℕ) :
    (∑ m ∈ Finset.Ioc 0 N, (m : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih]
    push_cast
    ring

/-- Sum the accepted totient convolution using Mathlib’s finite convolution identity. -/
lemma summatory_convolution (x : ℝ) :
    summatory x = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
      (mu d : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) + 1) / 2) := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    mu (idK 1 : ArithmeticFunction ℤ) ⌊x⌋₊
  rw [← P203.MobiusInversion.totientConvolution] at h
  have h' : summatory x = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
      (mu d : ℝ) * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / d), (m : ℝ) := by
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.pow_apply] at h
    have hr := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at hr
    exact hr
  rw [h']
  simp_rw [sum_id, Nat.floor_div_natCast]

lemma triangular_floor_error (y : ℝ) (hy : 0 ≤ y) :
    |(⌊y⌋₊ : ℝ) * ((⌊y⌋₊ : ℝ) + 1) / 2 - y ^ 2 / 2| ≤ y := by
  have hlo := Nat.floor_le hy
  have hhi := Nat.lt_floor_add_one y
  have hn : 0 ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (by linarith : 0 ≤ y + (⌊y⌋₊ : ℝ)),
      mul_nonneg (by linarith : 0 ≤ (⌊y⌋₊ : ℝ) + 1 - y) (by linarith : 0 ≤ y + (⌊y⌋₊ : ℝ))]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (by linarith : 0 ≤ y + (⌊y⌋₊ : ℝ))]

/-- The finite main coefficient, using exactly the source's integer Möbius function. -/
noncomputable def partialCoefficient (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, (mu d : ℝ) / (d : ℝ) ^ 2

lemma summatory_rounding_bound (x : ℝ) (hx : 0 ≤ x) :
    |summatory x - x ^ 2 / 2 * partialCoefficient x| ≤
      x * P203Specs.Ch03.harmonicNumber ⌊x⌋₊ := by
  rw [summatory_convolution, partialCoefficient, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        |(mu d : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) *
          ((⌊x / (d : ℝ)⌋₊ : ℝ) + 1) / 2) -
          x ^ 2 / 2 * ((mu d : ℝ) / (d : ℝ) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, x * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : 0 < (d : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
      have herr := triangular_floor_error (x / (d : ℝ)) (div_nonneg hx hd0.le)
      have heq : (mu d : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) *
          ((⌊x / (d : ℝ)⌋₊ : ℝ) + 1) / 2) -
          x ^ 2 / 2 * ((mu d : ℝ) / (d : ℝ) ^ 2) =
          (mu d : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) *
          ((⌊x / (d : ℝ)⌋₊ : ℝ) + 1) / 2 - (x / (d : ℝ)) ^ 2 / 2) := by ring
      rw [heq, abs_mul]
      calc
        _ ≤ 1 * (x / (d : ℝ)) :=
          mul_le_mul (P203.Ch03.MobiusReciprocalSquares.abs_mu_le d) herr
            (abs_nonneg _) (by norm_num)
        _ = x * (1 / (d : ℝ)) := by ring
    _ = x * P203Specs.Ch03.harmonicNumber ⌊x⌋₊ := by
      rw [← Finset.mul_sum]
      rfl

lemma coefficient_add_tail (x : ℝ) (hx : 0 ≤ x) :
    partialCoefficient x + P203Specs.Ch03.MobiusReciprocalSquares.mobiusTail x =
      6 / Real.pi ^ 2 := by
  let f : ℕ → ℝ := fun n => (mu n : ℝ) / (n : ℝ) ^ 2
  have hs : Summable f := (summable_nat_add_iff 1).mp
    P203.Ch03.MobiusReciprocalSquares.mobius_summable
  have hv : (∑' n, f n) = 6 / Real.pi ^ 2 := by
    rw [tsum_eq_zero_add' (f := f) P203.Ch03.MobiusReciprocalSquares.mobius_summable]
    simpa [f, P203Specs.Ch03.MobiusReciprocalSquares.mobiusTerm] using
      P203.Ch03.MobiusReciprocalSquares.mobius_hasSum.tsum_eq
  have h := hs.sum_add_tsum_subtype_compl (Finset.Ioc 0 ⌊x⌋₊)
  have ht : (∑' n : {n // n ∉ Finset.Ioc 0 ⌊x⌋₊}, f n) =
      ∑' n, ({n | n ∉ Finset.Ioc 0 ⌊x⌋₊} : Set ℕ).indicator f n :=
    tsum_subtype ({n | n ∉ Finset.Ioc 0 ⌊x⌋₊} : Set ℕ) f
  rw [ht] at h
  have he (n : ℕ) :
      ({n | n ∉ Finset.Ioc 0 ⌊x⌋₊} : Set ℕ).indicator f n =
        (if x < (n : ℝ) then f n else 0) := by
    by_cases hn : n = 0
    · subst n
      simp [f]
    · simp [Set.indicator, Finset.mem_Ioc, Nat.pos_of_ne_zero hn,
        Nat.le_floor_iff hx, not_le]
  simp_rw [he] at h
  rw [hv] at h
  exact h

lemma coefficient_error_bound (x : ℝ) (hx : 1 ≤ x) :
    |partialCoefficient x - 6 / Real.pi ^ 2| ≤ 2 / x := by
  have h := coefficient_add_tail x (by linarith)
  have he : partialCoefficient x - 6 / Real.pi ^ 2 =
      -P203Specs.Ch03.MobiusReciprocalSquares.mobiusTail x := by linarith
  rw [he, abs_neg]
  exact (P203.Ch03.MobiusReciprocalSquares.mobius_tail_bound x hx).2

lemma main_term_error_bound (x : ℝ) (hx : 1 ≤ x) :
    |x ^ 2 / 2 * partialCoefficient x - (3 / Real.pi ^ 2) * x ^ 2| ≤ x := by
  have hx0 : 0 < x := by linarith
  calc
    _ = x ^ 2 / 2 * |partialCoefficient x - 6 / Real.pi ^ 2| := by
      calc
        _ = |x ^ 2 / 2 * (partialCoefficient x - 6 / Real.pi ^ 2)| := by
          congr 1
          ring
        _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 / 2)]
    _ ≤ x ^ 2 / 2 * (2 / x) :=
      mul_le_mul_of_nonneg_left (coefficient_error_bound x hx) (by positivity)
    _ = x := by field_simp

/-- A uniform estimate for every real x ≥ 1, before absorbing the linear error. -/
lemma error_bound (x : ℝ) (hx : 1 ≤ x) :
    |summatory x - (3 / Real.pi ^ 2) * x ^ 2| ≤ x * (2 + Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  have hh : P203Specs.Ch03.harmonicNumber ⌊x⌋₊ ≤ 1 + Real.log x := by
    rw [P203.Ch03.HarmonicBasel.harmonic_eq_mathlib]
    exact harmonic_floor_le_one_add_log x hx
  calc
    _ ≤ |summatory x - x ^ 2 / 2 * partialCoefficient x| +
        |x ^ 2 / 2 * partialCoefficient x - (3 / Real.pi ^ 2) * x ^ 2| :=
      abs_sub_le _ _ _
    _ ≤ x * P203Specs.Ch03.harmonicNumber ⌊x⌋₊ + x :=
      add_le_add (summatory_rounding_bound x hx0) (main_term_error_bound x hx)
    _ ≤ x * (1 + Real.log x) + x := by gcongr
    _ = x * (2 + Real.log x) := by ring

theorem totient_asymptotic : P203Specs.Ch03.TotientAverage.TotientAsymptotic := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hx1 : 1 ≤ x := he.trans hx
  have hl : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ Real.log x))]
  calc
    _ ≤ x * (2 + Real.log x) := error_bound x hx1
    _ ≤ 3 * (x * Real.log x) := by nlinarith

end P203.Ch03.TotientAverage
