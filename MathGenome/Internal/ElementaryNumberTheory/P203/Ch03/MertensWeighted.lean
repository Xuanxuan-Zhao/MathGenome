import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.MertensWeighted
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace P203.MertensWeighted

open Finset
open P203Specs.MertensWeighted
open scoped ArithmeticFunction.vonMangoldt

/-- The weighted sum before removing higher prime powers. -/
noncomputable def mangoldtSum (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ)

/-- Summing the divisor identity gives the logarithm of the factorial. -/
theorem log_factorial_identity (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ n ∈ Ioc 0 N, Λ n * (N / n : ℕ) := by
  rw [← Real.sum_log_eq_log_factorial]
  simpa only [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply]
    using ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N

/-- All contributions outside the primes are summable. The library proof uses
prime-power indexing and a convergent geometric-series majorant. -/
theorem summable_higher_prime_powers :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ)) := by
  have hz (n : ℕ) : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simpa [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator, hz] using
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)

/-- Replacing integer quotients by real quotients costs at most ψ(N). -/
theorem factorial_quotient_bounds (N : ℕ) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * mangoldtSum N ∧
    (N : ℝ) * mangoldtSum N ≤ Real.log (N.factorial : ℝ) + Chebyshev.psi N := by
  have hmul : (N : ℝ) * mangoldtSum N =
      ∑ n ∈ Ioc 0 N, Λ n * ((N : ℝ) / n) := by
    simp only [mangoldtSum, mul_sum]
    apply sum_congr rfl
    intro n hn
    ring
  rw [hmul, log_factorial_identity]
  have hfloor (n : ℕ) (hn : 0 < n) :
      (N : ℝ) / n ≤ (N / n : ℕ) + 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ N hn).le)
  constructor
  · exact sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
  · rw [Chebyshev.psi, Nat.floor_natCast, ← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_left (hfloor n (mem_Ioc.mp hn).1)
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    simpa only [mul_add, mul_one] using h

/-- The full von Mangoldt weighted sum differs from log N by a bounded amount. -/
theorem mangoldtSum_bounds (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) - 1 ≤ mangoldtSum N ∧
    mangoldtSum N ≤ Real.log (N : ℝ) + (Real.log 4 + 4) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hl, hu⟩ := factorial_quotient_bounds N
  have hlow := Real.le_sum_log_nat N
  have hupp := Real.sum_log_le' h1
  rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial] at hupp
  rw [Real.sum_log_eq_log_factorial] at hlow
  have hpsi := Chebyshev.psi_le_const_mul_self hpos.le
  constructor <;> nlinarith

/-- The source prime sum is the prime part of the weighted Mangoldt sum. -/
theorem prime_sum_eq (x : ℝ) :
    M x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (if n.Prime then Λ n else 0) / (n : ℝ) := by
  classical
  unfold M P203Specs.PrimeProduct.primes
  have hsets : Nat.primesLE ⌊x⌋₊ = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext n
    simp only [Nat.mem_primesLE, mem_filter, mem_Ioc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  rw [hsets, sum_filter]
  apply sum_congr rfl
  intro n hn
  split_ifs with hp
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp

/-- A fixed finite constant bounding the contribution of higher prime powers. -/
noncomputable def higherPrimePowerTotal : ℝ :=
  ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)

private theorem higher_term_nonneg (n : ℕ) :
    0 ≤ (if n.Prime then 0 else Λ n) / (n : ℝ) := by
  positivity

theorem higherPrimePowerTotal_nonneg : 0 ≤ higherPrimePowerTotal :=
  tsum_nonneg higher_term_nonneg

/-- Removing the higher powers changes the weighted sum by a uniformly
bounded, nonnegative quantity, for every real cutoff. -/
theorem higher_prime_power_bound (x : ℝ) :
    0 ≤ mangoldtSum ⌊x⌋₊ - M x ∧
    mangoldtSum ⌊x⌋₊ - M x ≤ higherPrimePowerTotal := by
  classical
  have heq : mangoldtSum ⌊x⌋₊ = M x +
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (if n.Prime then 0 else Λ n) / (n : ℝ) := by
    rw [prime_sum_eq, ← sum_add_distrib]
    unfold mangoldtSum
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [heq, add_sub_cancel_left]
  exact ⟨sum_nonneg (fun n _ => higher_term_nonneg n),
    summable_higher_prime_powers.sum_le_tsum _ (fun n _ => higher_term_nonneg n)⟩

/-- A uniform bound already valid on the entire interval [2,∞). -/
theorem weightedPrimeSum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |M x - Real.log x| ≤ C := by
  refine ⟨higherPrimePowerTotal + (Real.log 4 + 4) + Real.log 2 + 1, ?_, ?_⟩
  · have := higherPrimePowerTotal_nonneg
    positivity
  intro x hx
  have hxpos : 0 < x := by linarith
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hxpos.le).mpr (by simpa using (show (1 : ℝ) ≤ x by linarith))
  have hNpos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hxN : x ≤ (⌊x⌋₊ : ℝ) * 2 := by
    have hf := Nat.lt_floor_add_one x
    have hn1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
    linarith
  have hlogl : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log hNpos hNx
  have hlogu : Real.log x ≤ Real.log (⌊x⌋₊ : ℝ) + Real.log 2 := by
    calc
      _ ≤ Real.log ((⌊x⌋₊ : ℝ) * 2) := Real.log_le_log hxpos hxN
      _ = _ := Real.log_mul hNpos.ne' (by norm_num)
  obtain ⟨hl, hu⟩ := mangoldtSum_bounds ⌊x⌋₊ hN
  obtain ⟨hel, heu⟩ := higher_prime_power_bound x
  have hT := higherPrimePowerTotal_nonneg
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- The first elementary Mertens estimate, with real upper limits. -/
theorem mertensWeighted : Estimate := by
  obtain ⟨C, hC, hb⟩ := weightedPrimeSum_bound
  exact ⟨C, hC, 2, hb⟩

end P203.MertensWeighted
