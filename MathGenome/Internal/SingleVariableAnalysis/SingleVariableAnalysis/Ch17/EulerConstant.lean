import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EulerConstant
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Monotone

/-! Existence of Euler's constant from proper Riemann comparison.
Strict reciprocal rectangle bounds follow by splitting a unit interval at
its midpoint. Summing the upper increment bound gives log(n+1) ≤ H_n;
the lower increment bound makes H_n-log n decrease. Its positive lower
bound then permits the accepted monotone convergence theorem. -/
noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators
open Set Riemann

def harmonicSum : ℕ → ℝ := Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicSumValue

def eulerConstant : ℝ := Specs.SingleVariableAnalysis.Ch17.EulerConstant.eulerConstantValue

lemma harmonicSum_succ (n : ℕ) :
    harmonicSum (n+1) = harmonicSum n + 1 / ((n : ℝ)+1) := by
  exact Finset.sum_range_succ _ n

/-- Lower rectangle bound for an arbitrary proper Darboux integral. -/
lemma Riemann.mul_bound_le_realIntegral {f : ℝ → ℝ} {a b M : ℝ}
    (hf : RealIntegrable f a b) (hM : ∀ x ∈ Icc a b, M ≤ f x) :
    (b-a)*M ≤ realIntegral f hf := by
  obtain ⟨P⟩ := partition_exists hf.ordered
  apply le_trans _ (realIntegral_bounds f hf P).1
  have hl (i : Fin P.n) : M ≤ cellInfimum f P hf.bounded i := by
    apply (cell_bounds f P hf.bounded i).1.2
    rintro _ ⟨x, hx, rfl⟩
    exact hM x (cell_subset_interval P i hx)
  calc
    (b-a)*M = ∑ i : Fin P.n, M * cellLength P i := by
      rw [← Finset.mul_sum, sum_cellLength, mul_comm]
    _ ≤ lowerSum f P hf.bounded := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hl i) (cell_positive P i).le

/-- The logarithm difference is an actual proper integral on [a,b]. -/
lemma reciprocal_integral_eq_log_sub {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hi : RealIntegrable (fun t => 1/t) a b) :
    realIntegral _ hi = seriesLog b - seriesLog a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hia : RealIntegrable (fun t => 1/t) 1 a := reciprocal_riemann_integrable 1 a zero_lt_one ha
  have hib : RealIntegrable (fun t => 1/t) 1 b := reciprocal_riemann_integrable 1 b zero_lt_one (ha.trans hab)
  obtain ⟨hoa, hla⟩ := seriesLog_eq_oriented_integral a ha0
  obtain ⟨hob, hlb⟩ := seriesLog_eq_oriented_integral b hb0
  change seriesLog a = orientedRealIntegral _ hoa at hla
  change seriesLog b = orientedRealIntegral _ hob at hlb
  have hea : orientedRealIntegral (fun t => 1/t) hoa = realIntegral _ hia :=
    oriented_real_agreement _ ha hoa hia
  have heb : orientedRealIntegral (fun t => 1/t) hob = realIntegral _ hib :=
    oriented_real_agreement _ (ha.trans hab) hob hib
  rw [hea] at hla
  rw [heb] at hlb
  have hs := (real_split (fun t => 1/t) ha hab hib.bounded).2 hib hia hi
  change realIntegral _ hib = realIntegral _ hia + realIntegral _ hi at hs
  linarith

theorem logarithmic_increment_bounds : Specs.SingleVariableAnalysis.Ch17.EulerConstant.logIncrementBounds := by
  intro x hx
  change ∃ h : RealIntegrable (fun t => 1/t) x (x+1),
    realIntegral _ h = seriesLog (x+1) - seriesLog x ∧
    1/(x+1) < realIntegral _ h ∧ realIntegral _ h < 1/x ∧
    seriesLog (1+1/x) = seriesLog (x+1) - seriesLog x
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let m := x + 1/2
  have hxm : x ≤ m := by dsimp [m]; linarith
  have hmy : m ≤ x+1 := by dsimp [m]; linarith
  have hm0 : 0 < m := hx0.trans_le hxm
  have hy0 : 0 < x+1 := by linarith
  let hi : RealIntegrable (fun t => 1/t) x (x+1) := reciprocal_riemann_integrable x (x+1) hx0 (by linarith)
  let hl : RealIntegrable (fun t => 1/t) x m := reciprocal_riemann_integrable x m hx0 hxm
  let hr : RealIntegrable (fun t => 1/t) m (x+1) := reciprocal_riemann_integrable m (x+1) hm0 hmy
  have hs := (real_split (fun t => 1/t) hxm hmy hi.bounded).2 hi hl hr
  change realIntegral _ hi = realIntegral _ hl + realIntegral _ hr at hs
  have hll := mul_bound_le_realIntegral hl (fun t ht =>
    one_div_le_one_div_of_le (hx0.trans_le ht.1) ht.2)
  have hrl := mul_bound_le_realIntegral hr (fun t ht =>
    one_div_le_one_div_of_le (hm0.trans_le ht.1) ht.2)
  have hlu := realIntegral_le_mul_bound hl (fun t ht =>
    one_div_le_one_div_of_le hx0 ht.1)
  have hru := realIntegral_le_mul_bound hr (fun t ht =>
    one_div_le_one_div_of_le hm0 ht.1)
  have hrec1 : 1/(x+1) < 1/m := one_div_lt_one_div_of_lt hm0 (by dsimp [m]; linarith)
  have hrec2 : 1/m < 1/x := one_div_lt_one_div_of_lt hx0 (by dsimp [m]; linarith)
  have heq := reciprocal_integral_eq_log_sub hx (by linarith : x ≤ x+1) hi
  refine ⟨hi, heq, ?_, ?_, ?_⟩
  · dsimp [m] at hll hrl
    nlinarith
  · dsimp [m] at hlu hru
    nlinarith
  · have he : (1+1/x)*x = x+1 := by field_simp
    have hlog := seriesLog_mul (1+1/x) x (by positivity) hx0
    change seriesLog ((1+1/x)*x) = seriesLog (1+1/x) + seriesLog x at hlog
    rw [he] at hlog
    linarith

theorem harmonic_log_lower_bound : Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicLogLowerBound := by
  intro n
  change seriesLog ((n : ℝ)+1) ≤ harmonicSum n
  induction n with
  | zero =>
    have hone : seriesLog 1 = 0 := seriesLog_one
    simpa only [Nat.cast_zero, zero_add, harmonicSum,
      Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicSumValue,
      Finset.range_zero, Finset.sum_empty] using hone.le
  | succ n ih =>
    obtain ⟨hi, he, _, hu, _⟩ := logarithmic_increment_bounds ((n : ℝ)+1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
    change realIntegral _ hi = seriesLog ((n : ℝ)+1+1) - seriesLog ((n : ℝ)+1) at he
    change realIntegral _ hi < 1 / ((n : ℝ)+1) at hu
    rw [harmonicSum_succ]
    push_cast
    linarith

theorem harmonic_log_positive : Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicLogPositive := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hinc := seriesLog_strictMonoOn hn0 (by positivity : (0 : ℝ) < (n : ℝ)+1)
    (by linarith : (n : ℝ) < (n : ℝ)+1)
  change seriesLog (n : ℝ) < seriesLog ((n : ℝ)+1) at hinc
  have hbound := harmonic_log_lower_bound n
  change seriesLog ((n : ℝ)+1) ≤ harmonicSum n at hbound
  change 0 < harmonicSum n - seriesLog (n : ℝ)
  linarith

theorem harmonic_log_step : Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicLogStep := by
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hi, he, hl, _, _⟩ := logarithmic_increment_bounds (n : ℝ) hn1
  change realIntegral _ hi = seriesLog ((n : ℝ)+1) - seriesLog (n : ℝ) at he
  change harmonicSum (n+1) - seriesLog ((n : ℝ)+1) < harmonicSum n - seriesLog (n : ℝ)
  rw [harmonicSum_succ]
  linarith

theorem harmonic_log_antitone : Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicLogAntitone := by
  intro n hn k hk hnk
  change harmonicSum k - seriesLog (k : ℝ) ≤ harmonicSum n - seriesLog (n : ℝ)
  induction k, hnk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hnk ih =>
    have hs := harmonic_log_step k (hn.trans hnk)
    change harmonicSum (k+1) - seriesLog ((k : ℝ)+1) < harmonicSum k - seriesLog (k : ℝ) at hs
    push_cast
    exact hs.le.trans (ih (hn.trans hnk))

private lemma euler_difference_antitone :
    Antitone (fun n : ℕ => harmonicSum (n+1) - seriesLog ((n : ℝ)+1)) := by
  intro n k hnk
  have h := harmonic_log_antitone (show 1 ≤ n+1 by omega) (show 1 ≤ k+1 by omega)
      (Nat.add_le_add_right hnk 1)
  change harmonicSum (k+1) - seriesLog ((k+1 : ℕ) : ℝ) ≤
    harmonicSum (n+1) - seriesLog ((n+1 : ℕ) : ℝ) at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

private lemma euler_difference_bddBelow :
    BddBelow (Set.range (fun n : ℕ => harmonicSum (n+1) - seriesLog ((n : ℝ)+1))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h := (harmonic_log_positive (n+1) (by omega)).le
  change 0 ≤ harmonicSum (n+1) - seriesLog ((n+1 : ℕ) : ℝ) at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem harmonic_log_convergence : Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicLogConvergence := by
  have h := antitone_converges_to_infimum _ euler_difference_antitone euler_difference_bddBelow
  rw [real_infimum_eq_csInf] at h
  exact h

theorem harmonic_log_limit_exists : Specs.SingleVariableAnalysis.Ch17.EulerConstant.harmonicLogLimitExists := by
  refine ⟨eulerConstant, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := harmonic_log_convergence ε hε
  change ∀ n ≥ N, |harmonicSum (n+1) - seriesLog ((n : ℝ)+1) - eulerConstant| < ε at hN
  refine ⟨N+1, by omega, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
  have hk : N ≤ k := by omega
  change |harmonicSum (1+k) - seriesLog ((1+k : ℕ) : ℝ) - eulerConstant| < ε
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hN k hk

end SingleVariableAnalysis
