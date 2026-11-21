import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.DivisorAverage
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.ClassicalFunctions
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Hyperbola
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.HarmonicBasel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter Finset P203Specs P203Specs.Ch03
open scoped Asymptotics BigOperators

namespace P203.Ch03.DivisorAverage

lemma summatory_one (t : ℝ) :
    summatory (restrictPositive (P203Specs.ClassicalFunctions.one : ArithmeticFunction ℝ)) t =
      (⌊t⌋₊ : ℝ) := by
  unfold summatory
  have he : zeroExtend (restrictPositive (P203Specs.ClassicalFunctions.one : ArithmeticFunction ℝ)) =
      (P203Specs.ClassicalFunctions.one : ArithmeticFunction ℝ) := (positiveEquiv ℝ).right_inv _
  rw [he]
  simp only [ArithmeticFunction.natCoe_apply]
  rw [← Nat.cast_sum, ArithmeticFunction.sum_Ioc_zeta]

/-- The real-cutoff hyperbola formula for the divisor counting function. -/
lemma divisor_hyperbola (x : ℝ) (hx : 0 ≤ x) :
    summatory (restrictPositive (P203Specs.ClassicalFunctions.tau : ArithmeticFunction ℝ)) x =
      2 * (∑ d ∈ Ioc 0 ⌊Real.sqrt x⌋₊, (⌊x / (d : ℝ)⌋₊ : ℝ)) -
      (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 := by
  let z := restrictPositive (P203Specs.ClassicalFunctions.one : ArithmeticFunction ℝ)
  have hc : positiveConvolution z z =
      restrictPositive (P203Specs.ClassicalFunctions.tau : ArithmeticFunction ℝ) := by
    rw [← P203.ClassicalFunctions.restrict_mul,
      P203.ClassicalFunctions.divisorConvolutions.1, ArithmeticFunction.natCoe_mul]
  have h := P203.Hyperbola.symmetricIdentity ℝ z z x hx
  change P203Specs.Hyperbola.Formula z z x _ _ at h
  unfold P203Specs.Hyperbola.Formula at h
  rw [hc] at h
  have hz (t : ℝ) : summatory z t = (⌊t⌋₊ : ℝ) := summatory_one t
  simp only [hz, Nat.floor_natCast] at h
  have he : (∑ d ∈ Ioc 0 ⌊Real.sqrt x⌋₊,
      zeroExtend z d * (⌊x / (d : ℝ)⌋₊ : ℝ)) =
      ∑ d ∈ Ioc 0 ⌊Real.sqrt x⌋₊, (⌊x / (d : ℝ)⌋₊ : ℝ) := by
    apply sum_congr rfl
    intro d hd
    have hd0 := (mem_Ioc.mp hd).1
    simp [z, zeroExtend, restrictPositive, hd0,
      ne_of_gt hd0]
  rw [he] at h
  nlinarith [h]

/-- Replacing each floor in the short sum costs at most the number of terms. -/
lemma floor_sum_error (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    |(∑ d ∈ Ioc 0 m, (⌊x / (d : ℝ)⌋₊ : ℝ)) - x * harmonicNumber m| ≤ m := by
  have he : x * harmonicNumber m = ∑ d ∈ Ioc 0 m, x / (d : ℝ) := by
    rw [harmonicNumber, mul_sum]
    have hi : Icc 1 m = Ioc 0 m := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [hi]
    apply sum_congr rfl
    intro d _
    simp [div_eq_mul_inv]
  rw [he, ← sum_sub_distrib]
  calc
    |∑ d ∈ Ioc 0 m, ((⌊x / (d : ℝ)⌋₊ : ℝ) - x / (d : ℝ))| ≤
        ∑ d ∈ Ioc 0 m, |(⌊x / (d : ℝ)⌋₊ : ℝ) - x / (d : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Ioc 0 m, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hxd : 0 ≤ x / (d : ℝ) := div_nonneg hx (Nat.cast_nonneg d)
      have hl := Nat.floor_le hxd
      have hu := Nat.lt_floor_add_one (x / (d : ℝ))
      rw [abs_of_nonpos (sub_nonpos.mpr hl)]
      linarith
    _ = (m : ℝ) := by simp

/-- A uniform error bound for all real x ≥ 1. -/
lemma divisor_error_bound (x : ℝ) (hx : 1 ≤ x) :
    |summatory (restrictPositive (P203Specs.ClassicalFunctions.tau : ArithmeticFunction ℝ)) x -
      (x * Real.log x + (2 * gamma - 1) * x)| ≤ 9 * Real.sqrt x := by
  let s := Real.sqrt x
  let m := ⌊s⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  have hs1 : 1 ≤ s := by nlinarith
  have hmle : (m : ℝ) ≤ s := Nat.floor_le hs0
  have hslt : s < (m : ℝ) + 1 := Nat.lt_floor_add_one s
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hm0, Nat.cast_zero] at hslt
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by positivity
  have hhalf : s ≤ 2 * (m : ℝ) := by linarith
  have hxm : x / (m : ℝ) ≤ 2 * s := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_nonneg hs0 (show 0 ≤ 2 * (m : ℝ) - s by linarith)]
  have hlog0 : 0 ≤ Real.log s - Real.log (m : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hm0 hmle)
  have hlog1 : Real.log s - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hm0)]
    calc
      Real.log (s / (m : ℝ)) ≤ s / (m : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 1 / (m : ℝ) := by
        apply (le_div_iff₀ hm0).mpr
        field_simp
        nlinarith
  have hh := HarmonicBasel.harmonic_error_bound m hm
  have hh1 : harmonicNumber m - Real.log (m : ℝ) - gamma ≤ 1 / (m : ℝ) :=
    (le_abs_self _).trans hh.2
  have hHerr : |harmonicNumber m - Real.log s - gamma| ≤ 1 / (m : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hh.1]
  have hHprod : |x * (harmonicNumber m - Real.log s - gamma)| ≤ 2 * s := by
    rw [abs_mul, abs_of_nonneg hx0]
    calc
      x * |harmonicNumber m - Real.log s - gamma| ≤ x * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hHerr hx0
      _ = x / (m : ℝ) := by ring
      _ ≤ 2 * s := hxm
  have hsquare : 0 ≤ x - (m : ℝ) ^ 2 ∧ x - (m : ℝ) ^ 2 ≤ 3 * s := by
    have hms : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    constructor
    · nlinarith [sq_le_sq₀ hms hs0 |>.mpr hmle]
    · have hupper : s ^ 2 < ((m : ℝ) + 1) ^ 2 := by
        nlinarith [sq_lt_sq₀ hs0 (by positivity : 0 ≤ (m : ℝ) + 1) |>.mpr hslt]
      nlinarith
  have hfloor := floor_sum_error x hx0 m
  have hid := divisor_hyperbola x hx0
  change summatory _ x = 2 * (∑ d ∈ Ioc 0 m, (⌊x / (d : ℝ)⌋₊ : ℝ)) -
    (m : ℝ) ^ 2 at hid
  have hlog : Real.log x = 2 * Real.log s := by
    dsimp [s]
    rw [Real.log_sqrt hx0]
    ring
  rw [hid, hlog]
  rcases abs_le.mp hfloor with ⟨hflo, hfhi⟩
  rcases abs_le.mp hHprod with ⟨hhlo, hhhi⟩
  apply abs_le.mpr
  constructor <;> nlinarith [hsquare.1, hsquare.2]

/-- The divisor average, including its second main term, at real infinity. -/
theorem asymptotic : P203Specs.Ch03.DivisorAverage.Asymptotic := by
  apply Asymptotics.IsBigO.of_bound 9
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)] using
    divisor_error_bound x hx

end P203.Ch03.DivisorAverage
