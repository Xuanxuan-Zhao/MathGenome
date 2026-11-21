import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorSharpHolder
import MathGenome.Internal.RealAnalysis.D11.Ch22.CantorDigitSurjection
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

noncomputable section
open Set Filter
open scoped Topology
open D11.Ch03.CantorStaircase

namespace D11.Ch22.CantorSharpHolder
open CantorDigitSurjection

local notation "α" => CantorDigitSurjection.alpha

lemma alpha_pos : 0 < α := alpha_bounds.1
lemma alpha_le_one : α ≤ 1 := alpha_bounds.2.le
lemma three_pow : (3 : ℝ) ^ α = 2 := three_rpow_alpha

lemma rpow_third (u : ℝ) (hu : 0 ≤ u) : (u / 3) ^ α = u ^ α / 2 := by
  rw [Real.div_rpow hu (by norm_num), three_pow]

/-- Concavity compares the two inner points 1 and 2+u with the outer points u and 3.
Adding the two Jensen inequalities avoids differentiating at zero. -/
lemma right_branch_power {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    1 + u ^ α ≤ (2 + u) ^ α := by
  have hd : 0 < 3 - u := by linarith [hu.2]
  let a := 2 / (3 - u)
  let b := (1 - u) / (3 - u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hu.2) hd.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have h₁ : a * u + b * 3 = 1 := by dsimp [a, b]; field_simp; ring
  have h₂ : b * u + a * 3 = 2 + u := by dsimp [a, b]; field_simp; ring
  have hc := Real.concaveOn_rpow alpha_pos.le alpha_le_one
  have h := hc.2 hu.1 (by norm_num : (3 : ℝ) ∈ Ici 0) ha hb hab
  have h' := hc.2 hu.1 (by norm_num : (3 : ℝ) ∈ Ici 0) hb ha (by linarith : b + a = 1)
  simp only [smul_eq_mul, h₁, h₂, Real.one_rpow, three_pow] at h h'
  have hs : (a + b) * u ^ α + (a + b) * 2 ≤ 1 + (2 + u) ^ α := by
    nlinarith only [h, h']
  rw [hab] at hs
  linarith

lemma ternary_head (a : ℕ → Bool) : ternary a =
    ((if a 0 then 2 else 0) + ternary (fun n => a (n + 1))) / 3 := by
  rw [ternary, Real.ofDigits_eq_sum_add_ofDigits _ 1]
  cases h : a 0 <;> simp [Real.ofDigitsTerm, ternary, h] <;> ring

lemma binary_head (a : ℕ → Bool) : binary a =
    ((if a 0 then 1 else 0) + binary (fun n => a (n + 1))) / 2 := by
  rw [binary, Real.ofDigits_eq_sum_add_ofDigits _ 1]
  cases h : a 0 <;> simp [Real.ofDigitsTerm, binary, h] <;> ring

lemma ternary_bounds (a : ℕ → Bool) : ternary a ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

lemma binary_bounds (a : ℕ → Bool) : binary a ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

/-- A uniform error is halved whenever one digit is removed. -/
lemma endpoint_with_error (n : ℕ) (a : ℕ → Bool) :
    binary a ≤ (ternary a) ^ α + (1 / 2 : ℝ) ^ n := by
  induction n generalizing a with
  | zero =>
    have := (binary_bounds a).2
    have := Real.rpow_nonneg (ternary_bounds a).1 α
    simpa only [pow_zero] using (by linarith : binary a ≤ (ternary a) ^ α + 1)
  | succ n ih =>
    let t := fun k => a (k + 1)
    have hi := ih t
    have ht := ternary_bounds t
    rw [binary_head a, ternary_head a]
    cases h : a 0
    · simp only [Bool.false_eq_true, ite_false, zero_add]
      rw [rpow_third _ ht.1, pow_succ]
      dsimp [t] at hi ht ⊢
      linarith
    · simp only [ite_true]
      rw [rpow_third _ (by linarith [ht.1]), pow_succ]
      have hr := right_branch_power ht
      dsimp [t] at hi ht hr ⊢
      linarith

lemma binary_le_ternary_power (a : ℕ → Bool) : binary a ≤ (ternary a) ^ α := by
  have hlim : Tendsto (fun n : ℕ => (ternary a) ^ α + (1 / 2 : ℝ) ^ n)
      atTop (𝓝 ((ternary a) ^ α)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => endpoint_with_error n a)

lemma ternary_reflect (a : ℕ → Bool) :
    ternary a + ternary (fun n => !(a n)) = 1 := by
  rw [← ternary_true]
  unfold ternary Real.ofDigits
  rw [← Summable.tsum_add Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm]
  apply tsum_congr
  intro n
  cases h : a n <;> simp [Real.ofDigitsTerm, h]

lemma binary_reflect (a : ℕ → Bool) :
    binary a + binary (fun n => !(a n)) = 1 := by
  rw [← binary_true]
  unfold binary Real.ofDigits
  rw [← Summable.tsum_add Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm]
  apply tsum_congr
  intro n
  cases h : a n <;> simp [Real.ofDigitsTerm, h]

lemma one_sub_binary_le (a : ℕ → Bool) :
    1 - binary a ≤ (1 - ternary a) ^ α := by
  have ht := ternary_reflect a
  have hb := binary_reflect a
  have hi := binary_le_ternary_power (fun n => !(a n))
  rwa [show ternary (fun n => !(a n)) = 1 - ternary a by linarith,
    show binary (fun n => !(a n)) = 1 - binary a by linarith] at hi

/-- The opposite-branch estimate is exact, by midpoint concavity and the
inequality ((1-u)+v)/2 ≤ (2+v-u)/3 for u,v in [0,1]. -/
lemma cross_branch (a b : ℕ → Bool) :
    (1 + binary b - binary a) / 2 ≤
      ((2 + ternary b - ternary a) / 3) ^ α := by
  have ha := ternary_bounds a
  have hb := ternary_bounds b
  have hA : 0 ≤ 1 - ternary a := sub_nonneg.mpr ha.2
  have hc := (Real.concaveOn_rpow alpha_pos.le alpha_le_one).2
    hA hb.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hc
  calc
    (1 + binary b - binary a) / 2 ≤
        ((1 - ternary a) ^ α + (ternary b) ^ α) / 2 := by
      linarith [one_sub_binary_le a, binary_le_ternary_power b]
    _ ≤ (((1 - ternary a) + ternary b) / 2) ^ α := by
      convert hc using 1 <;> congr 1 <;> ring
    _ ≤ ((2 + ternary b - ternary a) / 3) ^ α := by
      apply Real.rpow_le_rpow (by linarith [hb.1]) _ alpha_pos.le
      linarith [ha.1, hb.2]

lemma same_branch_bound {u v p q e : ℝ}
    (h : |q - p| ≤ |v - u| ^ α + e) (c d : ℝ) :
    |(c + q) / 2 - (c + p) / 2| ≤
      |(d + v) / 3 - (d + u) / 3| ^ α + e / 2 := by
  rw [show (c + q) / 2 - (c + p) / 2 = (q - p) / 2 by ring,
    show (d + v) / 3 - (d + u) / 3 = (v - u) / 3 by ring,
    abs_div, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [rpow_third _ (abs_nonneg _)]
  linarith

lemma pair_with_error (n : ℕ) (a b : ℕ → Bool) :
    |binary b - binary a| ≤ |ternary b - ternary a| ^ α + (1 / 2 : ℝ) ^ n := by
  induction n generalizing a b with
  | zero =>
    have ha := binary_bounds a
    have hb := binary_bounds b
    have h : |binary b - binary a| ≤ 1 := abs_le.mpr (by constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
    have := Real.rpow_nonneg (abs_nonneg (ternary b - ternary a)) α
    simpa only [pow_zero] using (by linarith :
      |binary b - binary a| ≤ |ternary b - ternary a| ^ α + 1)
  | succ n ih =>
    let a' := fun k => a (k + 1)
    let b' := fun k => b (k + 1)
    have he : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n / 2 := by
      rw [pow_succ]; ring
    by_cases hh : a 0 = b 0
    · have h := same_branch_bound (ih a' b')
        (if a 0 then 1 else 0) (if a 0 then 2 else 0)
      rw [binary_head a, binary_head b, ternary_head a, ternary_head b, ← hh, he]
      exact h
    · have hea := binary_head a
      have heb := binary_head b
      have hta := ternary_head a
      have htb := ternary_head b
      have ha := binary_bounds a'
      have hb := binary_bounds b'
      have hta' := ternary_bounds a'
      have htb' := ternary_bounds b'
      cases h₀ : a 0 <;> cases h₁ : b 0
      · exact (hh (h₀.trans h₁.symm)).elim
      · have h := cross_branch a' b'
        simp only [h₀, Bool.false_eq_true, ite_false, zero_add] at hea hta
        simp only [h₁, ite_true] at heb htb
        rw [hea, heb, hta, htb]
        rw [abs_of_nonneg (by dsimp [a', b'] at *; linarith [ha.2, hb.1]),
          abs_of_nonneg (by dsimp [a', b'] at *; linarith [hta'.2, htb'.1])]
        have h' : (1 + binary b') / 2 - binary a' / 2 ≤
            ((2 + ternary b') / 3 - ternary a' / 3) ^ α := by
          convert h using 1 <;> congr 1 <;> ring
        exact h'.trans (le_add_of_nonneg_right (by positivity))
      · have h := cross_branch b' a'
        simp only [h₀, ite_true] at hea hta
        simp only [h₁, Bool.false_eq_true, ite_false, zero_add] at heb htb
        rw [hea, heb, hta, htb]
        rw [abs_of_nonpos (by dsimp [a', b'] at *; linarith [ha.1, hb.2]),
          abs_of_nonpos (by dsimp [a', b'] at *; linarith [hta'.1, htb'.2])]
        have h' : -(binary b' / 2 - (1 + binary a') / 2) ≤
            (-(ternary b' / 3 - (2 + ternary a') / 3)) ^ α := by
          convert h using 1 <;> congr 1 <;> ring
        exact h'.trans (le_add_of_nonneg_right (by positivity))
      · exact (hh (h₀.trans h₁.symm)).elim

lemma digit_sharp_holder (a b : ℕ → Bool) :
    |binary b - binary a| ≤ |ternary b - ternary a| ^ α := by
  have hlim : Tendsto (fun n : ℕ => |ternary b - ternary a| ^ α + (1 / 2 : ℝ) ^ n)
      atTop (𝓝 (|ternary b - ternary a| ^ α)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => pair_with_error n a b)

/-- Every existing Cantor point is decoded using the upstream unique expansion. -/
lemma exists_digits (x : ↥Specs.D11.Ch03.CantorSet.C_value) :
    ∃ a : ℕ → Bool, ternary a = (x : ℝ) ∧
      binary a = Specs.D11.Ch22.CantorDigitSurjection.F_value x := by
  obtain ⟨a, ha, _⟩ := unique_digits x x.property
  refine ⟨a, (ternary_series a).symm.trans ha, ?_⟩
  exact (binary_series a).symm.trans (F_digit_formula x a ha).symm

theorem endpoint_upper : Specs.D11.Ch22.CantorSharpHolder.endpoint_upper := by
  intro x
  obtain ⟨a, ha, hb⟩ := exists_digits x
  change Specs.D11.Ch22.CantorDigitSurjection.F_value x ≤ (x : ℝ) ^ α
  simpa only [ha, hb] using binary_le_ternary_power a

theorem endpoint_lower : Specs.D11.Ch22.CantorSharpHolder.endpoint_lower := by
  intro x
  obtain ⟨a, ha, hb⟩ := exists_digits x
  change 1 - Specs.D11.Ch22.CantorDigitSurjection.F_value x ≤ (1 - (x : ℝ)) ^ α
  simpa only [ha, hb] using one_sub_binary_le a

theorem sharp_holder : Specs.D11.Ch22.CantorSharpHolder.sharp_holder := by
  intro x y
  obtain ⟨a, ha, hfa⟩ := exists_digits x
  obtain ⟨b, hb, hfb⟩ := exists_digits y
  change |Specs.D11.Ch22.CantorDigitSurjection.F_value y -
    Specs.D11.Ch22.CantorDigitSurjection.F_value x| ≤ |(y : ℝ) - (x : ℝ)| ^ α
  simpa only [ha, hb, hfa, hfb] using digit_sharp_holder a b

end D11.Ch22.CantorSharpHolder
