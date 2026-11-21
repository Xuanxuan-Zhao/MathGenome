import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorDigitSurjection
import MathGenome.Internal.RealAnalysis.D11.Ch03.CantorFunction

noncomputable section
open Set
open D11.Ch03.CantorStaircase

namespace D11.Ch22.CantorDigitSurjection

def alpha : ℝ := Real.log 2 / Real.log 3

theorem alpha_bounds : Specs.D11.Ch22.CantorDigitSurjection.alpha_bounds := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact ⟨div_pos h2 h3, (div_lt_one h3).mpr (Real.log_lt_log (by norm_num) (by norm_num))⟩

theorem three_rpow_alpha : Specs.D11.Ch22.CantorDigitSurjection.three_rpow_alpha := by
  change (3 : ℝ) ^ (Real.log 2 / Real.log 3) = 2
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [mul_div_cancel₀ _ h3, Real.exp_log (by norm_num)]

def F (x : Ch03.CantorSet.C) : ℝ := Ch03.CantorFunction.Gamma x

/-- The positional sums are exactly the upstream encodings. -/
theorem ternary_series (a : ℕ → Bool) :
    (∑' n, (if a n then (2 : ℝ) else 0) / 3 ^ (n + 1)) = ternary a := by
  unfold ternary Real.ofDigits
  apply tsum_congr
  intro n
  cases h : a n <;> simp [Real.ofDigitsTerm, h, div_eq_mul_inv]

theorem binary_series (a : ℕ → Bool) :
    (∑' n, (if a n then (1 : ℝ) else 0) / 2 ^ (n + 1)) = binary a := by
  unfold binary Real.ofDigits
  apply tsum_congr
  intro n
  cases h : a n <;> simp [Real.ofDigitsTerm, h, div_eq_mul_inv]

/-- This uses the inverse of the canonical Cantor digit equivalence. -/
theorem ternary_injective : Function.Injective ternary := by
  intro a b h
  have heq : cantorSetEquivNatToBool.symm a = cantorSetEquivNatToBool.symm b :=
    Subtype.ext h
  exact cantorSetEquivNatToBool.symm.injective heq

theorem unique_digits : Specs.D11.Ch22.CantorDigitSurjection.unique_digits := by
  intro x hx
  let a := cantorSetEquivNatToBool ⟨x, hx⟩
  have ha : ternary a = x := congrArg Subtype.val
    (cantorSetEquivNatToBool.symm_apply_apply ⟨x, hx⟩)
  refine ⟨a, (ternary_series a).trans ha, ?_⟩
  intro b hb
  exact ternary_injective (((ternary_series b).symm.trans hb).trans ha.symm)

theorem allowed_series_mem : Specs.D11.Ch22.CantorDigitSurjection.allowed_series_mem := by
  intro a
  rw [ternary_series]
  exact Ch03.CantorFunction.ternary_mem_C a

theorem F_digit_formula : Specs.D11.Ch22.CantorDigitSurjection.F_digit_formula := by
  intro x a ha
  change Ch03.CantorFunction.Gamma x = _
  rw [← ha]
  exact Ch03.CantorFunction.digit_formula a

theorem F_range : Specs.D11.Ch22.CantorDigitSurjection.F_range := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact Ch03.CantorFunction.Gamma_bounds x
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Ch03.CantorFunction.cantor_surjective hy
    exact ⟨⟨x, hx⟩, hxy⟩

theorem ternary_false : ternary (fun _ => false) = 0 := by
  simp [ternary, Real.ofDigits, Real.ofDigitsTerm]

theorem ternary_true : ternary (fun _ => true) = 1 :=
  Real.ofDigits_const_last_eq_one 2

theorem binary_false : binary (fun _ => false) = 0 := by
  simp [binary, Real.ofDigits, Real.ofDigitsTerm]

theorem binary_true : binary (fun _ => true) = 1 :=
  Real.ofDigits_const_last_eq_one 1

theorem endpoints : Specs.D11.Ch22.CantorDigitSurjection.endpoints := by
  refine ⟨zero_mem_cantorSet, ?_, ?_, ?_, Ch03.CantorFunction.endpoints⟩
  · rw [← ternary_true]
    exact Ch03.CantorFunction.ternary_mem_C _
  · exact (ternary_series _).trans ternary_false
  · exact (ternary_series _).trans ternary_true

/-- The two binary expansions of one half: 0.0111… and 0.1000…. -/
private def leftGapDigits : ℕ → Bool := fun n => decide (n ≠ 0)
private def rightGapDigits : ℕ → Bool := fun n => decide (n = 0)

private theorem gap_values :
    ternary leftGapDigits = 1 / 3 ∧ binary leftGapDigits = 1 / 2 ∧
    ternary rightGapDigits = 2 / 3 ∧ binary rightGapDigits = 1 / 2 := by
  have ht (a : ℕ → Bool) : ternary a =
      ((if a 0 then 2 else 0) + ternary (fun n => a (n + 1))) / 3 := by
    rw [ternary, Real.ofDigits_eq_sum_add_ofDigits _ 1]
    cases h : a 0 <;> simp [Real.ofDigitsTerm, ternary, h] <;> ring
  have hb (a : ℕ → Bool) : binary a =
      ((if a 0 then 1 else 0) + binary (fun n => a (n + 1))) / 2 := by
    rw [binary, Real.ofDigits_eq_sum_add_ofDigits _ 1]
    cases h : a 0 <;> simp [Real.ofDigitsTerm, binary, h] <;> ring
  have hlt : (fun n => leftGapDigits (n + 1)) = (fun _ => true) := by
    funext n
    simp [leftGapDigits]
  have hrt : (fun n => rightGapDigits (n + 1)) = (fun _ => false) := by
    funext n
    simp [rightGapDigits]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht, hlt, ternary_true]
    norm_num [leftGapDigits]
  · rw [hb, hlt, binary_true]
    norm_num [leftGapDigits]
  · rw [ht, hrt, ternary_false]
    norm_num [rightGapDigits]
  · rw [hb, hrt, binary_false]
    norm_num [rightGapDigits]

theorem binary_ambiguity : Specs.D11.Ch22.CantorDigitSurjection.binary_ambiguity := by
  obtain ⟨htl, hbl, htr, hbr⟩ := gap_values
  refine ⟨?_, ?_, by norm_num, ?_, ?_⟩
  · rw [← htl]
    exact Ch03.CantorFunction.ternary_mem_C _
  · rw [← htr]
    exact Ch03.CantorFunction.ternary_mem_C _
  · change Ch03.CantorFunction.Gamma (1 / 3) = 1 / 2
    rw [← htl, Ch03.CantorFunction.Gamma_ternary, hbl]
  · change Ch03.CantorFunction.Gamma (2 / 3) = 1 / 2
    rw [← htr, Ch03.CantorFunction.Gamma_ternary, hbr]

end D11.Ch22.CantorDigitSurjection
