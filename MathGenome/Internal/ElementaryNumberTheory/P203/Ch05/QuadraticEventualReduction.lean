import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticEventualReduction
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticSurdRecurrence
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ReducedPredecessors
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ContinuedFractionErrors

namespace P203

open private minpoly_quadratic_equation from MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticContinuedFractions

/-- All iterates remain quadratic, without any reducedness assumption. -/
theorem quadratic_iterate (x : ℝ) (hx : P203Specs.QuadraticIrrational x) (n : ℕ) :
    P203Specs.QuadraticIrrational (P203Specs.continuedFractionStep^[n] x) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (quadratic_step _ ih).1

/-- The conjugates cannot remain nonnegative forever: otherwise the original
number and its other root would have the same infinite canonical digit string. -/
theorem quadratic_conjugate_eventually_negative (x : ℝ)
    (hx : P203Specs.QuadraticIrrational x) :
    ∃ n : ℕ, P203Specs.quadraticConjugate (P203Specs.continuedFractionStep^[n] x) < 0 := by
  classical
  by_contra! hnonneg
  let u : ℕ → ℝ := fun n => P203Specs.continuedFractionStep^[n] x
  let v : ℕ → ℝ := fun n => P203Specs.quadraticConjugate (u n)
  have hq (n : ℕ) : P203Specs.QuadraticIrrational (u n) := quadratic_iterate x hx n
  have hv (n : ℕ) : 0 < v n :=
    lt_of_le_of_ne (hnonneg n) (Ne.symm (quadratic_other_root _ (hq n)).1.ne_zero)
  have hrec (n : ℕ) : v (n + 1) = 1 / (v n - (⌊u n⌋ : ℝ)) := by
    simpa only [v, u, Function.iterate_succ_apply'] using (quadratic_step (u n) (hq n)).2
  have hlarge (n : ℕ) : (⌊u n⌋ : ℝ) < v n := by
    have hp : 0 < 1 / (v n - (⌊u n⌋ : ℝ)) := by rw [← hrec]; exact hv (n + 1)
    exact sub_pos.mp (one_div_pos.mp hp)
  have hv1 (n : ℕ) : 1 < v (n + 1) := by
    have hu1 : 1 < u (n + 1) :=
      later_completeQuotients x _ (n + 1) (by omega)
        (quotient_iterates x (quadratic_is_irrational x hx) (n + 1)).2.1
    have ha : (1 : ℝ) ≤ (⌊u (n + 1)⌋ : ℝ) := by
      exact_mod_cast (Int.le_floor.mpr (by simpa using hu1.le) : (1 : ℤ) ≤ ⌊u (n + 1)⌋)
    exact lt_of_le_of_lt ha (hlarge (n + 1))
  have hf (n : ℕ) : ⌊v n⌋ = ⌊u n⌋ := by
    apply Int.floor_eq_iff.mpr
    refine ⟨(hlarge n).le, ?_⟩
    have hp := sub_pos.mpr (hlarge n)
    have hb : 1 / (v n - (⌊u n⌋ : ℝ)) > 1 := by rw [← hrec]; exact hv1 n
    have hb' := (one_lt_div hp).mp hb
    linarith
  have hiter (n : ℕ) : P203Specs.continuedFractionStep^[n] (P203Specs.quadraticConjugate x) = v n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change 1 / (v n - (⌊v n⌋ : ℝ)) = v (n + 1)
      rw [hf, hrec]
  have heq : x = P203Specs.quadraticConjugate x := by
    apply infinite_digit_uniqueness x _ (quadratic_is_irrational x hx) (quadratic_other_root x hx).1
    intro n
    rw [(quotient_iterates x (quadratic_is_irrational x hx) n).2.2,
      (quotient_iterates _ (quadratic_other_root x hx).1 n).2.2, hiter, hf]
  exact (quadratic_other_root x hx).2.1 heq.symm

/-- One step after a negative conjugate at a positive index, all reduced
inequalities hold; the reduced-step theorem then preserves them forever. -/
theorem quadratic_eventual_reduction : P203Specs.QuadraticEventualReduction := by
  intro x hx
  let u : ℕ → ℝ := fun n => P203Specs.continuedFractionStep^[n] x
  have hq (n : ℕ) : P203Specs.QuadraticIrrational (u n) := quadratic_iterate x hx n
  have hu (n : ℕ) : 1 < u (n + 1) :=
    later_completeQuotients x _ (n + 1) (by omega)
      (quotient_iterates x (quadratic_is_irrational x hx) (n + 1)).2.1
  have hrec (n : ℕ) : P203Specs.quadraticConjugate (u (n + 1)) =
      1 / (P203Specs.quadraticConjugate (u n) - (⌊u n⌋ : ℝ)) := by
    simpa only [u, Function.iterate_succ_apply'] using (quadratic_step (u n) (hq n)).2
  -- Start at the first later quotient, where its floor is at least one.
  have hneg : ∃ n : ℕ, 1 ≤ n ∧ P203Specs.quadraticConjugate (u n) < 0 := by
    obtain ⟨m, hm⟩ := quadratic_conjugate_eventually_negative (u 1) (hq 1)
    refine ⟨m + 1, by omega, ?_⟩
    have he : P203Specs.continuedFractionStep^[m] (u 1) = u (m + 1) :=
      (Function.iterate_add_apply _ m 1 x).symm
    rw [← he]
    exact hm
  obtain ⟨n, hn, hnegative⟩ := hneg
  have ha : (1 : ℝ) ≤ (⌊u n⌋ : ℝ) := by
    have hn1 : 1 < u n := by
      exact later_completeQuotients x _ n hn
        (quotient_iterates x (quadratic_is_irrational x hx) n).2.1
    exact_mod_cast (Int.le_floor.mpr (by simpa using hn1.le) : (1 : ℤ) ≤ ⌊u n⌋)
  have hd : P203Specs.quadraticConjugate (u n) - (⌊u n⌋ : ℝ) < -1 := by linarith
  have hr : P203Specs.ReducedQuadratic (u (n + 1)) := by
    refine ⟨hq _, hu n, ?_, ?_⟩ <;> rw [hrec]
    · apply (lt_div_iff_of_neg (by linarith : P203Specs.quadraticConjugate (u n) - (⌊u n⌋ : ℝ) < 0)).mpr
      linarith
    · exact div_neg_of_pos_of_neg zero_lt_one (by linarith)
  have hred (j : ℕ) : P203Specs.ReducedQuadratic (u (n + 1 + j)) := by
    induction j with
    | zero => simpa using hr
    | succ j ih =>
      have h := (reduced_step _ ih).2.1
      change P203Specs.ReducedQuadratic (P203Specs.continuedFractionStep^[n + 1 + (j + 1)] x)
      rw [← Nat.add_assoc, Function.iterate_succ_apply']
      exact h
  refine ⟨n + 1, ?_⟩
  intro j hj
  refine ⟨u j, (quotient_iterates x (quadratic_is_irrational x hx) j).2.1, ?_⟩
  have h := hred (j - (n + 1))
  simpa only [Nat.add_sub_of_le hj] using h

/-- Clear the two rational coefficients of the monic minimal quadratic.
The leading integer coefficient is positive, hence nonzero. -/
theorem quadratic_integer_equation (x : ℝ) (hx : P203Specs.QuadraticIrrational x) :
    ∃ A B C : ℤ, 0 < A ∧ (A : ℝ) * x ^ 2 + (B : ℝ) * x + (C : ℝ) = 0 := by
  let b := (minpoly ℚ x).coeff 1
  let c := (minpoly ℚ x).coeff 0
  let A : ℤ := b.den * c.den
  let B : ℤ := b.num * c.den
  let C : ℤ := c.num * b.den
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  have hc : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  have hB : (A : ℝ) * (b : ℝ) = (B : ℝ) := by
    dsimp [A, B]
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hC : (A : ℝ) * (c : ℝ) = (C : ℝ) := by
    dsimp [A, C]
    rw [Rat.cast_def]
    push_cast
    field_simp
  refine ⟨A, B, C, ?_, ?_⟩
  · dsimp [A]
    exact mul_pos (by exact_mod_cast b.den_pos) (by exact_mod_cast c.den_pos)
  · have he := minpoly_quadratic_equation x hx
    change x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 at he
    linear_combination (A : ℝ) * he - x * hB - hC

/-- The quadratic formula with signed denominator includes both roots. -/
theorem quadratic_initial_surd (x : ℝ) (hx : P203Specs.QuadraticIrrational x) :
    ∃ D P Q : ℤ, 0 < D ∧ ¬ IsSquare D ∧ Q ≠ 0 ∧ Q ∣ D - P ^ 2 ∧
      x = ((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ) := by
  obtain ⟨A, B, C, hA, he⟩ := quadratic_integer_equation x hx
  let D : ℤ := B ^ 2 - 4 * A * C
  have hAr : (A : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hdisc : (D : ℝ) = (2 * (A : ℝ) * x + (B : ℝ)) ^ 2 := by
    dsimp [D]
    push_cast
    linear_combination -4 * (A : ℝ) * he
  have hlin : 2 * (A : ℝ) * x + (B : ℝ) ≠ 0 := by
    intro hz
    apply (quadratic_is_irrational x hx).ne_rat (- (B : ℚ) / (2 * (A : ℚ)))
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num) hAr)).mpr
    linarith
  have hD : 0 < D := by
    have hp : (0 : ℝ) < D := by rw [hdisc]; exact sq_pos_of_ne_zero hlin
    exact_mod_cast hp
  have hns : ¬ IsSquare D := by
    rintro ⟨k, hk⟩
    have hsq : (2 * (A : ℝ) * x + (B : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by
      rw [← hdisc, hk]
      push_cast
      ring
    obtain h | h := (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
    · apply (quadratic_is_irrational x hx).ne_rat (((k - B : ℤ) : ℚ) / (2 * (A : ℚ)))
      push_cast
      apply (eq_div_iff (mul_ne_zero (by norm_num) hAr)).mpr
      linarith
    · apply (quadratic_is_irrational x hx).ne_rat (((-k - B : ℤ) : ℚ) / (2 * (A : ℚ)))
      push_cast
      apply (eq_div_iff (mul_ne_zero (by norm_num) hAr)).mpr
      linarith
  have hsqrt : Real.sqrt (D : ℝ) = |2 * (A : ℝ) * x + (B : ℝ)| := by
    rw [hdisc, Real.sqrt_sq_eq_abs]
  by_cases hsign : 0 ≤ 2 * (A : ℝ) * x + (B : ℝ)
  · refine ⟨D, -B, 2 * A, hD, hns, by omega, ?_, ?_⟩
    · refine ⟨-2 * C, ?_⟩
      dsimp [D]
      ring
    · rw [hsqrt, abs_of_nonneg hsign]
      push_cast
      apply (eq_div_iff (mul_ne_zero (by norm_num) hAr)).mpr
      ring
  · refine ⟨D, B, -2 * A, hD, hns, by omega, ?_, ?_⟩
    · refine ⟨2 * C, ?_⟩
      dsimp [D]
      ring
    · rw [hsqrt, abs_of_neg (lt_of_not_ge hsign)]
      push_cast
      apply (eq_div_iff (mul_ne_zero (by norm_num) hAr)).mpr
      ring

/-- Propagate an admissible initial state along the same quotient map that
produces the canonical complete quotients, keeping its discriminant fixed. -/
theorem quadratic_surd_expansion : P203Specs.QuadraticSurdExpansion := by
  intro x hx
  obtain ⟨D, P₀, Q₀, hD, hns, hQ₀, hdvd₀, hx₀⟩ := quadratic_initial_surd x hx
  let update : ℤ × ℤ → ℤ × ℤ := fun t =>
    (P203Specs.surdNextP t.1 t.2 D, P203Specs.surdNextQ t.1 t.2 D)
  let state : ℕ → ℤ × ℤ := fun n => update^[n] (P₀, Q₀)
  let P : ℕ → ℤ := fun n => (state n).1
  let Q : ℕ → ℤ := fun n => (state n).2
  have hstate (n : ℕ) : state (n + 1) = update (state n) :=
    Function.iterate_succ_apply' update n (P₀, Q₀)
  have hP (n : ℕ) : P (n + 1) = P203Specs.surdNextP (P n) (Q n) D :=
    congrArg Prod.fst (hstate n)
  have hQ (n : ℕ) : Q (n + 1) = P203Specs.surdNextQ (P n) (Q n) D :=
    congrArg Prod.snd (hstate n)
  have hi (n : ℕ) : Q n ≠ 0 ∧ Q n ∣ D - P n ^ 2 ∧
      P203Specs.continuedFractionStep^[n] x =
        ((P n : ℝ) + Real.sqrt (D : ℝ)) / (Q n : ℝ) := by
    induction n with
    | zero => exact ⟨hQ₀, hdvd₀, hx₀⟩
    | succ n ih =>
      have hs := surd_recurrence (P n) (Q n) D hD hns ih.1 ih.2.1
      rw [hP, hQ]
      refine ⟨hs.1, hs.2.2.1, ?_⟩
      rw [Function.iterate_succ_apply', ih.2.2]
      exact hs.2.2.2
  refine ⟨D, P, Q, hD, hns, ?_, fun n => ⟨hP n, hQ n⟩⟩
  intro n
  refine ⟨(hi n).1, (hi n).2.1, ?_⟩
  rw [(quotient_iterates x (quadratic_is_irrational x hx) n).2.1, (hi n).2.2]

end P203
