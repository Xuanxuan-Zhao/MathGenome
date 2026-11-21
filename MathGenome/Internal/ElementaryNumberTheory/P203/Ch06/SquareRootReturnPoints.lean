import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.SquareRootReturnPoints
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch06.PellConvergentNorm
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.PurePeriodicityCriterion

namespace P203
open P203Specs

noncomputable abbrev sqrtPeriod : SqrtPeriodType := P203Specs.sqrtPeriod

/-- Basic strict floor bounds, also covering nonsquare discriminants which
are not squarefree. -/
theorem sqrt_floor_bounds (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    1 < Real.sqrt (D : ℝ) ∧ 1 ≤ ⌊Real.sqrt (D : ℝ)⌋ ∧
    (⌊Real.sqrt (D : ℝ)⌋ : ℝ) < Real.sqrt (D : ℝ) ∧
    Real.sqrt (D : ℝ) < (⌊Real.sqrt (D : ℝ)⌋ : ℝ) + 1 := by
  have hD2 : 2 ≤ D := by
    by_contra! h
    have he : D = 1 := by omega
    exact hns (he ▸ (show IsSquare (1 : ℤ) from ⟨1, by norm_num⟩))
  have hs : 1 < Real.sqrt (D : ℝ) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    exact_mod_cast (show (1 : ℤ) < D by omega)
  have hi := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  exact ⟨hs, Int.le_floor.mpr (by simpa using hs.le),
    lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hi.ne_int _)), Int.lt_floor_add_one _⟩

/-- The reduced predecessor closing the square-root block is `sqrt D+a₀`. -/
theorem sqrt_closing_state (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    let s := Real.sqrt (D : ℝ)
    let a : ℤ := ⌊s⌋
    ReducedQuadratic (s + (a : ℝ)) ∧
      ⌊s + (a : ℝ)⌋ = 2 * a ∧
      P203Specs.continuedFractionStep (s + (a : ℝ)) = P203Specs.continuedFractionStep s := by
  dsimp only
  let s := Real.sqrt (D : ℝ)
  let a : ℤ := ⌊s⌋
  have hi : Irrational s := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  obtain ⟨hs, ha, has, hsa⟩ := sqrt_floor_bounds D hD hns
  have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsq : s ^ 2 = (D : ℝ) := Real.sq_sqrt (by exact_mod_cast hD.le)
  have hq := quadratic_of_monic_equation s 0 (- (D : ℚ)) hi (by
    push_cast
    nlinarith [hsq])
  have hy := quadratic_add_rat s hq.1 (a : ℚ)
  simp only [Rat.cast_intCast] at hy
  have hc : P203Specs.quadraticConjugate (s + (a : ℝ)) = -s + (a : ℝ) := by
    rw [hy.2, hq.2]
    norm_num
  have hf : ⌊s + (a : ℝ)⌋ = 2 * a := Int.floor_eq_iff.mpr (by
    push_cast
    constructor <;> dsimp [s, a] at * <;> linarith)
  refine ⟨⟨hy.1, by dsimp [s] at *; linarith, ?_, ?_⟩, hf, ?_⟩
  · rw [hc]
    dsimp [s, a] at *
    linarith
  · rw [hc]
    dsimp [s, a] at *
    linarith
  · change 1 / (s + (a : ℝ) - (⌊s + (a : ℝ)⌋ : ℝ)) = 1 / (s - (a : ℝ))
    rw [hf]
    push_cast
    congr 1
    ring

/-- From index one onward, the two quotient orbits agree. -/
theorem sqrt_orbit_closing (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D)
    (j : ℕ) (hj : 1 ≤ j) :
    P203Specs.continuedFractionStep^[j] (Real.sqrt (D : ℝ)) =
      P203Specs.continuedFractionStep^[j] (Real.sqrt (D : ℝ) + (⌊Real.sqrt (D : ℝ)⌋ : ℝ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
    (sqrt_closing_state D hD hns).2.2]

theorem sqrt_reduced_states : SqrtReducedStates := by
  intro D hD hns j hj
  have hi := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  obtain ⟨hQ, _, hquot⟩ := sqrt_state_valid D hD hns j
  have he : ((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ) =
      P203Specs.continuedFractionStep^[j] (Real.sqrt (D : ℝ)) :=
    Option.some.inj (hquot.symm.trans (quotient_iterates _ hi j).2.1)
  have hr : ReducedQuadratic
      (((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ)) := by
    rw [he, sqrt_orbit_closing D hD hns j hj]
    exact reduced_iterates _ (sqrt_closing_state D hD hns).1 j
  have hp := (reduced_surd_state_bounds _ _ D hD hns hQ hr).2.2.1
  exact ⟨by exact_mod_cast hp, hr, hquot⟩

/-- For an irrational input, a period of all canonical digits is exactly an
orbit return. The forward implication uses the upstream convergence theorem. -/
theorem canonical_digit_period_iff_return (x : ℝ) (hx : Irrational x) (r : ℕ) :
    (∀ n, P203Specs.partialQuotient x (n + r) = P203Specs.partialQuotient x n) ↔
      P203Specs.continuedFractionStep^[r] x = x := by
  refine ⟨quotient_returns_of_period x hx r, ?_⟩
  intro hr n
  rw [(quotient_iterates x hx (n + r)).2.2, (quotient_iterates x hx n).2.2,
    Function.iterate_add_apply, hr]

/-- Reduced quadratic irrationals have a positive least orbit period. -/
theorem reduced_minimalPeriod_pos (x : ℝ) (hx : ReducedQuadratic x) :
    0 < Function.minimalPeriod P203Specs.continuedFractionStep x := by
  obtain ⟨hi, r, hr, hd⟩ := (pure_periodicity_bridge x).mp (reduced_purely_periodic x hx)
  exact Function.IsPeriodicPt.minimalPeriod_pos hr (quotient_returns_of_period x hi r hd)

/-- Shifting the reduced closing state by one step preserves its least period. -/
theorem sqrt_period_eq_closing (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    P203Specs.sqrtPeriod D = Function.minimalPeriod P203Specs.continuedFractionStep
      (Real.sqrt (D : ℝ) + (⌊Real.sqrt (D : ℝ)⌋ : ℝ)) := by
  have hy := (sqrt_closing_state D hD hns).1
  have hp := Function.minimalPeriod_pos_iff_mem_periodicPts.mp (reduced_minimalPeriod_pos _ hy)
  change Function.minimalPeriod P203Specs.continuedFractionStep
    (P203Specs.continuedFractionStep (Real.sqrt (D : ℝ))) = _
  rw [← (sqrt_closing_state D hD hns).2.2]
  exact Function.minimalPeriod_apply hp

theorem sqrt_periodicity : SqrtPeriodicity := by
  intro D hD hns
  dsimp only
  let s := Real.sqrt (D : ℝ)
  let z := P203Specs.continuedFractionStep s
  have hi : Irrational s := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  have hz : ReducedQuadratic z := by
    have h := (reduced_step _ (sqrt_closing_state D hD hns).1).2.1
    rw [(sqrt_closing_state D hD hns).2.2] at h
    exact h
  have hzi : Irrational z := quadratic_is_irrational z hz.1
  have hpos : 0 < P203Specs.sqrtPeriod D := reduced_minimalPeriod_pos z hz
  have hreturn : P203Specs.continuedFractionStep^[P203Specs.sqrtPeriod D] z = z :=
    Function.iterate_minimalPeriod
  have hd := (canonical_digit_period_iff_return z hzi (P203Specs.sqrtPeriod D)).mpr hreturn
  have hleast : ∀ r : ℕ, 0 < r →
      (∀ n, P203Specs.partialQuotient z (n + r) = P203Specs.partialQuotient z n) →
      P203Specs.sqrtPeriod D ≤ r := by
    intro r hr hdr
    exact Function.IsPeriodicPt.minimalPeriod_le hr
      ((canonical_digit_period_iff_return z hzi r).mp hdr)
  have hshift (n : ℕ) : P203Specs.partialQuotient z n =
      P203Specs.partialQuotient s (n + 1) := by
    simpa only [Function.iterate_one, Nat.add_comm 1] using partialQuotient_iterate s hi 1 n
  refine ⟨hpos, (quotient_iterates s hi 1).2.1, reduced_purely_periodic z hz,
    hd, hleast, ?_, ?_, hreturn, ?_⟩
  · intro n
    simpa only [hshift, Nat.add_right_comm n (P203Specs.sqrtPeriod D) 1] using hd n
  · intro r hr hdr
    apply hleast r hr
    intro n
    rw [hshift, hshift, Nat.add_right_comm n r 1]
    exact hdr n
  · intro r hr hret
    exact Function.IsPeriodicPt.minimalPeriod_le hr hret

/-- A unit denominator characterizes the reduced closing state. -/
theorem sqrt_unit_denominator_iff (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D)
    (j : ℕ) (hj : 1 ≤ j) :
    sqrtQ D j = 1 ↔
      P203Specs.continuedFractionStep^[j] (Real.sqrt (D : ℝ)) =
        Real.sqrt (D : ℝ) + (⌊Real.sqrt (D : ℝ)⌋ : ℝ) := by
  let s := Real.sqrt (D : ℝ)
  let a : ℤ := ⌊s⌋
  let P := sqrtP D j
  let Q := sqrtQ D j
  have hi : Irrational s := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  obtain ⟨hQ, _, hquot⟩ := sqrt_state_valid D hD hns j
  have he : P203Specs.continuedFractionStep^[j] s = ((P : ℝ) + s) / (Q : ℝ) :=
    Option.some.inj ((quotient_iterates s hi j).2.1.symm.trans hquot)
  rw [he]
  constructor
  · intro hunit
    have hr := (sqrt_reduced_states D hD hns j hj).2.1
    have hc := represented_surd_conjugate P Q D hD.le hQ hr.1
    have hlo := hr.2.2.1
    have hhi := hr.2.2.2
    rw [hc] at hlo hhi
    change Q = 1 at hunit
    change -1 < ((P : ℝ) - s) / (Q : ℝ) at hlo
    change ((P : ℝ) - s) / (Q : ℝ) < 0 at hhi
    rw [hunit] at hlo hhi ⊢
    simp only [Int.cast_one, div_one] at hlo hhi ⊢
    have hP : a = P := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [s, a] at hP
    rw [← hP]
    exact add_comm _ _
  · intro hvalue
    have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
    have hc := (div_eq_iff hQr).mp hvalue
    have hcoeff : ((P - a * Q : ℤ) : ℝ) + ((1 - Q : ℤ) : ℝ) * s = 0 := by
      push_cast
      change (P : ℝ) + s = (s + (a : ℝ)) * (Q : ℝ) at hc
      nlinarith [hc]
    have hzero := (irrational_integer_coefficients hi _ _ hcoeff).2
    change Q = 1
    omega

theorem sqrt_period_last : SqrtPeriodLast := by
  intro D hD hns
  let s := Real.sqrt (D : ℝ)
  let y := s + (⌊s⌋ : ℝ)
  have hi : Irrational s := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  have hp : 0 < P203Specs.sqrtPeriod D := (sqrt_periodicity D hD hns).1
  have hreturn : P203Specs.continuedFractionStep^[P203Specs.sqrtPeriod D] y = y := by
    rw [sqrt_period_eq_closing D hD hns]
    exact Function.iterate_minimalPeriod
  have hc : P203Specs.completeQuotient s (P203Specs.sqrtPeriod D) = some y := by
    rw [(quotient_iterates s hi (P203Specs.sqrtPeriod D)).2.1,
      sqrt_orbit_closing D hD hns (P203Specs.sqrtPeriod D) hp, hreturn]
  refine ⟨hc, ?_⟩
  rw [algorithm_digits, hc]
  simpa only [Option.map_some] using congrArg some (sqrt_closing_state D hD hns).2.1

theorem sqrt_return_points : SqrtReturnPoints := by
  intro D hD hns
  refine ⟨(sqrt_state_initial D).2.1, ?_⟩
  intro j hj
  rw [sqrt_unit_denominator_iff D hD hns j hj, sqrt_orbit_closing D hD hns j hj,
    sqrt_period_eq_closing D hD hns]
  exact Function.isPeriodicPt_iff_minimalPeriod_dvd

end P203
