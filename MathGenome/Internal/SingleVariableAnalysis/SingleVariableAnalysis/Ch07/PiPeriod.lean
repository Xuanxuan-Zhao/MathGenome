import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigProperties
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.PiPeriod

/-!
The manuscript's series functions have already been identified with Real.sin
and Real.cos by `sinCosSeries_eq_real`. We transport Mathlib's analytic π and
trigonometric results through that proved identity. In Mathlib π itself is
twice a positive cosine zero (Basic.lean, `Real.pi`); its positivity and
cosine sign theorem show that the infimum used here is its first positive
zero. No geometric definition or unproved zero-existence premise is used.
-/
noncomputable section
namespace SingleVariableAnalysis

def firstPositiveCosineZero : ℝ := sInf {x : ℝ | 0 < x ∧ realSeriesCos x = 0}
def analyticPi : ℝ := 2 * firstPositiveCosineZero

namespace PiPeriod
private theorem sine_eq : realSeriesSin = Real.sin :=
  funext fun x => (sinCosSeries_eq_real x).1
private theorem cosine_eq : realSeriesCos = Real.cos :=
  funext fun x => (sinCosSeries_eq_real x).2

private theorem shift_strictMono {f : ℝ → ℝ} {a b p : ℝ}
    (h : StrictMonoOn f (Set.Icc a b)) (hp : Function.Periodic f p) (k : ℤ) :
    StrictMonoOn f (Set.Icc (a + k * p) (b + k * p)) := by
  intro x hx y hy hxy
  have hx' : x - k * p ∈ Set.Icc a b := by constructor <;> linarith [hx.1, hx.2]
  have hy' : y - k * p ∈ Set.Icc a b := by constructor <;> linarith [hy.1, hy.2]
  have H := h hx' hy' (by linarith : x - k * p < y - k * p)
  simpa only [hp.sub_int_mul_eq] using H

private theorem shift_strictAnti {f : ℝ → ℝ} {a b p : ℝ}
    (h : StrictAntiOn f (Set.Icc a b)) (hp : Function.Periodic f p) (k : ℤ) :
    StrictAntiOn f (Set.Icc (a + k * p) (b + k * p)) := by
  intro x hx y hy hxy
  have hx' : x - k * p ∈ Set.Icc a b := by constructor <;> linarith [hx.1, hx.2]
  have hy' : y - k * p ∈ Set.Icc a b := by constructor <;> linarith [hy.1, hy.2]
  have H := h hx' hy' (by linarith : x - k * p < y - k * p)
  simpa only [hp.sub_int_mul_eq] using H

theorem firstPositiveCosineZero_eq_pi_div_two :
    firstPositiveCosineZero = Real.pi / 2 := by
  unfold firstPositiveCosineZero
  apply IsLeast.csInf_eq
  refine ⟨⟨Real.pi_div_two_pos, ?_⟩, ?_⟩
  · rw [cosine_eq, Real.cos_pi_div_two]
  · intro x hx
    by_contra h
    have hp := Real.cos_pos_of_mem_Ioo (x := x)
      ⟨by linarith [Real.pi_pos, hx.1], lt_of_not_ge h⟩
    rw [← cosine_eq, hx.2] at hp
    exact (lt_irrefl 0) hp

theorem firstPositiveCosineZero_isLeast :
    IsLeast {x : ℝ | 0 < x ∧ realSeriesCos x = 0} firstPositiveCosineZero := by
  rw [firstPositiveCosineZero_eq_pi_div_two]
  refine ⟨⟨Real.pi_div_two_pos, ?_⟩, ?_⟩
  · rw [cosine_eq, Real.cos_pi_div_two]
  · intro x hx
    by_contra h
    have hp := Real.cos_pos_of_mem_Ioo (x := x)
      ⟨by linarith [Real.pi_pos, hx.1], lt_of_not_ge h⟩
    rw [← cosine_eq, hx.2] at hp
    exact (lt_irrefl 0) hp

theorem analyticPi_eq_pi :
    analyticPi = Real.pi := by
  rw [analyticPi, firstPositiveCosineZero_eq_pi_div_two]
  ring

theorem piPeriod_positive :
    0 < firstPositiveCosineZero ∧ 0 < analyticPi := by
  rw [firstPositiveCosineZero_eq_pi_div_two, analyticPi_eq_pi]
  exact ⟨Real.pi_div_two_pos, Real.pi_pos⟩

theorem piPeriod_cosine_positive_before :
    ∀ x : ℝ, 0 ≤ x → x < firstPositiveCosineZero → 0 < realSeriesCos x := by
  intro x hx hxc
  rw [cosine_eq]
  rw [firstPositiveCosineZero_eq_pi_div_two] at hxc
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxc⟩

theorem piPeriod_at_firstZero :
    realSeriesSin firstPositiveCosineZero = 1 ∧ realSeriesCos firstPositiveCosineZero = 0 := by
  rw [sine_eq, cosine_eq, firstPositiveCosineZero_eq_pi_div_two]
  exact ⟨Real.sin_pi_div_two, Real.cos_pi_div_two⟩

theorem piPeriod_firstQuadrant_monotonicity :
    StrictMonoOn realSeriesSin (Set.Icc 0 firstPositiveCosineZero) ∧
    StrictAntiOn realSeriesCos (Set.Icc 0 firstPositiveCosineZero) := by
  rw [sine_eq, cosine_eq, firstPositiveCosineZero_eq_pi_div_two]
  constructor
  · exact Real.strictMonoOn_sin.mono (by intro x hx; exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  · exact Real.strictAntiOn_cos.mono (by intro x hx; exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)

theorem piPeriod_firstQuadrant_ranges :
    realSeriesSin '' Set.Icc 0 firstPositiveCosineZero = Set.Icc 0 1 ∧
    realSeriesCos '' Set.Icc 0 firstPositiveCosineZero = Set.Icc 0 1 := by
  obtain ⟨hs, hc⟩ := piPeriod_firstQuadrant_monotonicity
  have hs' : ContinuousOn realSeriesSin (Set.Icc 0 firstPositiveCosineZero) := by
    rw [sine_eq]; exact Real.continuous_sin.continuousOn
  have hc' : ContinuousOn realSeriesCos (Set.Icc 0 firstPositiveCosineZero) := by
    rw [cosine_eq]; exact Real.continuous_cos.continuousOn
  constructor
  · simpa only [sine_eq, firstPositiveCosineZero_eq_pi_div_two, Real.sin_zero,
      Real.sin_pi_div_two] using hs'.image_Icc_of_monotoneOn piPeriod_positive.1.le hs.monotoneOn
  · simpa only [cosine_eq, firstPositiveCosineZero_eq_pi_div_two, Real.cos_zero,
      Real.cos_pi_div_two] using hc'.image_Icc_of_antitoneOn piPeriod_positive.1.le hc.antitoneOn

theorem piPeriod_quarter_relations :
    ∀ x : ℝ,
    realSeriesSin (x + firstPositiveCosineZero) = realSeriesCos x ∧
    realSeriesCos (x + firstPositiveCosineZero) = -realSeriesSin x ∧
    realSeriesSin (x + 2 * firstPositiveCosineZero) = -realSeriesSin x ∧
    realSeriesCos (x + 2 * firstPositiveCosineZero) = -realSeriesCos x := by
  intro x
  rw [sine_eq, cosine_eq, firstPositiveCosineZero_eq_pi_div_two]
  have h : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [h]
  exact ⟨Real.sin_add_pi_div_two x, Real.cos_add_pi_div_two x,
    Real.sin_add_pi x, Real.cos_add_pi x⟩

theorem piPeriod_periodic :
    Function.Periodic realSeriesSin (2 * analyticPi) ∧
    Function.Periodic realSeriesCos (2 * analyticPi) := by
  rw [sine_eq, cosine_eq, analyticPi_eq_pi]
  exact ⟨Real.sin_periodic, Real.cos_periodic⟩

theorem piPeriod_integer_periods :
    ∀ (k : ℤ) (x : ℝ),
    realSeriesSin (x + k * (2 * analyticPi)) = realSeriesSin x ∧
    realSeriesCos (x + k * (2 * analyticPi)) = realSeriesCos x := by
  intro k x
  exact ⟨piPeriod_periodic.1.int_mul k x, piPeriod_periodic.2.int_mul k x⟩

theorem piPeriod_quadrant_signs :
    ∀ (k : ℤ) (x : ℝ),
    (x ∈ Set.Ioo 0 firstPositiveCosineZero →
      0 < realSeriesSin (x + k * (2 * analyticPi)) ∧
      0 < realSeriesCos (x + k * (2 * analyticPi))) ∧
    (x ∈ Set.Ioo firstPositiveCosineZero (2 * firstPositiveCosineZero) →
      0 < realSeriesSin (x + k * (2 * analyticPi)) ∧
      realSeriesCos (x + k * (2 * analyticPi)) < 0) ∧
    (x ∈ Set.Ioo (2 * firstPositiveCosineZero) (3 * firstPositiveCosineZero) →
      realSeriesSin (x + k * (2 * analyticPi)) < 0 ∧
      realSeriesCos (x + k * (2 * analyticPi)) < 0) ∧
    (x ∈ Set.Ioo (3 * firstPositiveCosineZero) (4 * firstPositiveCosineZero) →
      realSeriesSin (x + k * (2 * analyticPi)) < 0 ∧
      0 < realSeriesCos (x + k * (2 * analyticPi))) := by
  intro k x
  rw [(piPeriod_integer_periods k x).1, (piPeriod_integer_periods k x).2]
  rw [sine_eq, cosine_eq, firstPositiveCosineZero_eq_pi_div_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hx
    exact ⟨Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos]),
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩⟩
  · intro hx
    exact ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, Real.pi_pos]) (by linarith [hx.2]),
      Real.cos_neg_of_pi_div_two_lt_of_lt hx.1 (by linarith [hx.2, Real.pi_pos])⟩
  · intro hx
    constructor
    · have h := Real.sin_pos_of_pos_of_lt_pi (x := x - Real.pi)
        (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
      rw [Real.sin_sub_pi] at h
      linarith
    · exact Real.cos_neg_of_pi_div_two_lt_of_lt
        (by linarith [hx.1, Real.pi_pos]) (by linarith [hx.2])
  · intro hx
    constructor
    · have h := Real.sin_pos_of_pos_of_lt_pi (x := x - Real.pi)
        (by linarith [hx.1, Real.pi_pos]) (by linarith [hx.2])
      rw [Real.sin_sub_pi] at h
      linarith
    · have h := Real.cos_pos_of_mem_Ioo (x := x - 2 * Real.pi)
        ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
      simpa only [Real.cos_sub_two_pi] using h

theorem piPeriod_quadrant_monotonicity :
    ∀ k : ℤ,
    StrictMonoOn realSeriesSin
      (Set.Icc (-firstPositiveCosineZero + k * (2 * analyticPi))
        (firstPositiveCosineZero + k * (2 * analyticPi))) ∧
    StrictAntiOn realSeriesSin
      (Set.Icc (firstPositiveCosineZero + k * (2 * analyticPi))
        (3 * firstPositiveCosineZero + k * (2 * analyticPi))) ∧
    StrictAntiOn realSeriesCos
      (Set.Icc (k * (2 * analyticPi)) (2 * firstPositiveCosineZero + k * (2 * analyticPi))) ∧
    StrictMonoOn realSeriesCos
      (Set.Icc (2 * firstPositiveCosineZero + k * (2 * analyticPi))
        (4 * firstPositiveCosineZero + k * (2 * analyticPi))) := by
  intro k
  rw [sine_eq, cosine_eq, firstPositiveCosineZero_eq_pi_div_two, analyticPi_eq_pi]
  have hs : StrictAntiOn Real.sin (Set.Icc (Real.pi / 2) (3 * (Real.pi / 2))) := by
    intro x hx y hy hxy
    have h := Real.strictMonoOn_sin
      (show x - Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [hx.1, hx.2])
      (show y - Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [hy.1, hy.2]) (by linarith : x - Real.pi < y - Real.pi)
    rw [Real.sin_sub_pi, Real.sin_sub_pi] at h
    linarith
  have hc : StrictMonoOn Real.cos (Set.Icc Real.pi (2 * Real.pi)) := by
    intro x hx y hy hxy
    have h := Real.strictAntiOn_cos
      (show 2 * Real.pi - y ∈ Set.Icc 0 Real.pi by constructor <;> linarith [hy.1, hy.2])
      (show 2 * Real.pi - x ∈ Set.Icc 0 Real.pi by constructor <;> linarith [hx.1, hx.2])
      (by linarith : 2 * Real.pi - y < 2 * Real.pi - x)
    simpa only [Real.cos_two_pi_sub] using h
  refine ⟨shift_strictMono Real.strictMonoOn_sin Real.sin_periodic k,
    shift_strictAnti hs Real.sin_periodic k, ?_, ?_⟩
  · simpa only [zero_add, show 2 * (Real.pi / 2) = Real.pi by ring] using
      shift_strictAnti Real.strictAntiOn_cos Real.cos_periodic k
  · simpa only [show 2 * (Real.pi / 2) = Real.pi by ring,
      show 4 * (Real.pi / 2) = 2 * Real.pi by ring] using
      shift_strictMono hc Real.cos_periodic k

theorem piPeriod_sine_zeros :
    ∀ x : ℝ, realSeriesSin x = 0 ↔ ∃ k : ℤ, x = k * analyticPi := by
  intro x
  rw [sine_eq, analyticPi_eq_pi, Real.sin_eq_zero_iff]
  exact exists_congr (fun k => eq_comm)

theorem piPeriod_cosine_zeros :
    ∀ x : ℝ, realSeriesCos x = 0 ↔
    ∃ k : ℤ, x = firstPositiveCosineZero + k * analyticPi := by
  intro x
  rw [cosine_eq, firstPositiveCosineZero_eq_pi_div_two, analyticPi_eq_pi]
  have h : Real.cos x = 0 ↔ Real.sin (x - Real.pi / 2) = 0 := by
    rw [Real.sin_sub_pi_div_two, neg_eq_zero]
  rw [h, Real.sin_eq_zero_iff]
  apply exists_congr
  intro k
  constructor <;> intro h <;> linarith

theorem piPeriod_common_periods :
    ∀ p : ℝ,
    (Function.Periodic realSeriesSin p ∧ Function.Periodic realSeriesCos p) ↔
      ∃ k : ℤ, p = k * (2 * analyticPi) := by
  intro p
  rw [sine_eq, cosine_eq, analyticPi_eq_pi]
  constructor
  · intro h
    have hc : Real.cos p = 1 := by simpa only [zero_add, Real.cos_zero] using h.2 0
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff p).mp hc
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Real.sin_periodic.int_mul k, Real.cos_periodic.int_mul k⟩

theorem piPeriod_le_positive_common_period :
    ∀ p : ℝ, 0 < p →
    Function.Periodic realSeriesSin p → Function.Periodic realSeriesCos p →
      2 * analyticPi ≤ p := by
  intro p hp hs hc
  rw [cosine_eq] at hc
  rw [analyticPi_eq_pi]
  by_contra h
  have hcp : Real.cos p = 1 := by simpa only [zero_add, Real.cos_zero] using hc 0
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt
    (by linarith [Real.pi_pos] : -(2 * Real.pi) < p) (lt_of_not_ge h)).mp hcp
  linarith

end PiPeriod
end SingleVariableAnalysis
