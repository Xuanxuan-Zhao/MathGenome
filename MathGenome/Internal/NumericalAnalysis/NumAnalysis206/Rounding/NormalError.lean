import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.RadixModel
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.NormalError
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Rounding

private theorem radix_pos (P : RadixFormat) : (0 : ℝ) < P.β := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) P.radix_ge_two)

private theorem mantissa_step (P : RadixFormat) :
    (P.β : ℝ) ^ (P.p - 1) * (P.β : ℝ) = (P.β : ℝ) ^ P.p := by
  rw [← pow_succ, Nat.sub_add_cancel P.precision_pos]

private theorem amin_eq (P : RadixFormat) :
    amin P = (P.β : ℝ) ^ (P.p - 1) * (P.β : ℝ) ^ P.emin := by
  have hp : ((P.p - 1 : ℕ) : ℤ) = (P.p : ℤ) - 1 := by
    have := P.precision_pos
    omega
  simp only [amin, Specs.aminValue]
  rw [← zpow_natCast, hp, ← zpow_add₀ (ne_of_gt (radix_pos P))]

private theorem next_binade (P : RadixFormat) (e : ℤ) :
    (P.β : ℝ) ^ (P.p - 1) * (P.β : ℝ) ^ (e + 1) =
      (P.β : ℝ) ^ P.p * (P.β : ℝ) ^ e := by
  rw [zpow_add₀ (ne_of_gt (radix_pos P)), zpow_one]
  rw [← mul_assoc, mul_right_comm _ _ (P.β : ℝ), mantissa_step]

/-- Select the greatest allowed exponent whose binade starts below `x`. -/
private theorem exists_binade (P : RadixFormat) (x : ℝ) (hx : amin P ≤ x) :
    ∃ e : ℤ, P.emin ≤ e ∧ e ≤ P.emax ∧
      (P.β : ℝ) ^ (P.p - 1) * (P.β : ℝ) ^ e ≤ x ∧
      (e < P.emax → x < (P.β : ℝ) ^ P.p * (P.β : ℝ) ^ e) := by
  classical
  let s := (Finset.Icc P.emin P.emax).filter
    (fun e => (P.β : ℝ) ^ (P.p - 1) * (P.β : ℝ) ^ e ≤ x)
  have hne : s.Nonempty := by
    refine ⟨P.emin, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨le_rfl, P.exponent_order⟩
    · rwa [← amin_eq]
  let e := s.max' hne
  have he := Finset.mem_filter.mp (Finset.max'_mem s hne)
  have herange := Finset.mem_Icc.mp he.1
  refine ⟨e, herange.1, herange.2, he.2, ?_⟩
  intro hetop
  by_contra h
  have hs : e + 1 ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [next_binade]
    exact le_of_not_gt h
  have := Finset.le_max' s (e + 1) hs
  change e + 1 ≤ e at this
  omega

/-- Rounding an element of an interval with integral endpoints stays in the interval. -/
private theorem round_in_interval (a b : ℤ) (y : ℝ)
    (ha : (a : ℝ) ≤ y) (hb : y ≤ (b : ℝ)) :
    a ≤ round y ∧ round y ≤ b ∧ |(round y : ℝ) - y| ≤ 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [round_eq, Int.le_floor]
    linarith
  · have h : round y < b + 1 := by
      rw [round_eq, Int.floor_lt]
      push_cast
      linarith
    omega
  · simpa only [abs_sub_comm] using (abs_sub_round y)

/-- An integral mantissa in a binade, including its upper endpoint when allowed,
is represented in the format. -/
private theorem binade_point_mem (P : RadixFormat) (e m : ℤ)
    (helo : P.emin ≤ e) (hehi : e ≤ P.emax)
    (hmlo : P.β ^ (P.p - 1) ≤ m) (hmhi : m ≤ P.β ^ P.p)
    (htop : e = P.emax → m < P.β ^ P.p) :
    (m : ℝ) * (P.β : ℝ) ^ e ∈ F P := by
  rw [mem_F]
  right; left
  by_cases hm : m < P.β ^ P.p
  · exact ⟨m, e, hmlo, hm, helo, hehi, Or.inl rfl⟩
  · have hmeq : m = P.β ^ P.p := le_antisymm hmhi (le_of_not_gt hm)
    have helt : e < P.emax := lt_of_le_of_ne hehi (by
      intro heq
      exact hm (htop heq))
    refine ⟨P.β ^ (P.p - 1), e + 1, le_rfl, ?_, by omega, by omega, Or.inl ?_⟩
    · have hβ : 1 < P.β := by have := P.radix_ge_two; omega
      have hpos : 0 < P.β ^ (P.p - 1) := pow_pos (by omega) _
      have hstep : P.β ^ (P.p - 1) * P.β = P.β ^ P.p := by
        rw [← pow_succ, Nat.sub_add_cancel P.precision_pos]
      nlinarith
    · rw [hmeq]
      push_cast
      exact (next_binade P e).symm

private theorem u_nonneg (P : RadixFormat) : 0 ≤ u P := by
  dsimp [u, Specs.uValue]
  exact div_nonneg (le_of_lt (zpow_pos (radix_pos P) _)) (by norm_num)

private theorem u_mul_mantissa (P : RadixFormat) :
    u P * (P.β : ℝ) ^ (P.p - 1) = 1 / 2 := by
  have hexp : 1 - (P.p : ℤ) + ((P.p - 1 : ℕ) : ℤ) = 0 := by
    have := P.precision_pos
    omega
  have hpow : (P.β : ℝ) ^ (1 - (P.p : ℤ)) * (P.β : ℝ) ^ (P.p - 1) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (ne_of_gt (radix_pos P)), hexp, zpow_zero]
  dsimp [u, Specs.uValue]
  nlinarith

/-- A normal candidate within half a spacing exists throughout the positive safe range. -/
private theorem exists_close_normal (P : RadixFormat) (x : ℝ)
    (hlo : amin P ≤ x) (hhi : x ≤ amax P) :
    ∃ y : ℝ, y ∈ F P ∧ |y - x| ≤ u P * x := by
  obtain ⟨e, helo, hehi, helower, henext⟩ := exists_binade P x hlo
  let s : ℝ := (P.β : ℝ) ^ e
  have hs : 0 < s := zpow_pos (radix_pos P) e
  let cap : ℤ := if e = P.emax then P.β ^ P.p - 1 else P.β ^ P.p
  have hcap : cap ≤ P.β ^ P.p := by
    dsimp [cap]
    split_ifs <;> omega
  have htopcap : e = P.emax → cap < P.β ^ P.p := by
    intro he
    simp only [cap, ite_eq_left he]
    omega
  have hxcap : x ≤ (cap : ℝ) * s := by
    by_cases he : e = P.emax
    · simpa [cap, he, s, amax, Specs.amaxValue] using hhi
    · simp only [cap, ite_eq_right he, Int.cast_pow]
      exact (henext (lt_of_le_of_ne hehi he)).le
  have hratio_lower : ((P.β ^ (P.p - 1) : ℤ) : ℝ) ≤ x / s := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Int.cast_pow] using helower
  have hratio_upper : x / s ≤ (cap : ℝ) :=
    (div_le_iff₀ hs).mpr hxcap
  obtain ⟨hmlo, hmhi, hmerror⟩ :=
    round_in_interval (P.β ^ (P.p - 1)) cap (x / s) hratio_lower hratio_upper
  let m := round (x / s)
  have hmem : (m : ℝ) * s ∈ F P := by
    apply binade_point_mem P e m helo hehi hmlo (hmhi.trans hcap)
    intro he
    exact hmhi.trans_lt (htopcap he)
  refine ⟨(m : ℝ) * s, hmem, ?_⟩
  calc
    |(m : ℝ) * s - x| = |((m : ℝ) - x / s) * s| := by
      congr 1
      field_simp
    _ = |(m : ℝ) - x / s| * s := by rw [abs_mul, abs_of_pos hs]
    _ ≤ (1 / 2) * s := mul_le_mul_of_nonneg_right hmerror hs.le
    _ = u P * ((P.β : ℝ) ^ (P.p - 1) * s) := by
      rw [← mul_assoc, u_mul_mantissa]
    _ ≤ u P * x := mul_le_mul_of_nonneg_left helower (u_nonneg P)

private theorem neg_mem_F (P : RadixFormat) (y : ℝ) (hy : y ∈ F P) : -y ∈ F P := by
  classical
  have hsign (z : ℝ) : z ∈ F P ↔
      z = 0 ∨ z ∈ P.positiveValues ∨ -z ∈ P.positiveValues := by
    simp [F, Specs.FValue, RadixFormat.numbers]
  rw [hsign] at hy ⊢
  simpa only [neg_eq_zero, neg_neg] using hy.imp_right Or.symm

/-- The absolute form of the normal safe-domain rounding bound. -/
theorem normal_absolute_error (P : RadixFormat) (x : ℝ)
    (hx : x ∈ normalSafeDomain P) : |fl P x - x| ≤ u P * |x| := by
  change x = 0 ∨ amin P ≤ |x| ∧ |x| ≤ amax P at hx
  rcases hx with rfl | ⟨hlo, hhi⟩
  · simp
  · obtain ⟨y, hy, herr⟩ := exists_close_normal P |x| hlo hhi
    by_cases hsign : 0 ≤ x
    · rw [abs_of_nonneg hsign] at herr ⊢
      exact (fl_minimizes P x y hy).trans herr
    · have hneg : x ≤ 0 := le_of_not_ge hsign
      have heq : |-y - x| = |y - (|x|)| := by
        rw [abs_of_nonpos hneg]
        have : -y - x = -(y - -x) := by ring
        rw [this, abs_neg]
      exact (fl_minimizes P x (-y) (neg_mem_F P y hy)).trans (heq.trans_le herr)

/-- Nearest rounding has relative error at most `u` on the normal safe domain,
including zero, both signs, and the largest finite endpoint. -/
theorem normal_relative_error (P : RadixFormat) (x : ℝ)
    (hx : x ∈ normalSafeDomain P) :
    ∃ δ : ℝ, |δ| ≤ u P ∧ fl P x = x * (1 + δ) := by
  by_cases hxzero : x = 0
  · subst x
    exact ⟨0, by simpa using u_nonneg P, by simp⟩
  · refine ⟨(fl P x - x) / x, ?_, ?_⟩
    · rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr hxzero)).mpr (normal_absolute_error P x hx)
    · field_simp
      ring

end NumAnalysis206.Rounding
