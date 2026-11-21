import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MoserOneDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace P102.Sobolev.Moser

lemma measurable_slope (w : ℝ → ℝ) : Measurable (slope w) := measurable_deriv w

lemma exponent_pos {d : ℕ} (hd : 2 ≤ d) : 0 < exponent d := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold exponent
  exact div_pos (by linarith) (by linarith)

lemma exponent_lt_one {d : ℕ} (hd : 2 ≤ d) : exponent d < 1 := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold exponent
  apply (div_lt_one (by positivity : (0 : ℝ) < d)).2
  linarith

lemma inverse_exponent {d : ℕ} :
    1 / exponent d = (d : ℝ) / ((d : ℝ) - 1) := by
  unfold exponent
  simp

/-- Derivative energy on an interval. For admissible functions, integrability is
established below from the original bound before this quantity is used. -/
def intervalEnergy (d : ℕ) (w : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in Ioc a b, |slope w t| ^ d

lemma Admissible.energy_integrable {d : ℕ} {w : ℝ → ℝ} (hw : Admissible d w) :
    IntegrableOn (fun t ↦ |slope w t| ^ d) (Ioi (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using
      ((measurable_slope w).norm.pow_const d).aestronglyMeasurable
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun t ↦ pow_nonneg (abs_nonneg (slope w t)) d)).2
  exact hw.energy_le_one.trans_lt (by simp : (1 : ℝ≥0∞) < ⊤)

lemma Admissible.intervalEnergy_nonneg {d : ℕ} {w : ℝ → ℝ}
    (_hw : Admissible d w) (a b : ℝ) : 0 ≤ intervalEnergy d w a b := by
  exact integral_nonneg fun t ↦ pow_nonneg (abs_nonneg _) _

lemma Admissible.ac_interval {d : ℕ} {w : ℝ → ℝ} (hw : Admissible d w)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : AbsolutelyContinuousOnInterval w a b := by
  apply (hw.locallyAC b (ha.trans hab)).mono
  simpa [uIcc_of_le hab, uIcc_of_le (ha.trans hab)] using
    (Icc_subset_Icc ha le_rfl : Icc a b ⊆ Icc 0 b)

lemma Admissible.intervalEnergy_integrable {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t ↦ |slope w t| ^ d) (Ioc a b) :=
  hw.energy_integrable.mono_set fun _ ht ↦ lt_of_le_of_lt ha ht.1

lemma Admissible.total_energy_le_one {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) : (∫ t in Ioi (0 : ℝ), |slope w t| ^ d) ≤ 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun t ↦ pow_nonneg (abs_nonneg (slope w t)) d)
    hw.energy_integrable.aestronglyMeasurable]
  simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hw.energy_le_one

lemma Admissible.intervalEnergy_le_one {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) {a b : ℝ} (ha : 0 ≤ a) :
    intervalEnergy d w a b ≤ 1 := by
  apply le_trans ?_ hw.total_energy_le_one
  exact integral_mono_measure
    (Measure.restrict_mono (fun _ ht ↦ lt_of_le_of_lt ha ht.1) le_rfl)
    (Filter.Eventually.of_forall fun t ↦ pow_nonneg (abs_nonneg (slope w t)) d)
    hw.energy_integrable

/-- Hölder's inequality on any compact subinterval of the half-line. -/
lemma Admissible.increment_le_energy {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |w b - w a| ≤ (intervalEnergy d w a b) ^ (1 / (d : ℝ)) *
      (b - a) ^ exponent d := by
  have hdreal : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hdpos : (0 : ℝ) < d := lt_trans zero_lt_one hdreal
  have hpq := Real.HolderConjugate.conjExponent hdreal
  let g : ℝ → ℝ := slope w
  have hmem : MemLp g (ENNReal.ofReal (d : ℝ))
      (volume.restrict (Ioc a b)) := by
    apply (integrable_norm_rpow_iff (f := g) (p := ENNReal.ofReal (d : ℝ))
      (show AEStronglyMeasurable g _ from (measurable_slope w).aestronglyMeasurable)
      (by simpa using ne_of_gt hdpos) (by simp)).1
    simpa only [IntegrableOn, ENNReal.toReal_ofReal hdpos.le, Real.norm_eq_abs,
      Real.rpow_natCast, g]
      using hw.intervalEnergy_integrable ha (b := b)
  have hholder := integral_mul_norm_le_Lp_mul_Lq hpq hmem
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal (Real.conjExponent (d : ℝ))) (volume.restrict (Ioc a b)))
  have hconj : 1 / Real.conjExponent (d : ℝ) = exponent d := by
    simp [Real.conjExponent, exponent]
  have hmeasure : (volume.restrict (Ioc a b)).real univ = b - a := by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hholder' : (∫ t in Ioc a b, |slope w t|) ≤
      (intervalEnergy d w a b) ^ (1 / (d : ℝ)) * (b - a) ^ exponent d := by
    simpa [Real.norm_eq_abs, intervalEnergy, hconj, hmeasure, Real.rpow_natCast, g] using hholder
  apply le_trans ?_ hholder'
  have hftc := (hw.ac_interval ha hab).integral_deriv_eq_sub
  change |w b - w a| ≤ ∫ t in Ioc a b, |deriv w t|
  rw [← hftc, ← Real.norm_eq_abs]
  simpa [intervalIntegral.integral_of_le hab, Real.norm_eq_abs, slope] using
    (intervalIntegral.norm_integral_le_integral_norm (f := slope w) (μ := volume) hab)

lemma Admissible.increment_pow_le_energy {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |w b - w a| ^ d ≤ intervalEnergy d w a b * (b - a) ^ (d - 1) := by
  have hd0 : d ≠ 0 := by omega
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hb : exponent d * d = ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    unfold exponent
    field_simp
  have hpow := pow_le_pow_left₀ (abs_nonneg (w b - w a))
    (hw.increment_le_energy hd ha hab) d
  rw [mul_pow, one_div,
    Real.rpow_inv_natCast_pow (hw.intervalEnergy_nonneg a b) hd0,
    ← Real.rpow_mul_natCast (sub_nonneg.mpr hab), hb, Real.rpow_natCast] at hpow
  exact hpow

lemma Admissible.pointwise_le {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    w t ≤ t ^ exponent d := by
  have h := hw.increment_le_energy hd le_rfl ht
  rw [hw.zero, sub_zero, abs_of_nonneg (hw.nonneg t ht), sub_zero] at h
  have hroot : (intervalEnergy d w 0 t) ^ (1 / (d : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow (hw.intervalEnergy_nonneg 0 t)
      (hw.intervalEnergy_le_one le_rfl) (by positivity : 0 ≤ 1 / (d : ℝ))
  exact h.trans (by
    simpa using (mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg ht (exponent d))))

lemma Admissible.power_le_time {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    (w t) ^ (1 / exponent d) ≤ t := by
  have h := Real.rpow_le_rpow (hw.nonneg t ht) (hw.pointwise_le hd ht)
    (le_of_lt (one_div_pos.mpr (exponent_pos hd)))
  rw [one_div, Real.rpow_rpow_inv ht (ne_of_gt (exponent_pos hd))] at h
  simpa only [one_div] using h

lemma Admissible.intervalEnergy_add {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    intervalEnergy d w a b + intervalEnergy d w b c = intervalEnergy d w a c := by
  have habi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (hw.intervalEnergy_integrable ha)
  have hbci := (intervalIntegrable_iff_integrableOn_Ioc_of_le hbc).2
    (hw.intervalEnergy_integrable (ha.trans hab))
  simpa only [intervalEnergy, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le (hab.trans hbc)]
    using intervalIntegral.integral_add_adjacent_intervals habi hbci

lemma Admissible.remaining_energy {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    intervalEnergy d w a b ≤ 1 - intervalEnergy d w 0 a := by
  have hadd := hw.intervalEnergy_add le_rfl ha hab
  have htotal := hw.intervalEnergy_le_one (a := 0) (b := b) le_rfl
  linarith

lemma Admissible.continuousOn_pos {d : ℕ} {w : ℝ → ℝ} (hw : Admissible d w) :
    ContinuousOn w (Ioi (0 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hR : (0 : ℝ) ≤ t + 1 := by linarith [ht]
  apply ((hw.locallyAC (t + 1) hR).continuousOn.continuousAt ?_).continuousWithinAt
  rw [uIcc_of_le hR]
  exact Icc_mem_nhds ht (by linarith)

lemma exponent_mul_dim {d : ℕ} (hd : 2 ≤ d) :
    exponent d * d = ((d - 1 : ℕ) : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  unfold exponent
  field_simp

lemma Admissible.level_lower_bound {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {K t : ℝ} (ht : 0 ≤ t) (hKt : K ≤ t)
    (hlevel : t - (w t) ^ (1 / exponent d) ≤ K) :
    (t - K) ^ exponent d ≤ w t := by
  have h := Real.rpow_le_rpow (sub_nonneg.mpr hKt)
    (by linarith : t - K ≤ (w t) ^ (1 / exponent d)) (exponent_pos hd).le
  rw [← Real.rpow_mul (hw.nonneg t ht),
    one_div_mul_cancel (ne_of_gt (exponent_pos hd)), Real.rpow_one] at h
  exact h

/-- A point of small deficit has already expended almost all its energy. -/
lemma Admissible.energy_after_level {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {K t s : ℝ} (hK : 0 < K) (ht : K < t)
    (hts : t ≤ s) (hlevel : t - (w t) ^ (1 / exponent d) ≤ K) :
    intervalEnergy d w t s ≤ ((d : ℝ) - 1) * K / t := by
  have ht0 : 0 < t := hK.trans ht
  have hlow := hw.level_lower_bound hd ht0.le ht.le hlevel
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (sub_nonneg.mpr ht.le) (exponent d)) hlow d
  rw [← Real.rpow_mul_natCast (sub_nonneg.mpr ht.le), exponent_mul_dim hd,
    Real.rpow_natCast] at hpow
  have hinc := hw.increment_pow_le_energy hd le_rfl ht0.le
  rw [hw.zero, sub_zero, abs_of_nonneg (hw.nonneg t ht0.le), sub_zero] at hinc
  have hepre : (1 - K / t) ^ (d - 1) ≤ intervalEnergy d w 0 t := by
    have hh := (div_le_iff₀ (pow_pos ht0 (d - 1))).2 (hpow.trans hinc)
    convert hh using 1
    rw [← div_pow]
    congr 1
    field_simp
  have hbase : 0 ≤ 1 - K / t := by
    rw [sub_nonneg, div_le_one ht0]
    exact ht.le
  have hbern := one_add_mul_sub_le_pow (by linarith : -1 ≤ 1 - K / t) (d - 1)
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at hbern
  have hrem := hw.remaining_energy ht0.le hts
  have hb : 1 - ((d : ℝ) - 1) * K / t ≤ intervalEnergy d w 0 t := by
    calc
      _ = 1 + ((d : ℝ) - 1) * (1 - K / t - 1) := by ring
      _ ≤ _ := hbern.trans hepre
  linarith

lemma rpow_sub_lower {x y b : ℝ} (hx : 0 ≤ x) (hxy : x < y)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b * (y - x) * y ^ (b - 1) ≤ y ^ b - x ^ b := by
  have hy : 0 < y := hx.trans_lt hxy
  have h := (Real.concaveOn_rpow hb0 hb1).le_slope_of_hasDerivAt hx hy.le hxy
    (Real.hasDerivAt_rpow_const (Or.inl hy.ne'))
  rw [slope_def_field] at h
  have hh := (le_div_iff₀ (sub_pos.mpr hxy)).1 h
  nlinarith

def gapConstant (d : ℕ) : ℝ := ((d : ℝ) - 1) / (exponent d / 2) ^ d

lemma gapConstant_pos {d : ℕ} (hd : 2 ≤ d) : 0 < gapConstant d := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by linarith) (pow_pos (div_pos (exponent_pos hd) (by norm_num)) _)

lemma Admissible.level_pair_lower {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {K t l : ℝ} (hK : 0 < K)
    (ht : 0 ≤ t) (hl : 2 * K ≤ l)
    (hlevel : t + l - (w (t + l)) ^ (1 / exponent d) ≤ K) :
    exponent d / 2 * l * (t + l) ^ (-(1 / (d : ℝ))) ≤ w (t + l) - w t := by
  have hl0 : 0 < l := by linarith
  have htl0 : 0 < t + l := by linarith
  have hult : t < t + l - K := by linarith
  have hu0 : 0 < t + l - K := lt_of_le_of_lt ht hult
  have hb0 := (exponent_pos hd).le
  have hb1 := (exponent_lt_one hd).le
  have hconc := rpow_sub_lower ht hult hb0 hb1
  have hbminus : exponent d - 1 = -(1 / (d : ℝ)) := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    unfold exponent
    field_simp
    ring
  rw [hbminus] at hconc
  have hder : (t + l) ^ (-(1 / (d : ℝ))) ≤
      (t + l - K) ^ (-(1 / (d : ℝ))) := by
    apply Real.rpow_le_rpow_of_nonpos hu0
    · linarith
    · have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
      linarith
  have hlow := hw.level_lower_bound hd htl0.le (by linarith : K ≤ t + l) hlevel
  calc
    exponent d / 2 * l * (t + l) ^ (-(1 / (d : ℝ))) =
        (exponent d * (l / 2)) * (t + l) ^ (-(1 / (d : ℝ))) := by ring
    _ ≤ (exponent d * (t + l - K - t)) *
        (t + l - K) ^ (-(1 / (d : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hb0
      · exact hder
      · positivity
      · exact mul_nonneg hb0 (by linarith)
    _ ≤ (t + l - K) ^ exponent d - t ^ exponent d := hconc
    _ ≤ w (t + l) - w t := sub_le_sub hlow (hw.pointwise_le hd ht)

lemma Admissible.level_pair_ratio {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {K t l : ℝ} (hK : 0 < K)
    (ht : K < t) (hl : 2 * K ≤ l)
    (hlevel : t - (w t) ^ (1 / exponent d) ≤ K)
    (hlevel' : t + l - (w (t + l)) ^ (1 / exponent d) ≤ K) :
    l / (t + l) ≤ gapConstant d * K / t := by
  have ht0 := hK.trans ht
  have hl0 : 0 < l := by linarith
  have htl0 : 0 < t + l := by linarith
  have ha0 : 0 < exponent d / 2 := div_pos (exponent_pos hd) (by norm_num)
  have hlow := hw.level_pair_lower hd hK ht0.le hl hlevel'
  have hlpow := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg ha0.le hl0.le) (Real.rpow_nonneg htl0.le _))
    (hlow.trans (le_abs_self _)) d
  have hexp : -(1 / (d : ℝ)) * d = -1 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast htl0.le, hexp,
    Real.rpow_neg_one] at hlpow
  have hu := hw.increment_pow_le_energy hd ht0.le (by linarith : t ≤ t + l)
  simp only [add_sub_cancel_left] at hu
  have he := hw.energy_after_level hd hK ht (by linarith : t ≤ t + l) hlevel
  have hboth := hlpow.trans (hu.trans (mul_le_mul_of_nonneg_right he
    (pow_nonneg hl0.le (d - 1))))
  have hpower : l ^ d = l ^ (d - 1) * l := by
    rw [← pow_succ]
    congr 1
    omega
  have heq : (exponent d / 2) ^ d * l ^ d * (t + l)⁻¹ =
      l ^ (d - 1) * ((exponent d / 2) ^ d * (l / (t + l))) := by
    rw [hpower]
    ring
  rw [heq, mul_comm (((d : ℝ) - 1) * K / t) (l ^ (d - 1))] at hboth
  have hc := le_of_mul_le_mul_left hboth (pow_pos hl0 (d - 1))
  calc
    l / (t + l) ≤ (((d : ℝ) - 1) * K / t) / (exponent d / 2) ^ d := by
      apply (le_div_iff₀ (pow_pos ha0 d)).2
      simpa [mul_comm] using hc
    _ = gapConstant d * K / t := by unfold gapConstant; ring

lemma gap_bound_of_ratio {K t l c : ℝ} (hK : 0 < K) (hc : 0 ≤ c)
    (hl : 0 ≤ l) (ht : 2 * (c + 1) * K ≤ t)
    (hratio : l / (t + l) ≤ c * K / t) : l ≤ 2 * c * K := by
  have ht0 : 0 < t := by nlinarith
  have htl0 : 0 < t + l := by linarith
  have hh : l * t ≤ c * K * (t + l) := by
    exact (div_le_div_iff₀ htl0 ht0).1 hratio
  have hhalf : c * K ≤ t / 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hhalf hl
  nlinarith

lemma volume_le_of_ordered_pair_bound {A : Set ℝ} {T L : ℝ}
    (hA : A ⊆ Ioi 0) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hpair : ∀ t ∈ A, ∀ s ∈ A, T ≤ t → t ≤ s → s - t ≤ L) :
    volume A ≤ ENNReal.ofReal (T + L) := by
  have htail : volume (A ∩ Ici T) ≤ ENNReal.ofReal L := by
    apply (Real.volume_le_diam _).trans
    apply Metric.ediam_le
    intro x hx y hy
    have habs : |x - y| ≤ L := by
      rcases le_total x y with hxy | hyx
      · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        have hh := hpair x hx.1 y hy.1 hx.2 hxy
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        exact hpair y hy.1 x hx.1 hy.2 hyx
    simpa only [edist_dist, Real.dist_eq] using ENNReal.ofReal_le_ofReal habs
  calc
    volume A ≤ volume (Ioc 0 T ∪ (A ∩ Ici T)) := by
      apply measure_mono
      intro x hx
      rcases le_total x T with hxt | htx
      · exact Or.inl ⟨hA hx, hxt⟩
      · exact Or.inr ⟨hx, htx⟩
    _ ≤ volume (Ioc 0 T) + volume (A ∩ Ici T) := measure_union_le _ _
    _ ≤ ENNReal.ofReal T + ENNReal.ofReal L := by
      simpa using add_le_add (le_refl (volume (Ioc 0 T))) htail
    _ = ENNReal.ofReal (T + L) := (ENNReal.ofReal_add hT hL).symm

/-- The decisive distribution bound in the manuscript, with an explicit
dimension-dependent constant. It does not require monotonicity of `w`. -/
lemma Admissible.sublevel_volume {d : ℕ} {w : ℝ → ℝ}
    (hw : Admissible d w) (hd : 2 ≤ d) {K : ℝ} (hK : 0 < K) :
    volume {t : ℝ | 0 < t ∧ t - (w t) ^ (1 / exponent d) ≤ K} ≤
      ENNReal.ofReal ((4 * (gapConstant d + 1)) * K) := by
  let T := 2 * (gapConstant d + 1) * K
  have hc := (gapConstant_pos hd).le
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTK : K < T := by dsimp [T]; nlinarith
  have hpair : ∀ t ∈ {t : ℝ | 0 < t ∧ t - (w t) ^ (1 / exponent d) ≤ K},
      ∀ s ∈ {t : ℝ | 0 < t ∧ t - (w t) ^ (1 / exponent d) ≤ K},
      T ≤ t → t ≤ s → s - t ≤ T := by
    intro t ht s hs hTt hts
    by_cases hl : 2 * K ≤ s - t
    · have hratio := hw.level_pair_ratio hd hK (hTK.trans_le hTt) hl ht.2
        (by simpa only [add_sub_cancel] using hs.2)
      have hgap := gap_bound_of_ratio hK hc (sub_nonneg.mpr hts) hTt hratio
      dsimp [T]
      linarith
    · dsimp [T]
      nlinarith
  have h := volume_le_of_ordered_pair_bound (fun t ht ↦ ht.1) hT hT hpair
  convert h using 1
  congr 1
  dsimp [T]
  ring

/-- A linear bound on the measures of nonnegative deficit sublevels implies
the exponential integral bound, by Tonelli. -/
lemma lintegral_exp_neg_le_of_sublevel {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {F : α → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) {D : ℝ} (hD : 0 ≤ D)
    (hsub : ∀ K : ℝ, 0 < K → μ {x | F x ≤ K} ≤ ENNReal.ofReal (D * K)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-F x)) ∂μ) ≤ ENNReal.ofReal D := by
  let H : α → ℝ → ℝ≥0∞ := fun x K ↦
    if F x < K then ENNReal.ofReal (Real.exp (-K)) else 0
  have hH : Measurable (Function.uncurry H) := by
    apply Measurable.ite (measurableSet_lt (hF.comp measurable_fst) measurable_snd)
    · exact (Real.continuous_exp.measurable.comp measurable_snd.neg).ennreal_ofReal
    · exact measurable_const
  have htail (x : α) : (∫⁻ K in Ioi (0 : ℝ), H x K) =
      ENNReal.ofReal (Real.exp (-F x)) := by
    change (∫⁻ K in Ioi (0 : ℝ),
      (Ioi (F x)).indicator (fun K ↦ ENNReal.ofReal (Real.exp (-K))) K) = _
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi (hF0 x)),
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi (F x))
        (Filter.Eventually.of_forall fun K ↦ (Real.exp_pos (-K)).le),
      integral_exp_neg_Ioi]
  have hinner (K : ℝ) : (∫⁻ x, H x K ∂μ) =
      ENNReal.ofReal (Real.exp (-K)) * μ {x | F x < K} := by
    exact lintegral_indicator_const (measurableSet_lt hF measurable_const) _
  have hunit : (∫⁻ K in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-K) * K)) = 1 := by
    have hint : IntegrableOn (fun K : ℝ ↦ Real.exp (-K) * K) (Ioi 0) := by
      have hi := Real.GammaIntegral_convergent (s := 2) (by norm_num)
      norm_num at hi
      exact hi
    have hval : (∫ K : ℝ in Ioi 0, Real.exp (-K) * K) = 1 := by
      have hv := Real.Gamma_eq_integral (s := 2) (by norm_num)
      norm_num [Real.Gamma_ofNat_eq_factorial] at hv
      exact hv.symm
    calc
      _ = ENNReal.ofReal (∫ K : ℝ in Ioi 0, Real.exp (-K) * K) := by
        apply (ofReal_integral_eq_lintegral_ofReal hint ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with K hK
        exact mul_nonneg (Real.exp_pos _).le hK.le
      _ = 1 := by rw [hval]; norm_num
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (-F x)) ∂μ) =
        ∫⁻ x, (∫⁻ K in Ioi (0 : ℝ), H x K) ∂μ := by simp_rw [htail]
    _ = ∫⁻ K in Ioi (0 : ℝ), ∫⁻ x, H x K ∂μ :=
      lintegral_lintegral_swap hH.aemeasurable
    _ ≤ ∫⁻ K in Ioi (0 : ℝ),
        ENNReal.ofReal D * ENNReal.ofReal (Real.exp (-K) * K) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with K hK
      rw [hinner]
      calc
        ENNReal.ofReal (Real.exp (-K)) * μ {x | F x < K} ≤
            ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D * K) := by
          have hset : μ {x | F x < K} ≤ μ {x | F x ≤ K} :=
            measure_mono (show {x | F x < K} ⊆ {x | F x ≤ K} from
              fun x (hx : F x < K) ↦ (show F x ≤ K from hx.le))
          exact mul_le_mul_right
            (hset.trans (hsub K hK)) _
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hD]
          congr 1
          ring
    _ = ENNReal.ofReal D := by
      rw [lintegral_const_mul _ (by fun_prop), hunit, mul_one]

/-- The one-dimensional exponential estimate of Lemma `p102:u5-moser-1d`. -/
theorem oneDimensionalEstimate : OneDimensionalEstimate := by
  intro d hd
  have hc := (gapConstant_pos hd).le
  have hD : 0 ≤ 4 * (gapConstant d + 1) := by positivity
  refine ⟨4 * (gapConstant d + 1), hD, ?_⟩
  intro w hw
  let ν : Measure (Ioi (0 : ℝ)) := volume.comap Subtype.val
  have hmap : ν.map Subtype.val = volume.restrict (Ioi (0 : ℝ)) :=
    map_comap_subtype_coe measurableSet_Ioi volume
  have : SigmaFinite ν :=
    SigmaFinite.of_map ν measurable_subtype_coe.aemeasurable (by rw [hmap]; infer_instance)
  let F : Ioi (0 : ℝ) → ℝ := fun t ↦ (t : ℝ) - (w t) ^ (1 / exponent d)
  have hcontw : Continuous (fun t : Ioi (0 : ℝ) ↦ w t) :=
    continuousOn_iff_continuous_domRestrict.mp hw.continuousOn_pos
  have hF : Measurable F := by
    apply Continuous.measurable
    exact continuous_subtype_val.sub (hcontw.rpow_const fun _ ↦
      Or.inr (le_of_lt (one_div_pos.mpr (exponent_pos hd))))
  have hF0 (t : Ioi (0 : ℝ)) : 0 ≤ F t :=
    sub_nonneg.mpr (hw.power_le_time hd t.property.le)
  have hsub (K : ℝ) (hK : 0 < K) :
      ν {t | F t ≤ K} ≤ ENNReal.ofReal ((4 * (gapConstant d + 1)) * K) := by
    rw [show ν = volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) from rfl,
      comap_subtype_coe_apply measurableSet_Ioi]
    have himage : (Subtype.val : Ioi (0 : ℝ) → ℝ) '' {t | F t ≤ K} =
        {t : ℝ | 0 < t ∧ t - (w t) ^ (1 / exponent d) ≤ K} := by
      ext t
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, hx⟩
      · intro ht
        exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩
    rw [himage]
    exact hw.sublevel_volume hd hK
  have hmain := lintegral_exp_neg_le_of_sublevel ν hF hF0 hD hsub
  rw [← lintegral_subtype_comap measurableSet_Ioi
    (fun t : ℝ ↦ ENNReal.ofReal (Real.exp ((w t) ^ (1 / exponent d) - t)))]
  simpa only [F, neg_sub] using hmain

end P102.Sobolev.Moser
