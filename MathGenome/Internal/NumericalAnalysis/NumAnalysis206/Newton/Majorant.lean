import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Majorant
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Newton.Majorant
open Filter

lemma derivative (η L t : ℝ) : deriv (majorant η L) t = L * t - 1 := by
  have h := ((hasDerivAt_const t η).sub (hasDerivAt_id t)).add
    ((hasDerivAt_const t (L / 2)).mul ((hasDerivAt_id t).pow 2))
  have hh : HasDerivAt (majorant η L)
      (0 - 1 + (0 * t ^ 2 + L / 2 * (2 * t ^ (2 - 1) * 1))) t := h
  rw [hh.deriv]
  ring

lemma root_data {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L ≤ 1) :
    0 ≤ discriminant η L ∧ discriminant η L < 1 ∧
    L * lowerRoot η L = 1 - discriminant η L ∧
    L * upperRoot η L = 1 + discriminant η L ∧
    0 < lowerRoot η L ∧
    majorant η L (lowerRoot η L) = 0 ∧ majorant η L (upperRoot η L) = 0 := by
  have hd : 0 ≤ discriminant η L := Real.sqrt_nonneg _
  have hsq : discriminant η L ^ 2 = 1 - 2 * η * L := Real.sq_sqrt (by linarith)
  have hd1 : discriminant η L < 1 := by nlinarith [mul_pos hη hL]
  have ha : L * lowerRoot η L = 1 - discriminant η L := by
    unfold lowerRoot; field_simp
  have hc : L * upperRoot η L = 1 + discriminant η L := by
    unfold upperRoot; field_simp
  have hap : 0 < lowerRoot η L := by nlinarith
  refine ⟨hd, hd1, ha, hc, hap, ?_, ?_⟩
  · unfold majorant
    nlinarith [sq_nonneg (L * lowerRoot η L - (1 - discriminant η L))]
  · unfold majorant
    nlinarith [sq_nonneg (L * upperRoot η L - (1 + discriminant η L))]

lemma factorization {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L ≤ 1)
    (t : ℝ) : majorant η L t = (L / 2) * (t - lowerRoot η L) * (t - upperRoot η L) := by
  rcases root_data hη hL hb with ⟨hd, hd1, ha, hc, hap, hma, hmc⟩
  have hsum : L * (lowerRoot η L + upperRoot η L) = 2 := by linarith
  have hprod : L * lowerRoot η L * upperRoot η L = 2 * η := by
    have hsq : discriminant η L ^ 2 = 1 - 2 * η * L := Real.sq_sqrt (by linarith)
    have he : (L * lowerRoot η L) * (L * upperRoot η L) = 2 * η * L := by
      rw [ha, hc]; nlinarith
    nlinarith
  calc
    majorant η L t = L / 2 * t ^ 2 - (L * (lowerRoot η L + upperRoot η L)) / 2 * t +
        (L * lowerRoot η L * upperRoot η L) / 2 := by
      rw [hsum, hprod]; unfold majorant; ring
    _ = _ := by ring

lemma below_root {η L t : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L ≤ 1)
    (ht : t < lowerRoot η L) :
    0 < majorant η L t ∧ 0 < 1 - L * t ∧
    1 - L * t = discriminant η L + L * (lowerRoot η L - t) := by
  rcases root_data hη hL hb with ⟨hd, hd1, ha, hc, hap, hma, hmc⟩
  have he : 1 - L * t = discriminant η L + L * (lowerRoot η L - t) := by nlinarith
  have hp : 0 < 1 - L * t := by nlinarith [mul_pos hL (sub_pos.mpr ht)]
  have hu : lowerRoot η L ≤ upperRoot η L := by nlinarith
  rw [factorization hη hL hb]
  exact ⟨mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by positivity) (by linarith))
    (by linarith), hp, he⟩

lemma step_add (η L t : ℝ) :
    newtonStep η L t = t + majorant η L t / (1 - L * t) := by
  unfold newtonStep
  rw [show L * t - 1 = -(1 - L * t) by ring, div_neg]
  ring

lemma step_error {η L t : ℝ} (hroot : majorant η L (lowerRoot η L) = 0)
    (hden : 1 - L * t ≠ 0) :
    lowerRoot η L - newtonStep η L t =
      L / (2 * (1 - L * t)) * (lowerRoot η L - t) ^ 2 := by
  rw [step_add]
  unfold majorant at *
  have hd : 1 - t * L ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hden, hd]
  nlinarith only [hroot]

lemma step_residual {η L t : ℝ} (hden : 1 - L * t ≠ 0) :
    majorant η L (newtonStep η L t) =
      (L / 2) * (newtonStep η L t - t) ^ 2 := by
  rw [step_add]
  unfold majorant
  have hd : 1 - t * L ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hden, hd]
  ring

lemma step_control {η L t : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hb : 2 * η * L ≤ 1) (ht : t < lowerRoot η L) :
    t < newtonStep η L t ∧ newtonStep η L t < lowerRoot η L ∧
    L / (2 * (1 - L * t)) * (lowerRoot η L - t) ≤ 1 / 2 := by
  rcases below_root hη hL hb ht with ⟨hm, hp, he⟩
  have hroot := (root_data hη hL hb).2.2.2.2.2.1
  have herr := step_error hroot (ne_of_gt hp)
  have hc : 0 < L / (2 * (1 - L * t)) := div_pos hL (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [step_add]; linarith [div_pos hm hp]
  · have := mul_pos hc (sq_pos_of_pos (sub_pos.mpr ht))
    linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * (1 - L * t))]
    have hd : 0 ≤ discriminant η L := Real.sqrt_nonneg _
    nlinarith

lemma iterate_bounds {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L ≤ 1)
    (n : ℕ) : 0 ≤ iterate η L n ∧ iterate η L n < lowerRoot η L := by
  induction n with
  | zero => exact ⟨le_refl 0, (root_data hη hL hb).2.2.2.2.1⟩
  | succ n ih =>
    have hs := step_control hη hL hb ih.2
    exact ⟨le_trans ih.1 hs.1.le, hs.2.1⟩

lemma iterate_properties {η L : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hb : 2 * η * L ≤ 1) (n : ℕ) :
    0 ≤ iterate η L n ∧ iterate η L n < lowerRoot η L ∧
    0 < majorant η L (iterate η L n) ∧ 0 < 1 - L * iterate η L n ∧
    iterate η L n < iterate η L (n + 1) ∧
    0 < error η L n ∧ 0 < coefficient η L n ∧
    majorant η L (iterate η L (n + 1)) = (L / 2) *
      (iterate η L (n + 1) - iterate η L n) ^ 2 ∧
    error η L (n + 1) = coefficient η L n * error η L n ^ 2 ∧
    coefficient η L n * error η L n ≤ 1 / 2 ∧
    (0 < discriminant η L → coefficient η L n ≤ L / (2 * discriminant η L)) := by
  have hi := iterate_bounds hη hL hb n
  rcases below_root hη hL hb hi.2 with ⟨hm, hp, he⟩
  have hs := step_control hη hL hb hi.2
  have hroot := (root_data hη hL hb).2.2.2.2.2.1
  refine ⟨hi.1, hi.2, hm, hp, hs.1, sub_pos.mpr hi.2,
    div_pos hL (by positivity), step_residual (ne_of_gt hp),
    step_error hroot (ne_of_gt hp), hs.2.2, ?_⟩
  intro hd
  unfold coefficient
  apply div_le_div_of_nonneg_left hL.le (by positivity) _
  nlinarith [mul_pos hL (sub_pos.mpr hi.2)]

lemma error_halving_bound {η L : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hb : 2 * η * L ≤ 1) (n : ℕ) :
    error η L (n + 1) ≤ (1 / 2) * error η L n := by
  have hp := iterate_properties hη hL hb n
  have he := hp.2.2.2.2.2.2.2.2.1
  have hc := hp.2.2.2.2.2.2.2.2.2.1
  calc
    error η L (n + 1) = (coefficient η L n * error η L n) * error η L n := by
      rw [he]; ring
    _ ≤ (1 / 2) * error η L n := mul_le_mul_of_nonneg_right hc hp.2.2.2.2.2.1.le

lemma error_geometric_bound {η L : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hb : 2 * η * L ≤ 1) (n : ℕ) :
    error η L n ≤ lowerRoot η L * (1 / 2) ^ n := by
  induction n with
  | zero => simp [error, iterate]
  | succ n ih =>
    calc
      error η L (n + 1) ≤ (1 / 2) * error η L n := error_halving_bound hη hL hb n
      _ ≤ (1 / 2) * (lowerRoot η L * (1 / 2) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = lowerRoot η L * (1 / 2) ^ (n + 1) := by rw [pow_succ]; ring

lemma iterate_tendsto {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L ≤ 1) :
    Tendsto (iterate η L) atTop (nhds (lowerRoot η L)) := by
  have hg : Tendsto (fun n : ℕ => lowerRoot η L * (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (lowerRoot η L)
  have he : Tendsto (error η L) atTop (nhds 0) :=
    squeeze_zero (fun n => (sub_pos.mpr (iterate_bounds hη hL hb n).2).le)
      (error_geometric_bound hη hL hb) hg
  have hh : Tendsto (fun n => lowerRoot η L - error η L n) atTop
      (nhds (lowerRoot η L - 0)) := tendsto_const_nhds.sub he
  simpa [error] using hh

lemma strict_case {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L < 1) :
    lowerRoot η L < upperRoot η L ∧
    ∀ s, lowerRoot η L < s → s < upperRoot η L → majorant η L s < 0 := by
  have hd : 0 < discriminant η L := Real.sqrt_pos.mpr (by linarith)
  rcases root_data hη hL hb.le with ⟨_, _, ha, hc, _, _, _⟩
  refine ⟨?_, ?_⟩
  · nlinarith
  · intro s hs hs'
    rw [factorization hη hL hb.le]
    exact mul_neg_of_pos_of_neg (mul_pos (by positivity) (sub_pos.mpr hs)) (sub_neg.mpr hs')

lemma critical_case {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (hb : 2 * η * L = 1) :
    discriminant η L = 0 ∧ lowerRoot η L = upperRoot η L ∧
    deriv (majorant η L) (lowerRoot η L) = 0 ∧
    (∀ t, majorant η L t = (L / 2) * (t - lowerRoot η L) ^ 2) ∧
    ∀ n, error η L (n + 1) = error η L n / 2 := by
  have hd : discriminant η L = 0 := by simp [discriminant, hb]
  have hr : lowerRoot η L = upperRoot η L := by simp [lowerRoot, upperRoot, hd]
  rcases root_data hη hL hb.le with ⟨_, _, ha, _, _, _, _⟩
  refine ⟨hd, hr, ?_, ?_, ?_⟩
  · rw [derivative]; rw [hd] at ha; linarith
  · intro t
    rw [factorization hη hL hb.le, ← hr]
    ring
  · intro n
    have hi := iterate_bounds hη hL hb.le n
    have hp := iterate_properties hη hL hb.le n
    have he := hp.2.2.2.2.2.2.2.2.1
    have hden := hp.2.2.2.1
    have hc : coefficient η L n * error η L n = 1 / 2 := by
      unfold coefficient error
      rw [div_mul_eq_mul_div, div_eq_iff (by positivity : 2 * (1 - L * iterate η L n) ≠ 0)]
      rw [hd] at ha
      nlinarith
    calc
      error η L (n + 1) = (coefficient η L n * error η L n) * error η L n := by
        rw [he]; ring
      _ = error η L n / 2 := by rw [hc]; ring

/-- Scalar majorant, valid for the strict and critical Kantorovich data. -/
theorem scalar_majorant : Specs.NumAnalysis206.Newton.Majorant.statement := by
  intro η L hη hL hb
  rcases root_data hη hL hb with ⟨hd, hd1, ha, hc, hap, hma, hmc⟩
  exact ⟨derivative η L, hd, hd1, hap, hma, hmc, factorization hη hL hb,
    iterate_properties hη hL hb,
    strictMono_nat_of_lt_succ (fun n => (iterate_properties hη hL hb n).2.2.2.2.1),
    iterate_tendsto hη hL hb, strict_case hη hL, critical_case hη hL⟩

end NumAnalysis206.Newton.Majorant
