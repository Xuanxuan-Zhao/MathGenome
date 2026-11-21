import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.InverseSlope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace NumAnalysis206.Iterations.InverseSlope
open Set

/-- The mean value theorem bounds a secant from below without continuity of the derivative. -/
lemma mul_sub_le_abs_sub (f : ℝ → ℝ) {a b m : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hs : ∀ t ∈ Ioo a b, m ≤ |deriv f t|) :
    m * (b - a) ≤ |f b - f a| := by
  rcases hab.eq_or_lt with h | h
  · subst b
    simp
  · obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope f h hc hd
    have hbound := hs t ht
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr h)] at hbound
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hbound

/-- Proposition p206:W72, with exactly the segment mean-value hypotheses. -/
theorem certificate : Specs.NumAnalysis206.Iterations.InverseSlope.Certificate := by
  intro f x p m hp hm hc hd hs
  apply (le_div_iff₀ hm).mpr
  rcases le_total p x with h | h
  · have hc' : ContinuousOn f (Icc p x) := by
      simpa only [uIcc_of_le h] using hc
    have hd' : DifferentiableOn ℝ f (Ioo p x) := by
      simpa only [min_eq_left h, max_eq_right h] using hd
    have hs' : ∀ t ∈ Ioo p x, m ≤ |deriv f t| := by
      simpa only [min_eq_left h, max_eq_right h] using hs
    have he := mul_sub_le_abs_sub f h hc' hd' hs'
    simpa only [hp, sub_zero, abs_of_nonneg (sub_nonneg.mpr h), mul_comm] using he
  · have hc' : ContinuousOn f (Icc x p) := by
      simpa only [uIcc_of_ge h] using hc
    have hd' : DifferentiableOn ℝ f (Ioo x p) := by
      simpa only [min_eq_right h, max_eq_left h] using hd
    have hs' : ∀ t ∈ Ioo x p, m ≤ |deriv f t| := by
      simpa only [min_eq_right h, max_eq_left h] using hs
    have he := mul_sub_le_abs_sub f h hc' hd' hs'
    rw [hp, zero_sub, abs_neg] at he
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith

/-- Verification on an entire bracket suffices, including roots at its endpoints. -/
theorem bracketCertificate :
    Specs.NumAnalysis206.Iterations.InverseSlope.BracketCertificate := by
  intro f a b x p m hx hp hroot hm hc hd hs
  have hclosed : uIcc p x ⊆ Icc a b := by
    intro t ht
    exact ⟨le_trans (le_min hp.1 hx.1) ht.1,
      le_trans ht.2 (max_le hp.2 hx.2)⟩
  have hopen : Ioo (min p x) (max p x) ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_le_of_lt (le_min hp.1 hx.1) ht.1,
      lt_of_lt_of_le ht.2 (max_le hp.2 hx.2)⟩
  exact certificate f x p m hroot hm (hc.mono hclosed) (hd.mono hopen)
    (fun t ht => hs t (hopen ht))

/-- A certified bracket may specify a root existentially. -/
theorem bracketRootCertificate :
    Specs.NumAnalysis206.Iterations.InverseSlope.BracketRootCertificate := by
  intro f a b x m hx hroot hm hc hd hs
  obtain ⟨p, hp, hfp⟩ := hroot
  exact ⟨p, hp, hfp, bracketCertificate f a b x p m hx hp hfp hm hc hd hs⟩

private lemma small_positive (C r : ℝ) (hr : 0 < r) :
    ∃ x : ℝ, 0 < x ∧ x < r ∧ C * x < 1 := by
  let x := min (r / 2) (1 / (2 * (|C| + 1)))
  have hden : 0 < 2 * (|C| + 1) := by positivity
  have hx : 0 < x := lt_min (by positivity) (by positivity)
  have hxr : x < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hxb : x * (2 * (|C| + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hC : C ≤ |C| := le_abs_self C
  have hmul : C * x ≤ |C| * x := mul_le_mul_of_nonneg_right hC hx.le
  refine ⟨x, hx, hxr, ?_⟩
  nlinarith [abs_nonneg C]

/-- The square residual cannot linearly control error on any neighborhood of zero. -/
theorem squareCounterexample :
    Specs.NumAnalysis206.Iterations.InverseSlope.SquareCounterexample := by
  constructor
  · norm_num
  intro C r hr
  obtain ⟨x, hx, hxr, hCx⟩ := small_positive C r hr
  refine ⟨x, ?_, ?_, ?_⟩
  · simpa only [sub_zero, abs_of_pos hx] using hx
  · simpa only [sub_zero, abs_of_pos hx] using hxr
  · simp only [sub_zero, abs_of_pos hx, abs_of_nonneg (sq_nonneg x)]
    nlinarith [mul_lt_mul_of_pos_right hCx hx]

/-- The linear family has root zero and residual equal to its slope at error one. -/
theorem linearResidualFacts :
    Specs.NumAnalysis206.Iterations.InverseSlope.LinearResidualFacts := by
  intro σ hσ
  refine ⟨by simp, ?_, by norm_num, ?_⟩
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul σ).deriv
  · simp [abs_of_pos hσ]

/-- Arbitrarily small positive slopes give simple roots but residual arbitrarily small
at a point whose distance from the root is one. -/
theorem linearCounterexample :
    Specs.NumAnalysis206.Iterations.InverseSlope.LinearCounterexample := by
  intro C ε hε
  obtain ⟨σ, hσ, hσε, hCσ⟩ := small_positive C ε hε
  refine ⟨σ, hσ, by simp, ?_, by norm_num, ?_, ?_, ?_⟩
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul σ).deriv
  · simp [abs_of_pos hσ]
  · simpa [abs_of_pos hσ] using hσε
  · simpa [abs_of_pos hσ] using hCσ

end NumAnalysis206.Iterations.InverseSlope
