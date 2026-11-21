import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.MultipleConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.MultipleExpansion
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter Topology
namespace NumAnalysis206.Newton
open Specs.NumAnalysis206.Newton

/-- A bound on the distance to a fixed point suffices here; no two-point
Lipschitz estimate on the map is needed. -/
lemma local_distance_convergence (step : ℝ → ℝ) (p r q x₀ : ℝ)
    (x : ℕ → ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hx₀ : |x₀ - p| < r) (hx : IsExactRunValue step x₀ x)
    (hstep : ∀ y, |y - p| < r → |step y - p| ≤ q * |y - p|) :
    (∀ n, |x n - p| ≤ q ^ n * |x₀ - p| ∧ |x n - p| < r) ∧
      Tendsto x atTop (𝓝 p) := by
  have hbound : ∀ n, |x n - p| ≤ q ^ n * |x₀ - p| ∧ |x n - p| < r := by
    intro n
    induction n with
    | zero => simpa only [hx.1, pow_zero, one_mul] using And.intro (le_refl |x₀ - p|) hx₀
    | succ n ih =>
      have hs : |x (n + 1) - p| ≤ q * |x n - p| := by
        rw [hx.2 n]
        exact hstep _ ih.2
      constructor
      · calc
          |x (n + 1) - p| ≤ q * |x n - p| := hs
          _ ≤ q * (q ^ n * |x₀ - p|) := mul_le_mul_of_nonneg_left ih.1 hq
          _ = q ^ (n + 1) * |x₀ - p| := by rw [pow_succ]; ring
      · exact lt_of_le_of_lt
          (hs.trans (mul_le_of_le_one_left (abs_nonneg _) hq1.le)) ih.2
  refine ⟨hbound, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const |x₀ - p|
  simp only [zero_mul] at hlim
  simpa only [Real.dist_eq] using squeeze_zero (fun n => abs_nonneg (x n - p))
    (fun n => (hbound n).1) hlim

/-- Conversion of the one-point contraction estimate to valid, stopped runs. -/
lemma local_multiple_runs (f step : ℝ → ℝ) (p r q : ℝ)
    (hroot : f p = 0) (hq : 0 ≤ q) (hq1 : q < 1)
    (hfixed : ∀ y, f y = 0 → step y = y)
    (hvalid : ∀ y, |y - p| < r → y ≠ p → scalarStepValidValue f y)
    (hstep : ∀ y, |y - p| < r → |step y - p| ≤ q * |y - p|) :
    localMultipleRootRuns f p r q step := by
  intro x₀ x hx₀ hx
  have hstop : ∀ y, |y - p| < r →
      |stopAtRootValue f step y - p| ≤ q * |y - p| := by
    intro y hy
    by_cases hf : f y = 0
    · simpa only [stopAtRootValue, ite_eq_left hf, hfixed y hf] using hstep y hy
    · simpa only [stopAtRootValue, ite_eq_right hf] using hstep y hy
  obtain ⟨hb, ht⟩ := local_distance_convergence _ p r q x₀ x hq hq1 hx₀ hx hstop
  refine ⟨?_, ht, ?_⟩
  · intro n
    refine ⟨(hb n).1, (hb n).2, ?_⟩
    by_cases hf : f (x n) = 0
    · exact Or.inl hf
    · exact Or.inr (hvalid _ (hb n).2 (fun h => hf (h ▸ hroot)))
  · intro N hN k
    induction k with
    | zero => simpa using hN
    | succ k ih =>
      rw [Nat.add_succ, hx.2 (N + k), ih]
      simp only [stopAtRootValue, ite_eq_left hroot]

/-- Dividing a quadratic remainder by a nonzero error leaves a term tending
to zero. Reverse triangle inequality transfers this to absolute error ratios. -/
lemma error_ratio_tendsto (x : ℕ → ℝ) (p a C : ℝ) (ha : 0 ≤ a)
    (ht : Tendsto x atTop (𝓝 p)) (hne : ∀ n, x n ≠ p)
    (herr : ∀ n, |x (n + 1) - p - a * (x n - p)| ≤ C * |x n - p| ^ 2) :
    Tendsto (fun n => |x (n + 1) - p| / |x n - p|) atTop (𝓝 a) := by
  have hbound : ∀ n, |(|x (n + 1) - p| / |x n - p| - a)| ≤ C * |x n - p| := by
    intro n
    have he : 0 < |x n - p| := abs_pos.mpr (sub_ne_zero.mpr (hne n))
    have heq : |x (n + 1) - p| / |x n - p| - a =
        (|x (n + 1) - p| - a * |x n - p|) / |x n - p| := by
      field_simp
    have habs : |(|x (n + 1) - p| - a * |x n - p|)| ≤
        |x (n + 1) - p - a * (x n - p)| := by
      simpa only [abs_mul, abs_of_nonneg ha] using
        abs_abs_sub_abs_le_abs_sub (x (n + 1) - p) (a * (x n - p))
    rw [heq, abs_div, abs_abs]
    calc
      _ ≤ (C * |x n - p| ^ 2) / |x n - p| :=
        div_le_div_of_nonneg_right (habs.trans (herr n)) he.le
      _ = C * |x n - p| := by field_simp
  have habslim : Tendsto (fun n => |x n - p|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (ht.sub_const p).abs
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using
    squeeze_zero (fun n => abs_nonneg (|x (n + 1) - p| / |x n - p| - a))
      hbound (by simpa only [mul_zero] using habslim.const_mul C)

/-- W74, including invariant neighborhoods, successful stops, convergence of
both iterations, and the ordinary nonterminating error-ratio limit. -/
theorem multiple_root_convergence : multipleRootConvergence := by
  intro f g p m hm hg hgp hf
  obtain ⟨R, c, C, hR, hc, hC, hroot, hlocal⟩ :=
    multiple_root_expansion f g p m hm hg hgp hf
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hm)
  let a : ℝ := 1 - 1 / (m : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hmone
    simpa only [one_div_one] using sub_nonneg.mpr this
  have ha1 : a < 1 := by dsimp [a]; linarith [one_div_pos.mpr hmpos]
  let q : ℝ := (1 + a) / 2
  have haq : a < q := by dsimp [q]; linarith
  have hq : 0 ≤ q := le_trans ha haq.le
  have hqpos : 0 < q := lt_of_le_of_lt ha haq
  have hq1 : q < 1 := by dsimp [q]; linarith
  have habs : ContinuousAt (fun x : ℝ => |x - p|) p :=
    (continuousAt_id.sub continuousAt_const).abs
  have hnear : ∀ᶠ x in 𝓝 p,
      |x - p| < R ∧ a + C * |x - p| < q ∧ (m : ℝ) * C * |x - p| < q := by
    have h1 := habs.eventually_lt_const (by simpa using hR)
    have h2 : ∀ᶠ x in 𝓝 p, a + C * |x - p| < q :=
      (continuousAt_const.add (continuousAt_const.mul habs)).eventually_lt_const
        (by simpa [a] using haq)
    have h3 : ∀ᶠ x in 𝓝 p, (m : ℝ) * C * |x - p| < q :=
      (continuousAt_const.mul habs).eventually_lt_const
        (by simpa using hqpos)
    exact h1.and (h2.and h3)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hpoint : ∀ x : ℝ, |x - p| < r →
      DifferentiableAt ℝ f x ∧ (x ≠ p → deriv f x ≠ 0) ∧
      |scalarNewtonValue f x - p - a * (x - p)| ≤ C * |x - p| ^ 2 ∧
      |correctedNewtonValue m f x - p| ≤ (m : ℝ) * C * |x - p| ^ 2 ∧
      |scalarNewtonValue f x - p| ≤ q * |x - p| ∧
      |correctedNewtonValue m f x - p| ≤ q * |x - p| := by
    intro x hx
    obtain ⟨hxR, hsmall, hsmallc⟩ :=
      hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hx)
    obtain ⟨hd, hder, hden, hquot, herr, hcorr⟩ := hlocal x hxR
    refine ⟨hd, fun h => (hquot h).1, herr, hcorr, ?_, ?_⟩
    · calc
        |scalarNewtonValue f x - p| =
            |(scalarNewtonValue f x - p - a * (x - p)) + a * (x - p)| := by
              congr 1; ring
        _ ≤ |scalarNewtonValue f x - p - a * (x - p)| + |a * (x - p)| := abs_add_le _ _
        _ ≤ C * |x - p| ^ 2 + a * |x - p| := by
          rw [abs_mul, abs_of_nonneg ha]
          exact add_le_add herr le_rfl
        _ = (a + C * |x - p|) * |x - p| := by ring
        _ ≤ q * |x - p| := mul_le_mul_of_nonneg_right hsmall.le (abs_nonneg _)
    · calc
        |correctedNewtonValue m f x - p| ≤ (m : ℝ) * C * |x - p| ^ 2 := hcorr
        _ = ((m : ℝ) * C * |x - p|) * |x - p| := by ring
        _ ≤ q * |x - p| := mul_le_mul_of_nonneg_right hsmallc.le (abs_nonneg _)
  have hvalid : ∀ y, |y - p| < r → y ≠ p → scalarStepValidValue f y := by
    intro y hy hne
    exact ⟨(hpoint y hy).1, (hpoint y hy).2.1 hne⟩
  have hfixed : ∀ y, f y = 0 → scalarNewtonValue f y = y := by
    intro y hy
    simp only [scalarNewtonValue, hy, zero_div, sub_zero]
  have hfixedc : ∀ y, f y = 0 → correctedNewtonValue m f y = y := by
    intro y hy
    simp only [correctedNewtonValue, hy, mul_zero, zero_div, sub_zero]
  have hrun := local_multiple_runs f (scalarNewtonValue f) p r q hroot hq hq1
    hfixed hvalid (fun y hy => (hpoint y hy).2.2.2.2.1)
  have hrunc := local_multiple_runs f (correctedNewtonValue m f) p r q hroot hq hq1
    hfixedc hvalid (fun y hy => (hpoint y hy).2.2.2.2.2)
  refine ⟨r, C, q, hr, hC, hq, hq1, hroot, hpoint, hrun, hrunc, ?_⟩
  intro x₀ x hx₀ hx hne
  obtain ⟨hb, ht, hstop⟩ := hrun x₀ x hx₀ hx
  apply error_ratio_tendsto x p a C ha ht hne
  intro n
  have hnext : x (n + 1) = scalarNewtonValue f (x n) := by
    rw [hx.2 n]
    by_cases hf : f (x n) = 0
    · simp only [stopAtRootValue, ite_eq_left hf, hfixed _ hf]
    · simp only [stopAtRootValue, ite_eq_right hf]
  rw [hnext]
  exact (hpoint (x n) (hb n).2.1).2.2.1

end NumAnalysis206.Newton
