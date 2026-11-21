import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.SecantOrder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SecantError
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.InexactLimits
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SecantConvergence
noncomputable section
namespace NumAnalysis206.Newton
open Set Filter
open scoped Topology goldenRatio
open Specs.NumAnalysis206.Newton

/-- The golden-ratio error law follows from the multiplicative recurrence;
existence of the ratio limit is a conclusion. -/
theorem secant_error_ratio_tendsto (E A : ℕ → ℝ) (C : ℝ)
    (hE : ∀ n, 0 < E n) (hA : ∀ n, 0 < A n) (hC : 0 < C)
    (hrec : ∀ n, E (n + 2) = A n * E (n + 1) * E n)
    (hlim : Tendsto A atTop (𝓝 C)) :
    Tendsto (fun n => E (n + 1) / (E n) ^ φ) atTop (𝓝 (C ^ (1 / φ))) := by
  let s : ℕ → ℝ := fun n => Real.log (E (n + 1)) - φ * Real.log (E n)
  let S : ℝ := Real.log C / φ
  let T : ℝ → ℝ := fun t => Real.log C - t / φ
  have hφ : 1 / φ = φ - 1 := by
    rw [one_div, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hfix : T S = S := by
    dsimp [T, S]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← one_div, hφ]
    linear_combination -Real.log C * Real.goldenRatio_sq
  have hs (n : ℕ) : s (n + 1) = Real.log (A n) - s n / φ := by
    dsimp [s]
    rw [show n + 1 + 1 = n + 2 by omega, hrec n,
      Real.log_mul (mul_pos (hA n) (hE (n + 1))).ne' (hE n).ne',
      Real.log_mul (hA n).ne' (hE (n + 1)).ne']
    rw [div_eq_mul_inv, ← one_div, hφ]
    linear_combination -Real.log (E n) * Real.goldenRatio_sq
  have hlog : Tendsto (fun n => Real.log (A n) - Real.log C) atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log hC.ne').tendsto.comp hlim).sub_const (Real.log C)
  have hs_lim : Tendsto s atTop (𝓝 S) := by
    apply NumAnalysis206.Iterations.inexact_tendsto_of_errors_tendsto_zero
      Set.univ T (1 / φ) S s (fun n => |Real.log (A n) - Real.log C|)
      (by positivity) (by simpa [one_div] using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
      (by simp) ?_ (by simp) hfix (by simp) ?_ ?_
    · intro u _ v _
      simp only [T, Real.dist_eq]
      rw [show Real.log C - u / φ - (Real.log C - v / φ) = -(u - v) / φ by ring,
        abs_div, abs_neg, abs_of_pos Real.goldenRatio_pos]
      exact le_of_eq (by ring)
    · intro n
      rw [hs n]
      simp only [T, Real.dist_eq]
      exact le_of_eq (congrArg abs (by ring))
    · simpa using hlog.abs
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hs_lim
  convert hexp using 1
  · ext n
    dsimp [s]
    rw [Real.exp_sub, Real.exp_log (hE (n + 1)), Real.rpow_def_of_pos (hE n)]
    congr 2
    ring
  · dsimp [S]
    rw [Real.rpow_def_of_pos hC]
    congr 1
    ring

/-- Apply the recurrence theorem to the actual two-slot secant orbit.
Nontermination supplies positive errors and a positive coefficient; convergence
and node distinctness come from the full run properties. -/
theorem secant_run_order (f : ℝ → ℝ) (p r m M u v : ℝ)
    (hf : ContDiffAt ℝ 2 f p) (hp : f p = 0) (hn : deriv f p ≠ 0)
    (hrun : Specs.NumAnalysis206.Newton.SecantConvergence.RunProperties f p r m M u v)
    (hnever : ¬ ∃ N, SuccessfulSecantStopValue f N (secantIteratesValue f u v))
    (hcurv : deriv (deriv f) p ≠ 0) :
    let C := |deriv (deriv f) p / (2 * deriv f p)|
    0 < C ^ (1 / φ) ∧
    Tendsto (fun n => |(secantIteratesValue f u v n).2 - p| /
        |(secantIteratesValue f u v n).1 - p| ^ φ)
      atTop (𝓝 (C ^ (1 / φ))) := by
  let X := secantIteratesValue f u v
  let E : ℕ → ℝ := fun n => |(X n).1 - p|
  let A : ℕ → ℝ := fun n =>
    |Specs.NumAnalysis206.Approximation.dividedDifferenceValue
      [((X n).1, f (X n).1), ((X n).2, f (X n).2), (p, f p)] /
      secantSlopeValue f (X n).1 (X n).2|
  let C := |deriv (deriv f) p / (2 * deriv f p)|
  have hC : 0 < C := abs_pos.mpr (div_ne_zero hcurv (mul_ne_zero (by norm_num) hn))
  obtain hstop | ⟨hvalid, hU, hV⟩ := hrun.2.2.2
  · exact (hnever hstop).elim
  have hup (n : ℕ) : (X n).1 ≠ p := by
    intro he
    exact (hvalid n).1 (by change f (X n).1 = 0; rw [he, hp])
  have hvp (n : ℕ) : (X n).2 ≠ p := by
    intro he
    exact (hvalid n).2.1 (by change f (X n).2 = 0; rw [he, hp])
  have hE (n : ℕ) : 0 < E n := abs_pos.mpr (sub_ne_zero.mpr (hup n))
  have hnext (n : ℕ) : X (n + 1) = ((X n).2, secantStepValue f (X n).1 (X n).2) :=
    (hrun.2.1 n (hvalid n).1 (hvalid n).2.1).2.1
  have hfirst (n : ℕ) : (X (n + 1)).1 = (X n).2 := congrArg Prod.fst (hnext n)
  have hsecond (n : ℕ) : (X (n + 1)).2 = secantStepValue f (X n).1 (X n).2 :=
    congrArg Prod.snd (hnext n)
  have habs (n : ℕ) : |(X (n + 1)).2 - p| = A n * |(X n).2 - p| * E n := by
    rw [hsecond, secant_error_identity f p (X n).1 (X n).2 hp
      (hvalid n).2.2.1 (hup n) (hvp n) (hvalid n).2.2.2, abs_mul, abs_mul]
  have hrec (n : ℕ) : E (n + 2) = A n * E (n + 1) * E n := by
    change |(X (n + 2)).1 - p| = A n * |(X (n + 1)).1 - p| * E n
    rw [show n + 2 = (n + 1) + 1 by omega, hfirst (n + 1), habs n, hfirst n]
  have hA (n : ℕ) : 0 < A n := by
    have hprod : 0 < A n * (E (n + 1) * E n) := by
      rw [← mul_assoc, ← hrec]
      exact hE (n + 2)
    exact (mul_pos_iff_of_pos_right (mul_pos (hE (n + 1)) (hE n))).mp hprod
  have hlim : Tendsto A atTop (𝓝 C) :=
    secant_coefficient_limit f p hf hp hn (fun n => (X n).1) (fun n => (X n).2)
      hU hV (Eventually.of_forall (fun n => ⟨(hvalid n).2.2.1, hup n, hvp n⟩))
  refine ⟨Real.rpow_pos_of_pos hC _, ?_⟩
  have hratio := secant_error_ratio_tendsto E A C hE hA hC hrec hlim
  convert hratio using 1
  ext n
  dsimp [E]
  rw [hfirst]

/-- Conditional retention of the quantitative interval theorem. The premises
are the complete frozen convergence interfaces, in their mandated order. -/
theorem secant_order_interval_convergence_conditional :
    Specs.NumAnalysis206.Newton.SecantConvergence.intervalConvergence →
    Specs.NumAnalysis206.Newton.SecantConvergence.localConvergence →
    Specs.NumAnalysis206.Newton.SecantOrder.intervalConvergence := by
  intro hinterval _
  exact hinterval

/-- Conditional W75: local well-definedness/stopping/convergence and the exact
positive golden-ratio asymptotic constant, uniformly for all nearby starts. -/
theorem secant_local_order_conditional :
    Specs.NumAnalysis206.Newton.SecantConvergence.intervalConvergence →
    Specs.NumAnalysis206.Newton.SecantConvergence.localConvergence →
    Specs.NumAnalysis206.Newton.SecantOrder.localOrder := by
  intro _ hlocal f p hf hp hn
  obtain ⟨R, m, M, r, hR, hm, hM, hr, hrR, hsmall, hjet, hb, hrun⟩ :=
    hlocal f p hf hp hn
  refine ⟨R, m, M, r, hR, hm, hM, hr, hrR, hsmall, hjet, hb, ?_⟩
  intro u v hu hv huv
  have hprops := hrun u v hu hv huv
  exact ⟨hprops, secant_run_order f p r m M u v hf hp hn hprops⟩

end NumAnalysis206.Newton

theorem _root_.«NumAnalysis206».«Newton».«secant_local_order» : _root_.«Specs».«NumAnalysis206».«Newton».«SecantOrder».«localOrder» :=
  @_root_.«NumAnalysis206».«Newton».«secant_local_order_conditional» (@_root_.«NumAnalysis206».«Newton».«secant_interval_convergence») (@_root_.«NumAnalysis206».«Newton».«secant_local_convergence»)
theorem _root_.«NumAnalysis206».«Newton».«secant_order_interval_convergence» : _root_.«Specs».«NumAnalysis206».«Newton».«SecantOrder».«intervalConvergence» :=
  @_root_.«NumAnalysis206».«Newton».«secant_order_interval_convergence_conditional» (@_root_.«NumAnalysis206».«Newton».«secant_interval_convergence») (@_root_.«NumAnalysis206».«Newton».«secant_local_convergence»)
