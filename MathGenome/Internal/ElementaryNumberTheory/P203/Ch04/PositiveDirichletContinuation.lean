import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.PositiveDirichletContinuation
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Complex Set
open scoped Topology

namespace P203.Ch04.PositiveDirichletContinuation

/-- The real coefficients occurring in the Taylor expansion at 2 before division
by the factorial. Division by `n²` makes the zero-indexed term identically zero. -/
def moment (b : ℕ → ℝ) (j n : ℕ) : ℝ :=
  b n / (n : ℝ)^2 * Real.log n ^ j

lemma logMul_iterate (b : ℕ → ℝ) (j n : ℕ) :
    (LSeries.logMul^[j] (fun k => (b k : ℂ))) n =
      (Real.log n : ℂ)^j * (b n : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, ← Complex.natCast_log]
    simp only [pow_succ]
    ring

lemma term_moment (b : ℕ → ℝ) (j n : ℕ) :
    LSeries.term (LSeries.logMul^[j] (fun k => (b k : ℂ))) 2 n =
      (moment b j n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moment]
  · rw [LSeries.term_of_ne_zero hn, logMul_iterate]
    simp only [moment, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.cpow_ofNat]
    ring

lemma moment_nonneg {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (j n : ℕ) :
    0 ≤ moment b j n :=
  mul_nonneg (div_nonneg (hb n) (sq_nonneg _))
    (pow_nonneg (Real.log_natCast_nonneg n) _)

lemma moment_summable {b : ℕ → ℝ}
    (hc : LSeries.abscissaOfAbsConv (fun k => (b k : ℂ)) < (2 : ℝ)) (j : ℕ) :
    Summable (moment b j) := by
  have h : LSeriesSummable (LSeries.logMul^[j] (fun k => (b k : ℂ))) 2 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  exact Complex.summable_ofReal.mp (h.congr (term_moment b j))

lemma derivative_moments {b : ℕ → ℝ} {F : ℂ → ℂ}
    (hc : LSeries.abscissaOfAbsConv (fun k => (b k : ℂ)) < (2 : ℝ))
    (heq : EqOn F (LSeries (fun k => (b k : ℂ))) {s | 1 < s.re}) (j : ℕ) :
    iteratedDeriv j F 2 = (-1 : ℂ)^j * (∑' n, moment b j n : ℝ) := by
  rw [heq.iteratedDeriv_of_isOpen (isOpen_lt continuous_const continuous_re) j
    (by norm_num : (2 : ℂ) ∈ {s | 1 < s.re}),
    LSeries_iteratedDeriv j (by simpa using hc), LSeries, Complex.ofReal_tsum]
  congr 1
  exact tsum_congr (term_moment b j)

lemma taylor_moments {b : ℕ → ℝ} {F : ℂ → ℂ}
    (hc : LSeries.abscissaOfAbsConv (fun k => (b k : ℂ)) < (2 : ℝ))
    (hf : DifferentiableOn ℂ F {s | 0 < s.re})
    (heq : EqOn F (LSeries (fun k => (b k : ℂ))) {s | 1 < s.re})
    {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 2) :
    Summable (fun j => (2 - σ)^j / j.factorial * ∑' n, moment b j n) := by
  have hd : DifferentiableOn ℂ F (Metric.ball 2 2) := by
    apply hf.mono
    intro z hz
    have hn : ‖z - 2‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hr := (abs_le.mp (Complex.abs_re_le_norm (z - 2))).1
    simp only [sub_re, re_ofNat] at hr
    change 0 < z.re
    linarith
  have hz : (σ : ℂ) ∈ Metric.ball 2 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have ht := (Complex.hasSum_taylorSeries_on_ball hd hz).summable
  have hterm (j : ℕ) :
      (j.factorial : ℂ)⁻¹ • ((σ : ℂ) - 2)^j • iteratedDeriv j F 2 =
        (((2 - σ)^j / j.factorial * ∑' n, moment b j n : ℝ) : ℂ) := by
    rw [derivative_moments hc heq]
    simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_ofNat]
    have hp : ((σ : ℂ) - 2)^j * (-1 : ℂ)^j = ((2 : ℂ) - σ)^j := by
      rw [← mul_pow]
      congr 1
      ring
    calc
      _ = (j.factorial : ℂ)⁻¹ * (((σ : ℂ) - 2)^j * (-1 : ℂ)^j) *
        (∑' n, moment b j n : ℝ) := by ring
      _ = _ := by rw [hp]; ring
  exact Complex.summable_ofReal.mp (ht.congr hterm)

/-- Nonnegative Taylor terms, with the two indices left separate. -/
def taylorKernel (b : ℕ → ℝ) (t : ℝ) (j n : ℕ) : ℝ :=
  t^j / j.factorial * moment b j n

lemma kernel_hasSum (b : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    HasSum (fun j => taylorKernel b t j n)
      (b n / (n : ℝ)^2 * Real.exp (t * Real.log n)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (t * Real.log n)).mul_left
    (b n / (n : ℝ)^2)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext j
  simp only [taylorKernel, moment, mul_pow]
  ring

/-- Tonelli for the nonnegative Taylor expansion proves convergence of the
exponentially recombined moments. No convergence at `σ` is assumed here. -/
lemma recombined_summable {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {F : ℂ → ℂ}
    (hc : LSeries.abscissaOfAbsConv (fun k => (b k : ℂ)) < (2 : ℝ))
    (hf : DifferentiableOn ℂ F {s | 0 < s.re})
    (heq : EqOn F (LSeries (fun k => (b k : ℂ))) {s | 1 < s.re})
    {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 2) :
    Summable (fun n => b n / (n : ℝ)^2 * Real.exp ((2 - σ) * Real.log n)) := by
  have hnonneg (j n : ℕ) : 0 ≤ taylorKernel b (2 - σ) j n :=
    mul_nonneg (div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
      (moment_nonneg hb j n)
  have hs (j : ℕ) : Summable (taylorKernel b (2 - σ) j) :=
    (moment_summable hc j).mul_left _
  have hout : Summable (fun j => ∑' n, taylorKernel b (2 - σ) j n) := by
    simpa only [taylorKernel, tsum_mul_left] using taylor_moments hc hf heq hσ hσ2
  have hp : Summable (fun p : ℕ × ℕ => taylorKernel b (2 - σ) p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => hnonneg p.1 p.2)).mpr ⟨hs, hout⟩
  exact hp.prod_symm.prod.congr (fun n => (kernel_hasSum b (2 - σ) n).tsum_eq)

lemma recombined_eq (b : ℕ → ℝ) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    b n / (n : ℝ)^2 * Real.exp ((2 - σ) * Real.log n) =
      b n * Real.exp (-σ * Real.log n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have he : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ)^2 := by
    simpa using (Real.exp_nat_mul (Real.log (n : ℝ)) 2).trans
      (congrArg (fun x : ℝ => x^2) (Real.exp_log hnpos))
  rw [show (2 - σ) * Real.log (n : ℝ) =
    2 * Real.log (n : ℝ) + (-σ * Real.log (n : ℝ)) by ring, Real.exp_add, he]
  field_simp

/-- The standard L-series convention at a positive index agrees with the
exponential convention fixed in the source. -/
lemma term_eq_exp (a : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term a s n = a n * Complex.exp (-s * (Real.log n : ℂ)) := by
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr hn), div_eq_mul_inv, ← Complex.exp_neg, ← Complex.natCast_log]
  congr 2
  ring

/-- Internal form with Mathlib's zero-padded indexing. -/
lemma continuation_LSeries {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hc : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (b n : ℂ)) s)
    {F : ℂ → ℂ} (hf : DifferentiableOn ℂ F {s | 0 < s.re})
    (heq : EqOn F (LSeries (fun n => (b n : ℂ))) {s | 1 < s.re})
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => b (n + 1) * Real.exp (-σ * Real.log (n + 1))) := by
  by_cases hσ1 : 1 < σ
  · have hs := hc σ (by simpa using hσ1)
    have hshift := (summable_nat_add_iff 1).mpr hs
    have hh : Summable (fun n : ℕ =>
        ((b (n + 1) * Real.exp (-σ * Real.log (n + 1)) : ℝ) : ℂ)) := by
      convert hshift using 1
      funext n
      rw [term_eq_exp _ _ (Nat.succ_ne_zero n)]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
        Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]
    exact Complex.summable_ofReal.mp hh
  · have hab : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ (1 : ℝ) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (fun y hy => hc y (by simpa using hy))
    have hlt : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < (2 : ℝ) :=
      hab.trans_lt (by exact_mod_cast (show (1 : ℝ) < 2 by norm_num))
    have hs := recombined_summable hb hlt hf heq hσ (by linarith)
    exact ((summable_nat_add_iff 1).mpr hs).congr
      (fun n => by simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        recombined_eq b σ (Nat.succ_ne_zero n))

/-- Continuation from nonnegative coefficients (Lemma 4.7). -/
theorem continuation : P203Specs.Ch04.PositiveDirichletContinuation.continuation_type := by
  intro b hb habs F hf heq σ hσ
  let a : ℕ → ℝ := fun n => b (n - 1)
  have hterm (s : ℂ) (n : ℕ) :
      LSeries.term (fun k => (a k : ℂ)) s (n + 1) =
        (b n : ℂ) * Complex.exp (-s * (Real.log (n + 1) : ℂ)) := by
    rw [term_eq_exp _ _ (Nat.succ_ne_zero n)]
    simp [a]
  have hc (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun k => (a k : ℂ)) s := by
    apply (summable_nat_add_iff 1).mp
    exact (summable_norm_iff.mp (habs s hs)).congr (fun n => (hterm s n).symm)
  have hEq : EqOn F (LSeries (fun k => (a k : ℂ))) {s | 1 < s.re} := by
    intro s hs
    rw [heq s hs, LSeries, (hc s hs).tsum_eq_zero_add, LSeries.term_zero, zero_add]
    exact tsum_congr (fun n => (hterm s n).symm)
  have h := continuation_LSeries (fun n => hb (n - 1)) hc hf hEq hσ
  simpa [a] using h

end P203.Ch04.PositiveDirichletContinuation
