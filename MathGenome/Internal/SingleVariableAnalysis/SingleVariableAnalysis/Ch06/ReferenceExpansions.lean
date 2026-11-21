import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.UniformBound
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ElementaryDerivatives
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.ReferenceExpansions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

noncomputable section
namespace SingleVariableAnalysis.ReferenceExpansions
open Set Filter
open scoped BigOperators Topology
open Specs.SingleVariableAnalysis.Ch06.ReferenceExpansions

/-- An actual derivative tower on an open domain identifies all total derivatives
there; no statement is made about the exterior extension. -/
theorem tower_iteratedDeriv {s : Set ℝ} (hs : IsOpen s) (f : ℝ → ℝ)
    (D : ℕ → ℝ → ℝ) (h0 : EqOn (D 0) f s)
    (hd : ∀ k x, x ∈ s → HasDerivAt (D k) (D (k+1) x) x) (k : ℕ) :
    EqOn (iteratedDeriv k f) (D k) s := by
  induction k with
  | zero => exact h0.symm
  | succ k ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    exact ((hd k x hx).congr_of_eventuallyEq
      (ih.eventuallyEq_of_mem (hs.mem_nhds hx))).deriv

/-- Apply the accepted uniform Taylor estimate to a differentiable tower. -/
theorem tower_taylor_bound {s : Set ℝ} (hs : IsOpen s) (f : ℝ → ℝ)
    (D : ℕ → ℝ → ℝ) (h0 : EqOn (D 0) f s)
    (hd : ∀ k x, x ∈ s → HasDerivAt (D k) (D (k+1) x) x)
    (n : ℕ) (r M : ℝ) (hr : 0 ≤ r) (hI : Icc (-r) r ⊆ s)
    (hM : ∀ x ∈ Icc (-r) r, |D (n+1) x| ≤ M)
    (x : ℝ) (hx : |x| ≤ r) :
    |f x - ∑ k ∈ Finset.range (n+1), D k 0 / (k.factorial : ℝ) * x^k| ≤
      M / ((n+1).factorial : ℝ) * |x|^(n+1) := by
  have heq := tower_iteratedDeriv hs f D h0 hd
  have hD : ClosedDerivativeFamily n f (-r) r D := by
    refine ⟨h0.mono hI, ?_, ?_⟩
    · intro k _ t ht
      exact (hd k t (hI ht)).continuousAt.continuousWithinAt
    · intro k _ t ht
      exact (hd k t (hI ht)).hasDerivWithinAt
  have hd' : ∀ t ∈ Ioo (-r) r, DifferentiableAt ℝ (RealIteratedDerivative n f) t := by
    intro t ht
    exact ((hd n t (hI (Ioo_subset_Icc_self ht))).congr_of_eventuallyEq
      ((heq n).eventuallyEq_of_mem (hs.mem_nhds (hI (Ioo_subset_Icc_self ht))))).differentiableAt
  have hM' : ∀ t ∈ Ioo (-r) r, ‖RealIteratedDerivative (n+1) f t‖ ≤ M := by
    intro t ht
    change |iteratedDeriv (n+1) f t| ≤ M
    rw [heq (n+1) (hI (Ioo_subset_Icc_self ht))]
    exact hM t (Ioo_subset_Icc_self ht)
  have h := uniform_taylor_bound f n (-r) r M D hD hd' hM'
    0 ⟨by linarith, hr⟩ x (abs_le.mp hx)
  simpa only [Real.norm_eq_abs, sub_zero, Algebra.algebraMap_self_apply] using h

theorem falling_succ (α : ℝ) (k : ℕ) : falling α (k+1) = falling α k * (α-k) := by
  exact Finset.prod_range_succ _ _

theorem power_tower_deriv (α : ℝ) (k : ℕ) (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun t : ℝ => falling α k * (1+t)^(α-k))
      (falling α (k+1) * (1+x)^(α-((k+1:ℕ):ℝ))) x := by
  have h := (((hasDerivAt_id x).const_add 1).rpow_const (p := α-(k:ℝ))
    (Or.inl (show 1+x ≠ 0 by linarith))).const_mul (falling α k)
  convert h using 1
  · rfl
  · simp only [id_eq, falling_succ, Nat.cast_add, Nat.cast_one]
    rw [show α - ((k:ℝ)+1) = α-(k:ℝ)-1 by ring]
    ring

def logJet : ℕ → ℝ → ℝ
  | 0 => fun x => Real.log (1+x)
  | k+1 => fun x => (-1 : ℝ)^k * (k.factorial : ℝ) * (1+x)^(-(k:ℝ)-1)

theorem log_tower_deriv (k : ℕ) (x : ℝ) (hx : -1 < x) :
    HasDerivAt (logJet k) (logJet (k+1) x) x := by
  have hp : 0 < 1+x := by linarith
  cases k with
  | zero =>
    simpa [logJet, Real.rpow_neg_one] using
      ((hasDerivAt_id x).const_add 1).log hp.ne'
  | succ k =>
    have h := (((hasDerivAt_id x).const_add 1).rpow_const (p := -(k:ℝ)-1)
      (Or.inl hp.ne')).const_mul ((-1 : ℝ)^k * (k.factorial : ℝ))
    convert h using 1
    · rfl
    · simp only [id_eq, logJet, pow_succ, Nat.factorial_succ, Nat.cast_add,
        Nat.cast_mul, Nat.cast_one]
      have he : -((k:ℝ)+1)-1 = -(k:ℝ)-1-1 := by ring
      rw [he]
      ring

theorem exp_eq : realSeriesExp = Real.exp := funext expSeries_eq_realExp

theorem sin_eq : realSeriesSin = Real.sin := funext fun x => (sinCosSeries_eq_real x).1
theorem cos_eq : realSeriesCos = Real.cos := funext fun x => (sinCosSeries_eq_real x).2

theorem reference_exp_derivatives : expDerivatives := by
  intro k x
  change iteratedDeriv k realSeriesExp x = realSeriesExp x
  rw [exp_eq, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

theorem reference_log_derivatives : logDerivatives := by
  intro k x hx
  change iteratedDeriv (k+1) (fun t => seriesLog (1+t)) x = _
  have hp : 0 < 1+x := by linarith
  have h := tower_iteratedDeriv isOpen_Ioi (fun t => seriesLog (1+t)) logJet
    (fun t ht => (seriesLog_eq_realLog (1+t) (by change -1 < t at ht; linarith)).symm)
    (fun j t ht => log_tower_deriv j t ht) (k+1) hx
  rw [h]
  simp only [logJet]
  rw [show -(k:ℝ)-1 = -((k+1 : ℕ):ℝ) by push_cast; ring,
    Real.rpow_neg hp.le, Real.rpow_natCast]
  ring

theorem reference_power_derivatives : powerDerivatives := by
  intro α k x hx
  change iteratedDeriv k (fun t => realPower (1+t) α) x =
    falling α k * realPower (1+x) (α-k)
  have h := tower_iteratedDeriv isOpen_Ioi (fun t => realPower (1+t) α)
    (fun j t => falling α j * (1+t)^(α-j))
    (fun t ht => by simp [falling, realPower_eq_rpow (1+t)
      (show 0 < 1+t by change -1 < t at ht; linarith)])
    (fun j t ht => power_tower_deriv α j t ht) k hx
  rw [h, realPower_eq_rpow (1+x) (by linarith)]

theorem reference_trig_derivatives : trigDerivatives := by
  intro k x
  change iteratedDeriv (2*k) realSeriesSin x = _ ∧ _ ∧ _ ∧ _
  change iteratedDeriv (2*k) realSeriesSin x = (-1 : ℝ)^k * realSeriesSin x ∧
    iteratedDeriv (2*k+1) realSeriesSin x = (-1 : ℝ)^k * realSeriesCos x ∧
    iteratedDeriv (2*k) realSeriesCos x = (-1 : ℝ)^k * realSeriesCos x ∧
    iteratedDeriv (2*k+1) realSeriesCos x = (-1 : ℝ)^(k+1) * realSeriesSin x
  rw [sin_eq, cos_eq]
  simp [pow_succ]

theorem reference_exp_derivative_bound : expDerivativeBound := by
  intro n r _ x hx
  rw [reference_exp_derivatives]
  change |realSeriesExp x| ≤ Real.exp r
  rw [exp_eq, abs_of_pos (Real.exp_pos x)]
  exact Real.exp_le_exp.mpr ((le_abs_self x).trans hx)

theorem reference_log_derivative_bound : logDerivativeBound := by
  intro n r _ hr x hx
  have hp : 0 < 1+x := by have := (abs_le.mp hx).1; linarith
  rw [reference_log_derivatives n x (by linarith)]
  rw [abs_div, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (show (0:ℝ) ≤ (n.factorial : ℝ) by positivity),
    abs_of_pos (pow_pos hp _)]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos (by linarith) _)
  exact pow_le_pow_left₀ (by linarith) (by have := (abs_le.mp hx).1; linarith) _

theorem rpow_le_max_endpoints (α r x : ℝ) (hr : r < 1) (hx : |x| ≤ r) :
    (1+x)^α ≤ max ((1-r)^α) ((1+r)^α) := by
  have hl : 0 < 1-r := by linarith
  have hp : 0 < 1+x := by have := (abs_le.mp hx).1; linarith
  by_cases hα : 0 ≤ α
  · exact (Real.rpow_le_rpow hp.le (by have := (abs_le.mp hx).2; linarith) hα).trans
      (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hl
      (by have := (abs_le.mp hx).1; linarith) (le_of_not_ge hα)).trans (le_max_left _ _)

theorem reference_power_derivative_bound : powerDerivativeBound := by
  intro α n r _ hr x hx
  have hp : 0 < 1+x := by have := (abs_le.mp hx).1; linarith
  rw [reference_power_derivatives α (n+1) x (by linarith)]
  change |falling α (n+1) * realPower (1+x) (α-((n+1:ℕ):ℝ))| ≤ powerBound α n r
  rw [realPower_eq_rpow (1+x) hp, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  unfold powerBound
  have he : α - ((n+1 : ℕ):ℝ) = α-n-1 := by push_cast; ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (rpow_le_max_endpoints _ _ _ hr hx) (abs_nonneg _)

theorem reference_trig_derivative_bound : trigDerivativeBound := by
  intro k x
  change |iteratedDeriv k realSeriesSin x| ≤ 1 ∧ |iteratedDeriv k realSeriesCos x| ≤ 1
  rw [sin_eq, cos_eq]
  exact ⟨Real.abs_iteratedDeriv_sin_le_one k x, Real.abs_iteratedDeriv_cos_le_one k x⟩

theorem reference_exp_uniform : expUniform := by
  intro n r hr x hx
  change |realSeriesExp x - expPoly n x| ≤ _
  have h := tower_taylor_bound isOpen_univ realSeriesExp (fun _ => Real.exp)
    (fun t _ => (congrFun exp_eq t).symm) (fun _ t _ => Real.hasDerivAt_exp t)
    n r (Real.exp r) hr.le (by simp) (fun t ht => by
      rw [abs_of_pos (Real.exp_pos t)]
      exact Real.exp_le_exp.mpr ht.2) x hx
  simpa [expPoly, div_eq_mul_inv, mul_comm] using h

theorem log_taylor_sum (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n+1), logJet k 0 / (k.factorial : ℝ) * x^k) = logPoly n x := by
  rw [Finset.sum_range_succ']
  simp only [logJet, add_zero, Real.log_one, zero_div, pow_zero, add_zero,
    Real.one_rpow, mul_one]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ]
  push_cast
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hn : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem reference_log_uniform : logUniform := by
  intro n r hr hr1 x hx
  change |seriesLog (1+x) - logPoly n x| ≤ _
  have hI : Icc (-r) r ⊆ Ioi (-1) := by
    intro t ht
    change -1 < t
    linarith [ht.1]
  have h := tower_taylor_bound isOpen_Ioi (fun t => seriesLog (1+t)) logJet
    (fun t ht => (seriesLog_eq_realLog (1+t) (by change -1 < t at ht; linarith)).symm)
    (fun j t ht => log_tower_deriv j t ht) n r
    ((n.factorial : ℝ) / (1-r)^(n+1)) hr.le hI (fun t ht => ?_) x hx
  · rw [log_taylor_sum] at h
    convert h using 1
    rw [Nat.factorial_succ]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    have hp : (1-r)^(n+1) ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
  · have hp : 0 < 1+t := by have := hI ht; change -1 < t at this; linarith
    rw [show logJet (n+1) t = (-1 : ℝ)^n * (n.factorial : ℝ) / (1+t)^(n+1) by
      simp only [logJet]
      rw [show -(n:ℝ)-1 = -((n+1 : ℕ):ℝ) by push_cast; ring,
        Real.rpow_neg hp.le, Real.rpow_natCast]
      ring]
    rw [← reference_log_derivatives n t (hI ht)]
    exact reference_log_derivative_bound n r hr hr1 t (abs_le.mpr ht)

theorem reference_power_uniform : powerUniform := by
  intro α n r hr hr1 x hx
  change |realPower (1+x) α - powerPoly α n x| ≤ _
  have hI : Icc (-r) r ⊆ Ioi (-1) := by
    intro t ht
    change -1 < t
    linarith [ht.1]
  have h := tower_taylor_bound isOpen_Ioi (fun t => realPower (1+t) α)
    (fun j t => falling α j * (1+t)^(α-j))
    (fun t ht => by simp [falling, realPower_eq_rpow (1+t)
      (show 0 < 1+t by change -1 < t at ht; linarith)])
    (fun j t ht => power_tower_deriv α j t ht) n r (powerBound α n r) hr.le hI
    (fun t ht => ?_) x hx
  · simpa [powerPoly] using h
  · have hp : 0 < 1+t := by have := hI ht; change -1 < t at this; linarith
    have hb := reference_power_derivative_bound α n r hr hr1 t (abs_le.mpr ht)
    rw [reference_power_derivatives α (n+1) t (hI ht)] at hb
    change |falling α (n+1) * realPower (1+t) (α-((n+1:ℕ):ℝ))| ≤ _ at hb
    rw [realPower_eq_rpow (1+t) hp] at hb
    exact hb

theorem sin_taylor_sum (m : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (2*m+3), iteratedDeriv k Real.sin 0 / (k.factorial : ℝ) * x^k) =
      sinPoly m x := by
  induction m with
  | zero => simp [sinPoly, Finset.sum_range_succ]
  | succ m ih =>
    rw [show 2*(m+1)+3 = (2*m+3)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [show 2*m+3+1 = 2*(m+2) by omega,
      show 2*m+3 = 2*(m+1)+1 by omega]
    simp only [Real.iteratedDeriv_even_sin, Real.iteratedDeriv_odd_sin,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.sin_zero,
      Real.cos_zero, mul_zero, mul_one, zero_div, zero_mul, add_zero]
    simp only [sinPoly, Finset.sum_range_succ]
    ring

theorem cos_taylor_sum (m : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (2*m+2), iteratedDeriv k Real.cos 0 / (k.factorial : ℝ) * x^k) =
      cosPoly m x := by
  induction m with
  | zero => simp [cosPoly, Finset.sum_range_succ]
  | succ m ih =>
    rw [show 2*(m+1)+2 = (2*m+2)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [show 2*m+2+1 = 2*(m+1)+1 by omega,
      show 2*m+2 = 2*(m+1) by omega]
    simp only [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.sin_zero,
      Real.cos_zero, mul_zero, mul_one, zero_div, zero_mul, add_zero]
    simp only [cosPoly, Finset.sum_range_succ]
    ring

theorem reference_sin_uniform : sinUniform := by
  intro m r hr x hx
  change |realSeriesSin x - sinPoly m x| ≤ _
  have h := tower_taylor_bound isOpen_univ realSeriesSin (fun j => iteratedDeriv j Real.sin)
    (by intro t _; simpa using (congrFun sin_eq t).symm)
    (fun j t _ => by simpa only [iteratedDeriv_succ] using
      (Real.differentiable_iteratedDeriv_sin j t).hasDerivAt)
    (2*m+2) r 1 hr.le (by simp)
    (fun t _ => Real.abs_iteratedDeriv_sin_le_one _ t) x hx
  rw [show 2*m+2+1 = 2*m+3 by omega, sin_taylor_sum] at h
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

theorem reference_cos_uniform : cosUniform := by
  intro m r hr x hx
  change |realSeriesCos x - cosPoly m x| ≤ _
  have h := tower_taylor_bound isOpen_univ realSeriesCos (fun j => iteratedDeriv j Real.cos)
    (by intro t _; simpa using (congrFun cos_eq t).symm)
    (fun j t _ => by simpa only [iteratedDeriv_succ] using
      (Real.differentiable_iteratedDeriv_cos j t).hasDerivAt)
    (2*m+1) r 1 hr.le (by simp)
    (fun t _ => Real.abs_iteratedDeriv_cos_le_one _ t) x hx
  rw [show 2*m+1+1 = 2*m+2 by omega, cos_taylor_sum] at h
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

theorem bigO_of_uniform_bound (f : ℝ → ℝ) (k : ℕ) (r C : ℝ) (hr : 0 < r)
    (h : ∀ x, |x| ≤ r → |f x| ≤ C * |x|^k) :
    Asymptotics.IsBigO (𝓝 (0:ℝ)) f (fun x => x^k) := by
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with x hx
  simpa only [Real.norm_eq_abs, abs_pow] using h x
    (le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx))

theorem reference_exp_bigO : expBigO := by
  intro n
  exact bigO_of_uniform_bound _ (n+1) 1 (Real.exp 1 / ((n+1).factorial : ℝ))
    zero_lt_one (reference_exp_uniform n 1 zero_lt_one)

theorem reference_log_bigO : logBigO := by
  intro n
  apply bigO_of_uniform_bound _ (n+1) (1/2) (1 / ((n+1) * (1-1/2)^(n+1))) (by norm_num)
  intro x hx
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
    reference_log_uniform n (1/2) (by norm_num) (by norm_num) x hx

theorem reference_power_bigO : powerBigO := by
  intro α n
  exact bigO_of_uniform_bound _ (n+1) (1/2)
    (powerBound α n (1/2) / ((n+1).factorial : ℝ)) (by norm_num)
    (reference_power_uniform α n (1/2) (by norm_num) (by norm_num))

theorem reference_sin_bigO : sinBigO := by
  intro m
  apply bigO_of_uniform_bound _ (2*m+3) 1 (1 / ((2*m+3).factorial : ℝ)) zero_lt_one
  intro x hx
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using reference_sin_uniform m 1 zero_lt_one x hx

theorem reference_cos_bigO : cosBigO := by
  intro m
  apply bigO_of_uniform_bound _ (2*m+2) 1 (1 / ((2*m+2).factorial : ℝ)) zero_lt_one
  intro x hx
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using reference_cos_uniform m 1 zero_lt_one x hx

end SingleVariableAnalysis.ReferenceExpansions
