import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.WholeLineFailure

/-!
# Local uniform convergence without uniform convergence on the whole line

K03.12.whole_line_failure, paper.tex:1339–1347.
The factorial majorant and the upstream M-test give interval convergence;
uniqueness of ordinary series limits identifies the sum. On the positive
half-line the first omitted term bounds the error from below. This growing
monomial makes every fixed partial-sum error unbounded, contradicting the
single error bound required by uniform convergence on ℝ.
-/
noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators

/-- The M-test controls all points of a bounded interval simultaneously. -/
theorem exp_partialSums_uniform_interval (A : ℝ) (hA : 0 < A) :
    RealUniformConverges
      (fun N (x : Set.Icc (-A) A) =>
        realPartialSum (fun n => (x : ℝ)^n / (n.factorial : ℝ)) N)
      (fun x => realSeriesExp x) := by
  obtain ⟨⟨f, hf⟩, _⟩ := real_m_test
    (fun n (x : Set.Icc (-A) A) => (x : ℝ)^n / (n.factorial : ℝ))
    (fun n => A^n / (n.factorial : ℝ))
    (fun n => by positivity)
    (fun n x => by
      simp only [abs_div, abs_pow, Nat.abs_cast]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr x.property) n) (by positivity))
    ⟨_, real_expSeries_hasSum A⟩
  have he : f = fun (x : Set.Icc (-A) A) => realSeriesExp x := by
    funext x
    exact real_series_sum_unique _ _ _ (realUniformConverges_pointwise _ _ hf x)
      (real_expSeries_hasSum x)
  simpa only [he] using hf

/-- The first omitted nonnegative term is a lower bound for the error. -/
theorem exp_partialSum_remainder_lower (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x^(N+1) / ((N+1).factorial : ℝ) ≤
      realSeriesExp x - realPartialSum (fun n => x^n / (n.factorial : ℝ)) N := by
  have h := Real.sum_le_exp_of_nonneg hx (N + 1 + 1)
  rw [Finset.sum_range_succ, ← expSeries_eq_realExp x] at h
  change (∑ n ∈ Finset.range (N+1), x^n / (n.factorial : ℝ)) +
    x^(N+1) / ((N+1).factorial : ℝ) ≤ realSeriesExp x at h
  dsimp [realPartialSum]
  linarith

/-- No fixed partial sum has a bounded error on the nonnegative half-line. -/
theorem exp_partialSum_error_unbounded (N : ℕ) (B : ℝ) :
    ∃ x : ℝ, 0 ≤ x ∧
      B < realSeriesExp x - realPartialSum (fun n => x^n / (n.factorial : ℝ)) N := by
  let d : ℝ := (N+1).factorial
  have hd : 0 < d := by dsimp [d]; positivity
  let x : ℝ := max 1 (B*d+1)
  have hx1 : 1 ≤ x := le_max_left _ _
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hBx : B*d < x := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hpow : x ≤ x^(N+1) := le_self_pow₀ hx1 (Nat.succ_ne_zero N)
  refine ⟨x, hx0, ?_⟩
  calc
    B < x / d := (lt_div_iff₀ hd).mpr hBx
    _ ≤ x^(N+1) / d := div_le_div_of_nonneg_right hpow hd.le
    _ ≤ realSeriesExp x - realPartialSum (fun n => x^n / (n.factorial : ℝ)) N :=
      exp_partialSum_remainder_lower N x hx0

/-- A single positive tolerance already rules out whole-line uniformity. -/
theorem exp_partialSums_not_uniform :
    ¬ RealUniformConverges
      (fun N (x : ℝ) => realPartialSum (fun n => x^n / (n.factorial : ℝ)) N)
      realSeriesExp := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  obtain ⟨x, _, hx⟩ := exp_partialSum_error_unbounded N 1
  have habs := hN N le_rfl x
  have hle := le_abs_self (realSeriesExp x -
    realPartialSum (fun n => x^n / (n.factorial : ℝ)) N)
  rw [abs_sub_comm] at habs
  linarith

end SingleVariableAnalysis
