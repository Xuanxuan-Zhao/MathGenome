import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.LindebergTheorem
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.LyapunovCriterion

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace ProbabilityFoundations.Ch09.IndependentRows
variable {r : ℕ → ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The pointwise tail inequality, for a real positive excess exponent. -/
lemma square_tail_le_rpow (y δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    Set.indicator {y : ℝ | ε < |y|} (fun y => y^2) y ≤
      ε ^ (-δ) * |y| ^ (2 + δ) := by
  by_cases hy : ε < |y|
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hy]
    rw [Real.rpow_neg hε.le, inv_mul_eq_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hε δ)).2
    rw [Real.rpow_add (hε.trans hy), Real.rpow_two, sq_abs]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hε.le hy.le hδ.le) (sq_nonneg y)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hy]
    exact mul_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Lyapunov's quantitative bound for the strict Lindeberg tail. -/
theorem lindeberg_le_moment (R : Row r Ω) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hmoment : ∀ j, Integrable (fun ω => |normalized R n j ω| ^ (2 + δ)) (R.μ n))
    (ε : ℝ) (hε : 0 < ε) :
    lindeberg R n ε ≤ ε ^ (-δ) *
      ∑ j, ∫ ω, |normalized R n j ω| ^ (2 + δ) ∂R.μ n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∫ ω, ε ^ (-δ) * |normalized R n j ω| ^ (2 + δ) ∂R.μ n := by
      apply integral_mono (lindeberg_integrable R n j ε) ((hmoment j).const_mul _)
      intro ω
      exact square_tail_le_rpow (normalized R n j ω) δ ε hδ hε
    _ = _ := integral_const_mul _ _

/-- Scaling absolute moments uses the actual standard deviation of the row. -/
lemma normalized_abs_rpow (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (p : ℝ)
    (ω : Ω n) :
    |normalized R n j ω| ^ p = |R.X n j ω| ^ p / (scale R n) ^ p := by
  have hs : 0 ≤ scale R n := Real.sqrt_nonneg _
  rw [normalized, abs_div, abs_of_nonneg hs]
  exact Real.div_rpow (abs_nonneg _) hs _

lemma normalized_moment_integrable (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (p : ℝ)
    (h : Integrable (fun ω => |R.X n j ω| ^ p) (R.μ n)) :
    Integrable (fun ω => |normalized R n j ω| ^ p) (R.μ n) := by
  simp_rw [normalized_abs_rpow]
  exact h.div_const _

/-- The normalized sum of moments is exactly the original Lyapunov ratio. -/
lemma sum_normalized_moment (R : Row r Ω) (n : ℕ) (p : ℝ) :
    (∑ j, ∫ ω, |normalized R n j ω| ^ p ∂R.μ n) =
      (∑ j, ∫ ω, |R.X n j ω| ^ p ∂R.μ n) / (scale R n) ^ p := by
  simp_rw [normalized_abs_rpow, integral_div]
  rw [Finset.sum_div]

/-- Lyapunov's central limit criterion for centered independent finite rows. -/
theorem lyapunov_central_limit (R : Row r Ω) (δ : ℝ) (hδ : 0 < δ)
    (hvar : ∀ n, 0 < varianceSum R n)
    (hmoment : ∀ n j, Integrable (fun ω => |R.X n j ω| ^ (2 + δ)) (R.μ n))
    (hLyap : Tendsto (fun n => (∑ j, ∫ ω, |R.X n j ω| ^ (2 + δ) ∂R.μ n) /
      (scale R n) ^ (2 + δ)) atTop (𝓝 0)) :
    TendstoInDistribution (sum R) atTop (id : ℝ → ℝ) R.μ (gaussianReal 0 1) := by
  apply lindeberg_central_limit R hvar
  intro ε hε
  have hnormalized : Tendsto
      (fun n => ∑ j, ∫ ω, |normalized R n j ω| ^ (2 + δ) ∂R.μ n)
      atTop (𝓝 0) := by
    simpa only [sum_normalized_moment] using hLyap
  apply squeeze_zero (fun n => lindeberg_nonneg R n ε)
    (fun n => lindeberg_le_moment R n δ hδ
      (fun j => normalized_moment_integrable R n j _ (hmoment n j)) ε hε)
  simpa only [mul_zero] using hnormalized.const_mul (ε ^ (-δ))

end ProbabilityFoundations.Ch09.IndependentRows
