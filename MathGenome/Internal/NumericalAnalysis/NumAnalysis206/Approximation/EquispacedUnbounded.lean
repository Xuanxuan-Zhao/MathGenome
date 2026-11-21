import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.EquispacedUnbounded
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.EquispacedLebesgue
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Filter
open scoped Topology
namespace NumAnalysis206.Approximation

/-- The numerical lower bound in W54 tends to infinity. -/
private theorem equispaced_lower_tendsto :
    Tendsto (fun n : ℕ => (2 : ℝ)^n / (2 * (n : ℝ) * ((n : ℝ)+1)^2))
      atTop atTop := by
  have h (k : ℕ) := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hd : Tendsto (fun n : ℕ => (2 * (n : ℝ) * ((n : ℝ)+1)^2) / (2 : ℝ)^n)
      atTop (𝓝 0) := by
    convert ((h 3).const_mul 2 |>.add ((h 2).const_mul 4) |>.add ((h 1).const_mul 2)) using 1
    · ext n
      ring
    · norm_num
  have hp : ∀ᶠ n : ℕ in atTop,
      0 < (2 * (n : ℝ) * ((n : ℝ)+1)^2) / (2 : ℝ)^n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  convert (tendsto_nhdsWithin_iff.mpr ⟨hd, hp⟩).inv_tendsto_nhdsGT_zero using 1
  ext n
  simp only [Pi.inv_apply, inv_div]

/-- W54: a single continuous function has unbounded equispaced interpolants. -/
theorem equispaced_unbounded (a b : ℝ) (hab : a < b) :
    ∃ f : IntervalContinuous a b, ∀ B : ℝ,
      ∃ (n : ℕ) (hn : 2 ≤ n),
        B < ‖interpolationOperator
          (equispacedNodes a b hab n (lt_of_lt_of_le (by decide) hn)) f‖ := by
  classical
  by_contra h
  push Not at h
  let T : {n : ℕ // 2 ≤ n} → IntervalContinuous a b →L[ℝ] IntervalContinuous a b :=
    fun n => interpolationOperator (equispacedNodes a b hab n (by omega))
  have hb : ∀ f, ∃ B : ℝ, ∀ n, ‖T n f‖ ≤ B := by
    intro f
    obtain ⟨B, hB⟩ := h f
    exact ⟨B, fun n => hB n n.property⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  obtain ⟨n, hn, hnC⟩ := ((eventually_ge_atTop 2).and
    (equispaced_lower_tendsto.eventually_gt_atTop C)).exists
  have hl := equispaced_lebesgue_lower a b hab n hn
  have he := interpolation_norm (equispacedNodes a b hab n (by omega)) hab
    (equispaced_nodes_injective a b hab n (by omega))
  have hu := hC ⟨n, hn⟩
  change ‖interpolationOperator (equispacedNodes a b hab n _)‖ ≤ C at hu
  rw [he] at hu
  exact (not_lt_of_ge (hl.trans hu)) hnC

end NumAnalysis206.Approximation
