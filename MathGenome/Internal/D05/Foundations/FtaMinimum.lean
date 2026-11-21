import MathGenome.Internal.Specs.D05.Foundations.FtaMinimum
import MathGenome.Internal.D05.Foundations.FormalPolynomials

/-!
The coercivity/minimum portion of the elementary FTA proof. The growth lemma
used below works in arbitrary normed rings with an absolute-value norm, and is
proved by polynomial degree induction, independently of the FTA. The minimum
is obtained on a compact complex disk; no root-existence result is used.
-/

namespace D05.Foundations.FtaMinimum

open Filter

theorem lowerBound : D05.Specs.FtaMinimum.lowerBound := by
  intro p z
  let s : ℂ := ∑ j ∈ Finset.range p.natDegree, p.coeff j * z ^ j
  have heval : p.eval z = s + p.leadingCoeff * z ^ p.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
      Polynomial.coeff_natDegree]
  have hs : ‖s‖ ≤ ∑ j ∈ Finset.range p.natDegree, ‖p.coeff j‖ * ‖z‖ ^ j := by
    simpa only [s, norm_mul, norm_pow] using
      (norm_sum_le (Finset.range p.natDegree) (fun j => p.coeff j * z ^ j))
  have ht := norm_sub_le (p.eval z) s
  rw [heval, add_sub_cancel_left, norm_mul, norm_pow] at ht
  rw [← heval] at ht
  exact sub_le_iff_le_add.mpr (ht.trans (add_le_add_right hs _))

theorem lowerDegreeBound : D05.Specs.FtaMinimum.lowerDegreeBound := by
  intro p z hz
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact pow_le_pow_right₀ hz (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj))

theorem coercivity : D05.Specs.FtaMinimum.coercivity := by
  intro p hp
  apply p.tendsto_norm_atTop
  · exact Polynomial.natDegree_pos_iff_degree_pos.mp hp
  · exact tendsto_comap

theorem outsideDisk : D05.Specs.FtaMinimum.outsideDisk := by
  intro p hp
  have h := (coercivity p hp).eventually (eventually_gt_atTop ‖p.eval 0‖)
  rcases (eventually_atTop.mp (eventually_comap.mp h)) with ⟨r, hr⟩
  refine ⟨max 1 r, le_max_left _ _, ?_⟩
  intro z hz
  exact hr ‖z‖ ((le_max_right 1 r).trans hz.le) z rfl

theorem globalMinimum : D05.Specs.FtaMinimum.globalMinimum := by
  intro p hp
  obtain ⟨R, hR, hout⟩ := outsideDisk p hp
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 R := by
    simpa using ((zero_le_one : (0 : ℝ) ≤ 1).trans hR)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMinOn
    ⟨0, hzero⟩ p.continuous.norm.continuousOn
  refine ⟨z₀, fun z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall 0 R
  · exact hmin hz
  · have hz' : R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    exact (hmin hzero).trans (hout z hz').le

end D05.Foundations.FtaMinimum
