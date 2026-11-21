import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.TaylorRemainderBounds
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.TaylorSmoothness
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Metric
open scoped Topology ENNReal

namespace D12Complex.TaylorRemainderBounds
open Taylor

private theorem closedBall_subset_eball (a : ℂ) (r : ℝ) (R : ℝ≥0∞)
    (hrR : ENNReal.ofReal r < R) : closedBall a r ⊆ eball a R := by
  intro z hz
  apply lt_of_le_of_lt _ hrR
  simpa [edist_dist] using ENNReal.ofReal_le_ofReal (mem_closedBall.mp hz)

theorem derivative_bound :
    Specs.D12Complex.Ch05.TaylorRemainderBounds.derivative_bound_type := by
  intro a R f r M hf hr hrR hM k
  exact DiskCauchyDerivatives.disk_cauchy_estimate a r (eball a R) f M hr hf
    (closedBall_subset_eball a r R hrR) hM k

theorem coefficient_bound :
    Specs.D12Complex.Ch05.TaylorRemainderBounds.coefficient_bound_type := by
  intro a R f r M hf hr hrR hM n
  have hd := derivative_bound a R f r M hf hr hrR hM n
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [Taylor.coefficients, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hn).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hd

theorem remainder_bound :
    Specs.D12Complex.Ch05.TaylorRemainderBounds.remainder_bound_type := by
  intro a R f r M hf hr hrR hM N z hz
  let q : ℝ := ‖z - a‖ / r
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hr.le
  have hq1 : q < 1 := (div_lt_one hr).mpr hz
  have hR : 0 < R := (ENNReal.ofReal_pos.mpr hr).trans hrR
  have hzR : z ∈ eball a R :=
    closedBall_subset_eball a r R hrR (mem_closedBall_iff_norm.mpr hz.le)
  have hs := TaylorSmoothness.taylor_hasSum a R f hR hf z hzR
  have ht : HasSum (fun n => coefficients f a (n + (N + 1)) *
      (z - a) ^ (n + (N + 1)))
      (f z - ∑ n ∈ Finset.range (N + 1), coefficients f a n * (z - a) ^ n) := by
    apply (hasSum_nat_add_iff' (N + 1)).mpr
    exact hs
  have hg : HasSum (fun n : ℕ => M * q ^ (N + 1) * q ^ n)
      (M * q ^ (N + 1) / (1 - q)) := by
    simpa [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q ^ (N + 1))
  apply ht.norm_le_of_bounded hg
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖coefficients f a (n + (N + 1))‖ * ‖z - a‖ ^ (n + (N + 1)) ≤
        (M / r ^ (n + (N + 1))) * ‖z - a‖ ^ (n + (N + 1)) :=
      mul_le_mul_of_nonneg_right (coefficient_bound a R f r M hf hr hrR hM _)
        (pow_nonneg (norm_nonneg _) _)
    _ = M * q ^ (N + 1) * q ^ n := by
      simp only [q, pow_add, div_eq_mul_inv, mul_inv_rev]
      ring

theorem bounds_at_circle_maximum :
    Specs.D12Complex.Ch05.TaylorRemainderBounds.bounds_at_circle_maximum_type := by
  intro a R f r hf hr hrR
  obtain ⟨b, hb, hmax, hd⟩ := DiskCauchyDerivatives.disk_cauchy_estimate_max
    a r (eball a R) f hr hf (closedBall_subset_eball a r R hrR)
  exact ⟨b, hb, hmax, coefficient_bound a R f r ‖f b‖ hf hr hrR hmax,
    hd, remainder_bound a R f r ‖f b‖ hf hr hrR hmax⟩

end D12Complex.TaylorRemainderBounds
