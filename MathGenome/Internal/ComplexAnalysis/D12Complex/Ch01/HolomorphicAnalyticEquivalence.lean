import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.TaylorSmoothness

/-!
The eventual equivalence of the three canonical notions of Chapter 1.
The forward power-series implication uses the proved Taylor theorem on
an interior disk. The reverse uses convergence of an actual scalar series
and the direct power-series calculus. No regularity certificate is assumed.
-/

open Filter Set Metric
open scoped Topology ContDiff NNReal ENNReal

namespace D12Complex.HolomorphicAnalyticEquivalence

open PowerSeriesCalculus

/-- Convergence at a noncentral point forces a positive convergence radius.
The series sum is differentiable at the center, and agrees locally with f. -/
theorem powerSeriesAnalyticAt_differentiableAt :
    Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence.powerSeriesAnalyticAt_differentiableAt_type := by
  rintro f a ⟨r, hr, c, hc⟩
  let b : ℂ := a + ((r / 2 : ℝ) : ℂ)
  have hb : ‖b - a‖ = r / 2 := by
    simpa only [b, add_sub_cancel_left] using
      (Complex.norm_of_nonneg (r := r / 2) (half_pos hr).le)
  have hs : Summable (fun n => c n * (b - a)^n) :=
    (hc b (by rw [hb]; linarith)).summable
  have hrad : (‖b - a‖₊ : ℝ≥0∞) ≤ powerSeriesRadius c := by
    apply le_of_not_gt
    intro hout
    exact PowerSeriesRadius.not_summable_outside c a b hout hs
  have hpos : 0 < powerSeriesRadius c := by
    apply lt_of_lt_of_le _ hrad
    simpa only [ENNReal.coe_pos, nnnorm_pos] using
      (norm_pos_iff.mp (show 0 < ‖b - a‖ by rw [hb]; exact half_pos hr))
  have hd := (hasDerivAt_sum c a a (by simpa [convergenceDisk] using hpos)).differentiableAt
  apply hd.congr_of_eventuallyEq
  apply eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr))
  intro z hz
  exact (hc z (mem_ball_iff_norm.mp hz)).tsum_eq.symm

theorem holomorphicOn_iff_c1HolomorphicOn :
    Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence.holomorphicOn_iff_c1HolomorphicOn_type := by
  intro Ω f
  constructor
  · intro hf
    refine ⟨hf, ?_⟩
    simpa only [iteratedDeriv_one] using
      DiskCauchyDerivatives.continuousOn_iteratedDeriv Ω f hf 1
  · exact And.left

theorem holomorphicOn_iff_powerSeriesAnalyticOn :
    Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence.holomorphicOn_iff_powerSeriesAnalyticOn_type := by
  intro Ω f
  constructor
  · intro hf
    refine ⟨hf.1, fun a ha => ?_⟩
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hf.1 a ha
    have hdisk : HolomorphicOn (eball a (ENNReal.ofReal r)) f := by
      rw [Metric.eball_ofReal]
      exact ⟨isOpen_ball, fun z hz => hf.2 z (hsub hz)⟩
    refine ⟨r, hr, Taylor.coefficients f a, fun z hz => ?_⟩
    exact TaylorSmoothness.taylor_hasSum a (ENNReal.ofReal r) f
      (ENNReal.ofReal_pos.mpr hr) hdisk z
      (by rwa [Metric.eball_ofReal, mem_ball_iff_norm])
  · intro hf
    exact ⟨hf.1, fun a ha => powerSeriesAnalyticAt_differentiableAt f a (hf.2 a ha)⟩

theorem c1HolomorphicOn_iff_powerSeriesAnalyticOn :
    Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence.c1HolomorphicOn_iff_powerSeriesAnalyticOn_type := by
  intro Ω f
  exact (holomorphicOn_iff_c1HolomorphicOn Ω f).symm.trans
    (holomorphicOn_iff_powerSeriesAnalyticOn Ω f)

private theorem holomorphicOn_of_three_notions (Ω : Set ℂ) (f : ℂ → ℂ)
    (h : HolomorphicOn Ω f ∨ C1HolomorphicOn Ω f ∨ PowerSeriesAnalyticOn Ω f) :
    HolomorphicOn Ω f := by
  rcases h with h | h | h
  · exact h
  · exact h.1
  · exact (holomorphicOn_iff_powerSeriesAnalyticOn Ω f).mpr h

theorem three_notions_real_smooth :
    Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence.three_notions_real_smooth_type := by
  intro Ω f h
  exact TaylorSmoothness.holomorphic_real_smooth Ω f (holomorphicOn_of_three_notions Ω f h)

theorem three_notions_iteratedDeriv :
    Specs.D12Complex.Ch01.HolomorphicAnalyticEquivalence.three_notions_iteratedDeriv_type := by
  intro Ω f h
  exact DiskCauchyDerivatives.holomorphicOn_iteratedDeriv Ω f
    (holomorphicOn_of_three_notions Ω f h)

end D12Complex.HolomorphicAnalyticEquivalence
