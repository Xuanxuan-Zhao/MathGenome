import MathGenome.Internal.RealAnalysis.D11.Ch13.LebesgueDifferentiation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.ApproximateContinuity

/-! Approximate continuity from the ball-wise Chebyshev inequality and
Lebesgue differentiation, for the shared completed Euclidean measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch13.ApproximateContinuity
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch13.AveragesMaximalDefinition
open D11.Ch13.LebesgueDifferentiation

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace n
variable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Chebyshev on a ball, with its finite positive volume made explicit. -/
lemma density_le_oscillation (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (x : Point n) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    (lebesgue n {y | y ∈ Metric.ball x r ∧ ε < ‖f y - f x‖}).toReal /
      (lebesgue n (Metric.ball x r)).toReal ≤ ε⁻¹ * oscillationAverage f hf r x := by
  have hm := ball_measure x r hr
  have hi := (integrableOn_ball f hf x r).sub
    (integrableOn_const (C := f x) hm.2.1.ne)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (lebesgue n).restrict (Metric.ball x r))
    (ae_of_all _ (fun y => norm_nonneg (f y - f x))) hi.norm ε
  have hnorm : Measurable (fun y => ‖f y - f x‖) :=
    (hf.1.sub measurable_const).norm
  have hlevel : MeasurableSet {y | ε ≤ ‖f y - f x‖} :=
    measurableSet_le measurable_const hnorm
  rw [measureReal_def, Measure.restrict_apply hlevel] at hmark
  have hfin : lebesgue n ({y | ε ≤ ‖f y - f x‖} ∩ Metric.ball x r) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right hm.2.1.ne
  have hmono :
      (lebesgue n {y | y ∈ Metric.ball x r ∧ ε < ‖f y - f x‖}).toReal ≤
      (lebesgue n ({y | ε ≤ ‖f y - f x‖} ∩ Metric.ball x r)).toReal := by
    apply ENNReal.toReal_mono hfin
    exact measure_mono (fun y hy => ⟨hy.2.le, hy.1⟩)
  have hb := (mul_le_mul_of_nonneg_left hmono hε.le).trans hmark
  have hdiv :
      (lebesgue n {y | y ∈ Metric.ball x r ∧ ε < ‖f y - f x‖}).toReal ≤
        (∫ y in Metric.ball x r, ‖f y - f x‖ ∂(lebesgue n)) / ε :=
    (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hb)
  calc
    _ ≤ ((∫ y in Metric.ball x r, ‖f y - f x‖ ∂(lebesgue n)) / ε) /
        (lebesgue n (Metric.ball x r)).toReal :=
      div_le_div_of_nonneg_right hdiv hm.2.2.le
    _ = _ := by
      change _ = ε⁻¹ * ((lebesgue n (Metric.ball x r)).toReal⁻¹ *
        ∫ y in Metric.ball x r, ‖f y - f x‖ ∂(lebesgue n))
      simp only [div_eq_mul_inv]
      ring

/-- The density limit at each Lebesgue point, for every positive threshold. -/
theorem at_lebesguePoint : Specs.D11.Ch13.ApproximateContinuity.at_lebesguePoint := by
  intro n _ 𝕜 _ _ _ f hf x hx ε hε
  change locallyIntegrable f at hf
  change lebesguePoint f hf x at hx
  have hlim : Tendsto (fun r => ε⁻¹ * oscillationAverage f hf r x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hx.const_mul ε⁻¹
  apply squeeze_zero' (Eventually.of_forall (fun r => div_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) _ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact density_le_oscillation f hf x hε hr

/-- Lebesgue differentiation supplies one exceptional set for all thresholds. -/
theorem approximate_continuity_ae :
    Specs.D11.Ch13.ApproximateContinuity.approximate_continuity_ae := by
  intro n _ 𝕜 _ _ _ f hf
  obtain ⟨N, hN, hnull, hpoint⟩ :=
    LebesgueDifferentiation.lebesgue_differentiation.{0} f hf
  refine ⟨N, hN, hnull, ?_⟩
  intro x hx
  exact at_lebesguePoint f hf x (hpoint x hx).1

end D11.Ch13.ApproximateContinuity
