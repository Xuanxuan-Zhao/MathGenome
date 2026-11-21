import MathGenome.Internal.RealAnalysis.D11.Ch13.LebesgueDifferentiation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.DensityPoints

/-! Density points for arbitrary completed-Lebesgue-measurable sets.
Apply local differentiation to the indicator, which is integrable on
every compact set even when the set has infinite total measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace D11.Ch13.DensityPoints
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch13.AveragesMaximalDefinition

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace n
variable {n : ℕ} [NeZero n]

lemma locallyIntegrable_indicator (E : Set (Point n)) (hE : MeasurableSet E) :
    locallyIntegrable (E.indicator (fun _ => (1 : ℝ))) := by
  apply (locallyIntegrable_iff _).mpr
  refine ⟨measurable_const.indicator hE, fun K hK => ?_⟩
  exact (integrableOn_const (C := (1 : ℝ)) (hK.measure_ne_top (μ := lebesgue n))).indicator hE

lemma average_indicator (E : Set (Point n)) (hE : MeasurableSet E)
    (r : ℝ) (x : Point n) :
    average (E.indicator (fun _ => (1 : ℝ))) (locallyIntegrable_indicator E hE) r x =
      (lebesgue n (E ∩ Metric.ball x r)).toReal /
        (lebesgue n (Metric.ball x r)).toReal := by
  rw [average_formula, setIntegral_indicator hE, integral_const]
  simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
  rw [Set.inter_comm (Metric.ball x r) E, div_eq_mul_inv, mul_comm]

theorem density_points : Specs.D11.Ch13.DensityPoints.density_points := by
  intro n _ E hE
  have hf := locallyIntegrable_indicator E hE
  obtain ⟨N, hN, hnull, hdiff⟩ :=
    D11.Ch13.LebesgueDifferentiation.lebesgue_differentiation.{0}
      (E.indicator (fun _ => (1 : ℝ))) hf
  refine ⟨N, hN, hnull, ?_⟩
  intro x hx
  have ht := (hdiff x hx).2.1
  change Tendsto (fun r => average (E.indicator (fun _ => (1 : ℝ))) hf r x)
    (𝓝[>] (0 : ℝ)) (𝓝 (E.indicator (fun _ => (1 : ℝ)) x)) at ht
  simp_rw [average_indicator E hE] at ht
  constructor
  · intro hxin
    rw [Set.indicator_of_mem hxin] at ht
    exact ht
  · intro hxout
    rw [Set.indicator_of_notMem hxout] at ht
    exact ht

end D11.Ch13.DensityPoints
