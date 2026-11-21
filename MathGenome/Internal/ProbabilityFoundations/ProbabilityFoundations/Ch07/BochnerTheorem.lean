import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.BochnerTheorem
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.BochnerGaussianRegularization
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.LevyContinuity
import Mathlib.Analysis.SpecificLimits.Basic

/-! Bochner's theorem, `paper.tex:2642–2686`. Gaussian regularization
provides actual probability laws. Their transforms converge pointwise to
the prescribed function, and Lévy's continuity theorem gives existence
and uniqueness without an integrability assumption on that function. -/

noncomputable section
open MeasureTheory Filter Topology

namespace ProbabilityFoundations.Ch07

/-- The normalized Euclidean Bochner theorem, including dimension zero. -/
theorem bochner : Specs.ProbabilityFoundations.Ch07.BochnerTheorem.Bochner := by
  intro d φ hc hp hzero
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hreg (n : ℕ) := gaussian_regularization φ hc hp hzero (ε n) (hε n)
  have hprob (n : ℕ) : IsProbabilityMeasure (regularizedMeasure φ (ε n)) :=
    (hreg n).2.2.2.2.2.2.2.2.1
  let μs : ℕ → ProbabilityMeasure (Euclidean d) :=
    fun n => ⟨regularizedMeasure φ (ε n), hprob n⟩
  have htransform (n : ℕ) (t : Euclidean d) :
      characteristicFunction (μs n) t = regularizedTransform φ (ε n) t :=
    (hreg n).2.2.2.2.2.2.2.2.2 t
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim (t : Euclidean d) :
      Tendsto (fun n => characteristicFunction (μs n) t) atTop (𝓝 (φ t)) := by
    simp_rw [htransform, regularizedTransform]
    have hexp : Tendsto (fun n => Real.exp (-ε n * ‖t‖ ^ 2 / 2)) atTop (𝓝 1) := by
      have harg : Tendsto (fun n => -ε n * ‖t‖ ^ 2 / 2) atTop (𝓝 0) := by
        simpa using (hεlim.neg.mul_const (‖t‖ ^ 2)).div_const 2
      simpa only [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.tendsto 0).comp harg
    simpa using tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto 1 |>.comp hexp)
  obtain ⟨μ, hμ, _, huniq⟩ := levy_continuity μs φ hlim hc.continuousAt
  exact ⟨μ, hμ, huniq⟩

end ProbabilityFoundations.Ch07
