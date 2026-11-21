import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UniformIntegrability
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UIMartingaleClosure
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Terminal closure of a source-UI real martingale. We fix `ℱ.limitProcess M μ`
as the terminal representative, including for subsequent Lp and stopping results. -/
theorem ui_martingale_terminal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ)
    (hM : IsMartingale M ℱ μ) (hui : Martingale.SourceUniformIntegrable μ M) :
    Measurable[terminalSigma ℱ] (ℱ.limitProcess M μ) ∧
      Integrable (ℱ.limitProcess M μ) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (ℱ.limitProcess M μ ω))) ∧
      Tendsto (fun n => ∫ ω, ‖M n ω - ℱ.limitProcess M μ ω‖ ∂μ) atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[ℱ.limitProcess M μ | ℱ n] := by
  have hm := (martingale_iff_library μ ℱ M).mp hM
  have hu := (Martingale.sourceUniformIntegrable_iff_uniformIntegrable μ M).mp hui
  obtain ⟨C, hC⟩ := hu.2
  have hi : Integrable (ℱ.limitProcess M μ) μ :=
    memLp_one_iff_integrable.mp (hm.submartingale.memLp_limitProcess hC)
  refine ⟨ℱ.stronglyMeasurable_limitProcess.measurable, hi,
    hm.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hu, ?_,
    hm.ae_eq_condExp_limitProcess hu⟩
  have ht := hm.submartingale.tendsto_eLpNorm_one_limitProcess hu
  have heq (n : ℕ) : eLpNorm (M n - ℱ.limitProcess M μ) 1 μ =
      ENNReal.ofReal (∫ ω, ‖M n ω - ℱ.limitProcess M μ ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hM.2.1 n).sub hi).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hM.2.1 n).sub hi)]
    rfl
  have ht' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simpa only [Function.comp_def, heq,
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _)),
    ENNReal.toReal_zero] using ht'

/-- The existential formulation of terminal closure in §6.5. -/
theorem exists_ui_martingale_terminal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ)
    (hM : IsMartingale M ℱ μ) (hui : Martingale.SourceUniformIntegrable μ M) :
    ∃ Y : Ω → ℝ, Measurable[terminalSigma ℱ] Y ∧ Integrable Y μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => ∫ ω, ‖M n ω - Y ω‖ ∂μ) atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[Y | ℱ n] :=
  ⟨ℱ.limitProcess M μ, ui_martingale_terminal μ ℱ M hM hui⟩

/-- Alternative terminal choices agree almost surely with the fixed representative. -/
theorem ui_martingale_terminal_unique (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ)
    (hM : IsMartingale M ℱ μ) (hui : Martingale.SourceUniformIntegrable μ M)
    (Y : Ω → ℝ)
    (hY : ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (Y ω))) :
    Y =ᵐ[μ] ℱ.limitProcess M μ := by
  filter_upwards [hY, (ui_martingale_terminal μ ℱ M hM hui).2.2.1] with ω hy hm
  exact tendsto_nhds_unique hy hm

end P207
