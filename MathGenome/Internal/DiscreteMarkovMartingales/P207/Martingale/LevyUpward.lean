import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.LevyUpward
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.FixedInputConditionalUI
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.LpConvergence

/-! Lévy's upward theorem, paper.tex §6.7 (W36).

Mathlib's upward theorem identifies the limit by the test-event identity on
the increasing union and the pi-lambda theorem. It already permits an input
which is not terminal-measurable. For higher moments, conditional contraction
gives the common Lp bound needed for martingale convergence. Uniqueness of
almost-sure limits identifies that theorem's representative with the terminal
conditional expectation as well.
-/

open MeasureTheory Filter
open scoped MeasureTheory Topology NNReal

universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Conditional expectations along an increasing filtration converge almost
surely and in mean to the conditional expectation on its generated sigma algebra. -/
theorem levy_upward (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : Ω → ℝ) (_hY : Integrable Y μ) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => μ[Y | ℱ n] ω) atTop
      (𝓝 (μ[Y | terminalSigma ℱ] ω))) ∧
    Tendsto (fun n => ∫ ω, ‖μ[Y | ℱ n] ω - μ[Y | terminalSigma ℱ] ω‖ ∂μ)
      atTop (𝓝 0) := by
  refine ⟨MeasureTheory.tendsto_ae_condExp (ℱ := ℱ) Y, ?_⟩
  have ht := MeasureTheory.tendsto_eLpNorm_condExp (μ := μ) (ℱ := ℱ) Y
  have heq (n : ℕ) :
      eLpNorm (μ[Y | ℱ n] - μ[Y | terminalSigma ℱ]) 1 μ =
        ENNReal.ofReal (∫ ω, ‖μ[Y | ℱ n] ω - μ[Y | terminalSigma ℱ] ω‖ ∂μ) := by
    have hi : Integrable (μ[Y | ℱ n] - μ[Y | terminalSigma ℱ]) μ :=
      integrable_condExp.sub integrable_condExp
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    rfl
  have ht' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simpa only [Function.comp_def, show (⨆ n, ℱ n) = terminalSigma ℱ from rfl,
    heq, ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _)),
    ENNReal.toReal_zero] using ht'

/-- For every finite real exponent greater than one the same identified limit
also gives convergence in Lp. -/
theorem levy_upward_lp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : Ω → ℝ) (p : ℝ) (hp : 1 < p)
    (hY : MemLp Y (ENNReal.ofReal p) μ) :
    MemLp (μ[Y | terminalSigma ℱ]) (ENNReal.ofReal p) μ ∧
    Tendsto (fun n => eLpNorm (μ[Y | ℱ n] - μ[Y | terminalSigma ℱ])
      (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp' : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hYi : Integrable Y μ := hY.integrable hp'
  have hM := (Martingale.conditional_expectation_ui_martingale μ ℱ Y hYi).1
  let R : ℝ≥0 := (eLpNorm Y (ENNReal.ofReal p) μ).toNNReal
  have hR : ∀ n, eLpNorm (μ[Y | ℱ n]) (ENNReal.ofReal p) μ ≤ R := by
    intro n
    simpa only [R, ENNReal.coe_toNNReal hY.eLpNorm_ne_top] using
      (eLpNorm_condExp_le_eLpNorm (m := ℱ n) (μ := μ) Y hp')
  have hterm := lp_martingale_convergence_of_eLpNorm_bdd μ ℱ
    (fun n => μ[Y | ℱ n]) hM p hp R hR
  have heq : ℱ.limitProcess (fun n => μ[Y | ℱ n]) μ =ᵐ[μ]
      μ[Y | terminalSigma ℱ] := by
    filter_upwards [hterm.2.2.1, (levy_upward μ ℱ Y hYi).1] with ω h₁ h₂
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨hY.condExp hp', ?_⟩
  apply hterm.2.2.2.1.congr
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [heq] with ω hω
  simp only [Pi.sub_apply, hω]

end P207
