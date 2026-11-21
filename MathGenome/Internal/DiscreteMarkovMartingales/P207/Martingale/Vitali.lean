import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UISmallSets
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.Vitali
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

universe u v

namespace P207.Martingale

variable {Ω : Type u} {E : Type v} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E]

/-- Vitali convergence, including construction of a strongly measurable
integrable representative on the original, possibly incomplete, measure space. -/
theorem vitali_forward (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ n, Integrable (X n) μ)
    (hprob : TendstoInMeasure μ X atTop Y)
    (hui : SourceUniformIntegrable μ X) :
    Integrable Y μ ∧
      (∃ Z : Ω → E, StronglyMeasurable Z ∧ Integrable Z μ ∧ Y =ᵐ[μ] Z) ∧
      Tendsto (fun n => ∫ x, ‖X n x - Y x‖ ∂μ) atTop (𝓝 0) := by
  have hu := (sourceUniformIntegrable_iff_uniformIntegrable μ X).mp hui
  have hY : Integrable Y μ := hu.integrable_of_tendstoInMeasure hprob
  have hm := hY.aestronglyMeasurable
  refine ⟨hY, ⟨hm.mk Y, hm.stronglyMeasurable_mk, hY.congr hm.ae_eq_mk,
    hm.ae_eq_mk⟩, ?_⟩
  have ht := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (hX n).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hY) hu.1 hprob
  have heq (n : ℕ) : eLpNorm (X n - Y) 1 μ =
      ENNReal.ofReal (∫ x, ‖X n x - Y x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hX n).sub hY).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hX n).sub hY)]
    rfl
  have ht' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simpa only [Function.comp_def, heq, ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _)),
    ENNReal.toReal_zero] using ht'

/-- L¹ convergence implies convergence in probability and source-tail uniform
integrability of the entire sequence, including its finitely many early terms. -/
theorem vitali_converse (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ n, Integrable (X n) μ) (hY : Integrable Y μ)
    (hL1 : Tendsto (fun n => ∫ x, ‖X n x - Y x‖ ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop Y ∧ SourceUniformIntegrable μ X := by
  have heq (n : ℕ) : eLpNorm (X n - Y) 1 μ =
      ENNReal.ofReal (∫ x, ‖X n x - Y x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hX n).sub hY).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hX n).sub hY)]
    rfl
  have ht : Tendsto (fun n => eLpNorm (X n - Y) 1 μ) atTop (𝓝 0) := by
    simpa only [heq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hL1
  refine ⟨tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ht,
    (sourceUniformIntegrable_iff_uniformIntegrable μ X).mpr ?_⟩
  refine ⟨unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top
    (fun n => memLp_one_iff_integrable.mpr (hX n))
    (memLp_one_iff_integrable.mpr hY) ht, ?_⟩
  obtain ⟨C, hC⟩ := hL1.bddAbove_range
  let B : ℝ≥0 := ⟨max (C + ∫ x, ‖Y x‖ ∂μ) 0, le_max_right _ _⟩
  refine ⟨B, fun n => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm (hX n).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (hX n)]
  apply ENNReal.ofReal_le_coe.mpr
  calc
    (∫ x, ‖X n x‖ ∂μ) ≤ ∫ x, ‖X n x - Y x‖ + ‖Y x‖ ∂μ :=
      integral_mono (hX n).norm (((hX n).sub hY).norm.add hY.norm)
        (fun x => norm_le_norm_sub_add (X n x) (Y x))
    _ = (∫ x, ‖X n x - Y x‖ ∂μ) + ∫ x, ‖Y x‖ ∂μ :=
      integral_add ((hX n).sub hY).norm hY.norm
    _ ≤ C + ∫ x, ‖Y x‖ ∂μ := add_le_add (hC (Set.mem_range_self n)) le_rfl
    _ ≤ B := le_max_left _ _

end P207.Martingale
