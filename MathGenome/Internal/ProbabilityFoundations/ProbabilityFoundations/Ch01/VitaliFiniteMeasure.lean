import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.VitaliFiniteMeasure
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.UniformIntegrabilitySmallSets

/-! Vitali convergence for the source's strict-tail definition. The reverse
implication first derives integrability of the limit, then applies the Lp
convergence theorem at exponent one. -/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace ProbabilityFoundations.Ch01

variable {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]

/-- Reindexing by the range neither loses nor adds members of a sequence. -/
private theorem uniformIntegrable_range_iff (μ : Measure S) (F : ℕ → S → E) :
    UniformIntegrable (fun g : Set.range F => (g : S → E)) 1 μ ↔
      UniformIntegrable F 1 μ := by
  classical
  constructor
  · rintro ⟨h, C, hC⟩
    let j : ℕ → Set.range F := fun n => ⟨F n, Set.mem_range_self n⟩
    have hj : UnifIntegrable F 1 μ := h.comp j
    exact ⟨hj, C, fun n => hC (j n)⟩
  · rintro ⟨h, C, hC⟩
    let k : Set.range F → ℕ := fun g => Classical.choose g.property
    have hk (g : Set.range F) : F (k g) = (g : S → E) :=
      Classical.choose_spec g.property
    have heq : F ∘ k = (fun g : Set.range F => (g : S → E)) := funext hk
    refine ⟨heq ▸ h.comp k, C, fun g => ?_⟩
    change eLpNorm (g : S → E) 1 μ ≤ C
    rw [← hk g]
    exact hC (k g)

private theorem eLpNorm_one_eq_ofReal_integral_norm (μ : Measure S) (g : S → E)
    (hg : Integrable g μ) :
    eLpNorm g 1 μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
    ofReal_integral_norm_eq_lintegral_enorm hg]

/-- The source's L¹ convergence criterion, without assuming an integrable limit. -/
theorem vitali_finite_measure :
    Specs.ProbabilityFoundations.Ch01.VitaliFiniteMeasure.vitaliFiniteMeasureType := by
  intro S E mS nE mE bE sE μ finite F f hF _hf
  change (Integrable f μ ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0)) ↔
    (ConvergesInMeasure μ F f ∧ SourceUniformIntegrable μ (Set.range F))
  rw [convergesInMeasure_iff_tendstoInMeasure,
    sourceUniformIntegrable_iff_uniformIntegrable, uniformIntegrable_range_iff]
  constructor
  · rintro ⟨hf, hconv⟩
    have hLp : Tendsto (fun n => eLpNorm (F n - f) 1 μ) atTop (𝓝 0) := by
      simpa only [eLpNorm_one_eq_ofReal_integral_norm μ _ ((hF _).sub hf),
        Pi.sub_apply, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hconv
    refine ⟨tendstoInMeasure_of_tendsto_eLpNorm (by simp) hLp, ?_, ?_⟩
    · exact unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top
        (fun n => memLp_one_iff_integrable.mpr (hF n))
        (memLp_one_iff_integrable.mpr hf) hLp
    · obtain ⟨C, hC⟩ := hconv.bddAbove_range
      refine ⟨Real.toNNReal (C + ∫ x, ‖f x‖ ∂μ), fun n => ?_⟩
      rw [eLpNorm_one_eq_ofReal_integral_norm μ _ (hF n)]
      change ENNReal.ofReal (∫ x, ‖F n x‖ ∂μ) ≤
        ENNReal.ofReal (C + ∫ x, ‖f x‖ ∂μ)
      apply ENNReal.ofReal_le_ofReal
      calc
        (∫ x, ‖F n x‖ ∂μ) ≤ ∫ x, ‖F n x - f x‖ + ‖f x‖ ∂μ := by
          apply integral_mono (hF n).norm (((hF n).sub hf).norm.add hf.norm)
          intro x
          exact norm_le_norm_sub_add (F n x) (f x)
        _ = (∫ x, ‖F n x - f x‖ ∂μ) + ∫ x, ‖f x‖ ∂μ :=
          integral_add ((hF n).sub hf).norm hf.norm
        _ ≤ C + ∫ x, ‖f x‖ ∂μ := add_le_add (hC (Set.mem_range_self n)) le_rfl
  · rintro ⟨hmeasure, hui⟩
    have hf : Integrable f μ := hui.integrable_of_tendstoInMeasure hmeasure
    refine ⟨hf, ?_⟩
    have hLp := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      (fun n => (hF n).aestronglyMeasurable)
      (memLp_one_iff_integrable.mpr hf) hui.1 hmeasure
    have hreal := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp hLp
    simpa only [eLpNorm_one_eq_ofReal_integral_norm μ _ ((hF _).sub hf),
      Function.comp_def, Pi.sub_apply, ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _)),
      ENNReal.toReal_zero] using hreal

end ProbabilityFoundations.Ch01
