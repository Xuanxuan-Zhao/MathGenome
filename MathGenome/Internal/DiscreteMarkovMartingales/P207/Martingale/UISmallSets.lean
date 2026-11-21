import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UniformIntegrability
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UISmallSets

open MeasureTheory
open scoped NNReal ENNReal

universe u v w

namespace P207.Martingale

variable {Ω : Type u} {E : Type v} {I : Type w}
  [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- On a measurable event, the extended L¹ norm equals the nonnegative
Bochner norm expectation. No measurable structure on the codomain is needed. -/
private theorem event_eLpNorm_eq (μ : Measure Ω) (f : Ω → E)
    (hf : Integrable f μ) (A : Set Ω) (hA : MeasurableSet A) :
    eLpNorm f 1 (μ.restrict A) =
      ENNReal.ofReal (∫ x, A.indicator (fun x => ‖f x‖) x ∂μ) := by
  rw [integral_indicator hA, ofReal_integral_norm_eq_lintegral_enorm hf.restrict,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable.restrict]

/-- The small-set criterion, with strict real ε and δ, for arbitrary indexed
families of integrable normed-group-valued functions. In particular this applies
to real or complex Banach-valued families on every probability space. -/
theorem sourceUniformIntegrable_iff_smallSets
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E)
    (hX : ∀ i, Integrable (X i) μ) :
    SourceUniformIntegrable μ X ↔
      (∃ C : ℝ≥0, ∀ i, (∫ x, ‖X i x‖ ∂μ) ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (i : I) (A : Set Ω), MeasurableSet A → μ A < ENNReal.ofReal δ →
          (∫ x, A.indicator (fun x => ‖X i x‖) x ∂μ) < ε := by
  constructor
  · intro h
    refine ⟨sourceUniformIntegrable_bounded μ X h, ?_⟩
    intro ε hε
    have hu := ((sourceUniformIntegrable_iff_uniformIntegrable μ X).mp h).1
    obtain ⟨d, hd, hsmall⟩ := unifIntegrable_iff'.mp hu
      (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
    obtain ⟨δ, _, hδ, hδd⟩ := ENNReal.lt_iff_exists_real_btwn.mp hd
    refine ⟨δ, ENNReal.ofReal_pos.mp hδ, fun i A hA hμA => ?_⟩
    apply (ENNReal.ofReal_lt_ofReal_iff hε).mp
    calc
      ENNReal.ofReal (∫ x, A.indicator (fun x => ‖X i x‖) x ∂μ) =
          eLpNorm (X i) 1 (μ.restrict A) := (event_eLpNorm_eq μ (X i) (hX i) A hA).symm
      _ ≤ ENNReal.ofReal (ε / 2) := hsmall i A hA (hμA.trans hδd).le
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)
  · rintro ⟨⟨C, hC⟩, hsmall⟩
    apply (sourceUniformIntegrable_iff_uniformIntegrable μ X).mpr
    refine ⟨unifIntegrable_iff'.mpr ?_, C, fun i => ?_⟩
    · intro ε hε
      obtain ⟨e, _, he, heε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
      obtain ⟨δ, hδ, hd⟩ := hsmall e (ENNReal.ofReal_pos.mp he)
      refine ⟨ENNReal.ofReal (δ / 2), ENNReal.ofReal_pos.mpr (half_pos hδ),
        fun i A hA hμA => ?_⟩
      have hμA' : μ A < ENNReal.ofReal δ := hμA.trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ))
      rw [event_eLpNorm_eq μ (X i) (hX i) A hA]
      exact ((ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp he)).mpr
        (hd i A hA hμA')).le.trans heε.le
    · rw [eLpNorm_one_eq_lintegral_enorm (hX i).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hX i)]
      exact ENNReal.ofReal_le_coe.mpr (hC i)

end P207.Martingale
