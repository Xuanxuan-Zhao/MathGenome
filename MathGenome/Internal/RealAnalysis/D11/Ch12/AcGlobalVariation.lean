import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcGlobalVariation
import MathGenome.Internal.RealAnalysis.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcBasic

/-! Initial partition variation preserves uniform global absolute continuity.
No differentiation or density representation is used. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace D11.Ch12.AcGlobalVariation
open ScalarStieltjesCorrespondence

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Refine all intervals simultaneously, using half the requested error. -/
theorem variation_ac (F : ℝ → 𝕂) (hF : NBV F)
    (hAC : D11.Ch12.AbsolutelyContinuous F) :
    D11.Ch12.AbsolutelyContinuous (fun x => (initialVariation F x).toReal) := by
  have hfinite (u v : ℝ) : variation F u v ≠ ⊤ := by
    rw [variation_eq_eVariationOn]
    exact hF.boundedVariationOn.mono (subset_univ _)
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hAC (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro n u v huv hmem hdis hlen
  have hvar := AcBasic.sum_variation_le hd (inferInstance : OrdConnected (univ : Set ℝ))
    u v huv hmem hdis hlen
  have hincr (i : Fin n) :
      ‖(initialVariation F (v i)).toReal - (initialVariation F (u i)).toReal‖ =
        (variation F (u i) (v i)).toReal := by
    rw [initialVariation_add (huv i).le, ← variation_eq_eVariationOn,
      ENNReal.toReal_add (initialVariation_finite hF.1 (u i)).ne (hfinite _ _),
      add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hincr]
  rw [← ENNReal.toReal_sum (fun i _ => hfinite (u i) (v i))]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
  rw [ENNReal.toReal_ofReal (half_pos hε).le] at hh
  exact hh.trans_lt (half_lt_self hε)

/-- The accepted partition variation equals the cumulative positive variation
measure pointwise, including the normalization at minus infinity. -/
lemma initialVariation_eq_cumulative (F : ℝ → 𝕂) (hF : NBV F) :
    (fun x => (initialVariation F x).toReal) =
      PositiveStieltjes.cumulative (stieltjesMeasure F).variation := by
  funext x
  exact congrArg ENNReal.toReal (NormalizedStieltjes.variation_initial F hF x).symm

/-- Finite global BV and normalization establish every generator condition. -/
theorem positiveGenerator (F : ℝ → 𝕂) (hF : NBV F) :
    PositiveStieltjes.PositiveGenerator (fun x => (initialVariation F x).toReal) := by
  rw [initialVariation_eq_cumulative F hF]
  exact PositiveStieltjes.cumulative_properties _ (measure_finite F hF)

/-- Exact equality on all Borel sets, proved without assuming measure AC. -/
theorem stieltjesMeasure_eq (F : ℝ → 𝕂) (hF : NBV F)
    (hV : PositiveStieltjes.PositiveGenerator (fun x => (initialVariation F x).toReal)) :
    (stieltjesMeasure F).variation =
      PositiveStieltjes.stieltjesMeasure (fun x => (initialVariation F x).toReal) hV := by
  have heq := initialVariation_eq_cumulative F hF
  have hcum : PositiveStieltjes.PositiveGenerator
      (PositiveStieltjes.cumulative (stieltjesMeasure F).variation) := heq ▸ hV
  simpa only [← heq] using
    (PositiveStieltjes.stieltjesMeasure_cumulative _ (measure_finite F hF) hcum).symm

/-- Uniform global AC together with the constructed generator and exact measure
identification, from NBV and AC alone. -/
theorem global_variation (F : ℝ → 𝕂) (hF : NBV F)
    (hAC : D11.Ch12.AbsolutelyContinuous F) :
    D11.Ch12.AbsolutelyContinuous (fun x => (initialVariation F x).toReal) ∧
    ∃ hV : PositiveStieltjes.PositiveGenerator (fun x => (initialVariation F x).toReal),
      (stieltjesMeasure F).variation =
        PositiveStieltjes.stieltjesMeasure (fun x => (initialVariation F x).toReal) hV :=
  ⟨variation_ac F hF hAC, positiveGenerator F hF,
    stieltjesMeasure_eq F hF (positiveGenerator F hF)⟩

end D11.Ch12.AcGlobalVariation
