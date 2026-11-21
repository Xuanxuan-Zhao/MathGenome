import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.ElementaryNormInterpolation
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch10.ElementaryNormInterpolation

-- Hölder applied to |f|^θ and |f|^(1-θ), with exponents p/θ and
-- r/(1-θ), treats the finite and infinite upper endpoint uniformly.
theorem eLpNorm_interpolation {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q r : ℝ≥0∞) (θ : ℝ) (f : X → 𝕜)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (heq : q⁻¹ = ENNReal.ofReal θ / p + ENNReal.ofReal (1 - θ) / r)
    (hf : Measurable f) :
    eLpNorm f q μ ≤ eLpNorm f p μ ^ θ * eLpNorm f r μ ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := sub_pos.mpr hθ1
  have hθ0 : ENNReal.ofReal θ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hθ
  have hθ0' : ENNReal.ofReal (1 - θ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hθ'
  have : ENNReal.HolderTriple (p / ENNReal.ofReal θ)
      (r / ENNReal.ofReal (1 - θ)) q := ⟨by
    rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hθ0),
      ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hθ0')]
    exact heq.symm⟩
  have hfm := hf.stronglyMeasurable.aestronglyMeasurable (μ := μ)
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal
    (p := p / ENNReal.ofReal θ) (q := r / ENNReal.ofReal (1 - θ)) (r := q)
    (f := fun x => ‖f x‖ₑ ^ θ) (g := fun x => ‖f x‖ₑ ^ (1 - θ))
    (by fun_prop) (by fun_prop)
  rw [eLpNorm_enorm_rpow f hfm hθ, eLpNorm_enorm_rpow f hfm hθ'] at h
  have hp : p / ENNReal.ofReal θ * ENNReal.ofReal θ = p := by
    exact ENNReal.div_mul_cancel hθ0 ENNReal.ofReal_ne_top
  have hr : r / ENNReal.ofReal (1 - θ) * ENNReal.ofReal (1 - θ) = r := by
    exact ENNReal.div_mul_cancel hθ0' ENNReal.ofReal_ne_top
  rw [hp, hr] at h
  have hfg : (fun x => ‖f x‖ₑ ^ θ) * (fun x => ‖f x‖ₑ ^ (1 - θ)) =
      fun x => ‖f x‖ₑ := by
    funext x
    change ‖f x‖ₑ ^ θ * ‖f x‖ₑ ^ (1 - θ) = ‖f x‖ₑ
    rw [← ENNReal.rpow_add_of_nonneg θ (1 - θ) hθ.le hθ'.le]
    simp
  rw [hfg, eLpNorm_enorm f hfm] at h
  exact h

open Specs.D11.Ch10.QuotientConstruction

/-- The canonical source norm agrees with the native norm for every ordinary
measurable scalar function, including when its value is infinite. -/
theorem sourceNorm_eq_eLpNorm {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → 𝕜) (hp : 1 ≤ p)
    (hf : Measurable f) : sourceNorm μ p f = eLpNorm f p μ := by
  unfold sourceNorm
  split_ifs with h
  · subst p
    exact LpDefinition.essentialSupNorm_eq_eLpNorm μ f hf
  · have hr : 1 ≤ p.toReal := by
      exact_mod_cast (ENNReal.toReal_le_toReal ENNReal.one_ne_top h).mpr hp
    have heq := LpDefinition.powerNorm_eq_eLpNorm μ p.toReal f hr hf
    simpa only [ENNReal.ofReal_toReal h] using heq

/-- Elementary norm interpolation for measurable scalar representatives, with
the shared source norms and the full infinite-upper-endpoint range. -/
theorem elementary_norm_interpolation :
    Specs.D11.Ch10.ElementaryNormInterpolation.elementary_norm_interpolation := by
  intro X 𝕜 _ _ _ _ μ p q r θ f hp hpq hqr hθ hθ1 heq hf hfp hfr
  have hq : 1 ≤ q := hp.trans hpq.le
  have hr : 1 ≤ r := hq.trans hqr.le
  rw [sourceNorm_eq_eLpNorm μ p f hp hf] at hfp
  rw [sourceNorm_eq_eLpNorm μ r f hr hf] at hfr
  have h := eLpNorm_interpolation μ p q r θ f hθ hθ1 heq hf
  have hfinite : eLpNorm f q μ < ∞ := by
    refine h.trans_lt (ENNReal.mul_lt_top ?_ ?_)
    · exact ENNReal.rpow_lt_top_of_nonneg hθ.le hfp.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (sub_pos.mpr hθ1).le hfr.ne
  refine ⟨⟨hf, hfinite⟩, ?_⟩
  simpa only [sourceNorm_eq_eLpNorm μ q f hq hf,
    sourceNorm_eq_eLpNorm μ p f hp hf, sourceNorm_eq_eLpNorm μ r f hr hf] using h

end D11.Ch10.ElementaryNormInterpolation
