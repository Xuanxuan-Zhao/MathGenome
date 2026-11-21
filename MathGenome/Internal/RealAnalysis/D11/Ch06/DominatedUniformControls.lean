import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.DominatedUniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch06.AbsoluteContinuityTails
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominationInvariance

/-! Domination supplies both uniform integral controls, paper.tex:2071–2085.
For each measurable set, a.e. monotonicity bounds every sequence integral
by the same integral of g, hence bounds its supremum. Apply the previously
proved small-set and finite-measure-tail estimates to g; their witnesses
depend on g and ε, and work for the whole sequence. No Vitali or dominated
convergence theorem is used.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch06.DominatedUniformControls

open D11.Ch05.NonnegativeIntegral
open D11.Ch04.AeCommonException

theorem dominated_integrable :
    Specs.D11.Ch06.DominatedUniformControls.dominated_integrable.{u} := by
  intro X 𝕜 _ _ _ _ μ f g hfm hg hg0 hfg n
  exact (DominationInvariance.integrable_domination μ (f n) g (hfm n) hg hg0 (hfg n)).1

theorem uniform_set_bound :
    Specs.D11.Ch06.DominatedUniformControls.uniform_set_bound.{u} := by
  intro X 𝕜 _ _ _ _ μ f g _hfm _hg _hg0 hfg E _hE
  refine iSup_le fun n => ?_
  change nonnegativeIntegral μ (E.indicator (fun x => ENNReal.ofReal ‖f n x‖)) ≤
    nonnegativeIntegral μ (E.indicator (fun x => ENNReal.ofReal (g x)))
  simp only [integral_eq_lintegral]
  apply lintegral_mono_ae
  apply ((almostEverywhere_iff_native μ _).mp (hfg n)).mono
  intro x hx
  by_cases hxE : x ∈ E
  · simpa only [indicator_of_mem hxE] using ENNReal.ofReal_le_ofReal hx
  · simp only [indicator_of_notMem hxE, le_refl]

theorem uniform_compl_bound :
    Specs.D11.Ch06.DominatedUniformControls.uniform_compl_bound.{u} := by
  intro X 𝕜 _ _ _ _ μ f g hfm hg hg0 hfg A hA
  exact uniform_set_bound μ f g hfm hg hg0 hfg Aᶜ hA.compl

theorem uniform_small_sets :
    Specs.D11.Ch06.DominatedUniformControls.uniform_small_sets.{u} := by
  intro X 𝕜 _ _ _ _ μ f g hfm hg hg0 hfg ε hε
  obtain ⟨δ, hδ, hsmall⟩ := AbsoluteContinuityTails.small_sets μ g hg ε hε
  refine ⟨δ, hδ, fun E hE hmass => ?_⟩
  have hgnorm : (fun x => ENNReal.ofReal ‖g x‖) =
      (fun x => ENNReal.ofReal (g x)) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
  have hsmallg := hsmall E hE hmass
  rw [hgnorm] at hsmallg
  exact (uniform_set_bound μ f g hfm hg hg0 hfg E hE).trans_lt hsmallg

theorem uniform_finite_measure_tail :
    Specs.D11.Ch06.DominatedUniformControls.uniform_finite_measure_tail.{u} := by
  intro X 𝕜 _ _ _ _ μ f g hfm hg hg0 hfg ε hε
  obtain ⟨A, hA, hmass, htail⟩ :=
    AbsoluteContinuityTails.finite_measure_tail μ g hg ε hε
  refine ⟨A, hA, hmass, ?_⟩
  have hgnorm : (fun x => ENNReal.ofReal ‖g x‖) =
      (fun x => ENNReal.ofReal (g x)) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
  rw [hgnorm] at htail
  exact (uniform_compl_bound μ f g hfm hg hg0 hfg A hA).trans_lt htail

end D11.Ch06.DominatedUniformControls
