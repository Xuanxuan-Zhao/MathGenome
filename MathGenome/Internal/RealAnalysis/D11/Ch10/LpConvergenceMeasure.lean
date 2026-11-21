import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpConvergenceMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace D11.Ch10.LpConvergenceMeasure
open Specs.D11.Ch10.QuotientConstruction
open D11.Ch07.ConvergenceDefinitions
open D11.Ch04.EssentialBounds D11.Ch04.AeCommonException

private theorem powerNorm_tendsto_iff {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (p : ℝ) (hp : 0 < p)
    (f : ℕ → X → 𝕜) :
    Tendsto (fun n => D11.Ch10.LpDefinition.powerNorm μ p (f n)) atTop (𝓝 0) ↔
      Tendsto (fun n => powerIntegral μ p (f n)) atTop (𝓝 0) := by
  constructor
  · intro h
    have h' := h.ennrpow_const p
    simpa only [D11.Ch10.LpDefinition.powerNorm, powerIntegral, one_div,
      ENNReal.rpow_inv_rpow hp.ne', ENNReal.zero_rpow_of_pos hp] using h'
  · intro h
    have h' := h.ennrpow_const (1 / p)
    simpa only [D11.Ch10.LpDefinition.powerNorm, powerIntegral,
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using h'

theorem finite_norm_iff_representative :
    Specs.D11.Ch10.LpConvergenceMeasure.finite_norm_iff_representative := by
  intro X 𝕜 _ _ _ _ μ p hp f g
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp⟩
  have hg := (D11.Ch10.LpDefinition.rawLp_iff_memLp μ p g.val hp).mpr g.property
  have hf := fun n =>
    (D11.Ch10.LpDefinition.rawLp_iff_memLp μ p (f n).val hp).mpr (f n).property
  have hg' := (D11.Ch10.LpDefinition.rawLp_iff_finite_integral μ p g.val hp).mp hg
  have hf' := fun n =>
    (D11.Ch10.LpDefinition.rawLp_iff_finite_integral μ p (f n).val hp).mp (hf n)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (f n).val)
    (fun n => (f n).property.2) g.val g.property.2]
  have heq : (fun n => eLpNorm ((f n).val - g.val) (ENNReal.ofReal p) μ) =
      (fun n => D11.Ch10.LpDefinition.powerNorm μ p ((f n).val - g.val)) := by
    funext n
    exact (D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm μ p _ hp
      ((f n).property.1.sub g.property.1)).symm
  rw [heq, powerNorm_tendsto_iff μ p (lt_of_lt_of_le zero_lt_one hp)]
  change _ ↔ 1 ≤ p ∧ _ ∧ _ ∧ _
  exact ⟨fun h => ⟨hp, hg', hf', h⟩, fun h => h.2.2.2⟩

theorem infinity_norm_iff_representative :
    Specs.D11.Ch10.LpConvergenceMeasure.infinity_norm_iff_representative := by
  intro X 𝕜 _ _ _ _ μ f g
  have hg := (D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ g.val).mpr g.property
  have hf := fun n =>
    (D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ (f n).val).mpr (f n).property
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (f n).val)
    (fun n => (f n).property.2) g.val g.property.2]
  have heq : (fun n => eLpNorm ((f n).val - g.val) ∞ μ) =
      (fun n => essentialSupNorm μ ((f n).val - g.val)) := by
    funext n
    exact (D11.Ch10.LpDefinition.essentialSupNorm_eq_eLpNorm μ _
      ((f n).property.1.sub g.property.1)).symm
  rw [heq]
  exact ⟨fun h => ⟨hg, hf, h⟩, fun h => h.2.2⟩

theorem finite_convergence : Specs.D11.Ch10.LpConvergenceMeasure.finite_convergence := by
  intro X 𝕜 _ _ _ _ μ p f g h
  rcases h with ⟨hp, hg, hf, hlim⟩
  have hn := (powerNorm_tendsto_iff μ p (lt_of_lt_of_le zero_lt_one hp)
    (fun n x => f n x - g x)).mpr hlim
  have heq : (fun n => D11.Ch10.LpDefinition.powerNorm μ p (f n - g)) =
      (fun n => eLpNorm (f n - g) (ENNReal.ofReal p) μ) := by
    funext n
    exact D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm μ p _ hp ((hf n).1.sub hg.1)
  change Tendsto (fun n => D11.Ch10.LpDefinition.powerNorm μ p (f n - g))
    atTop (𝓝 0) at hn
  rw [heq] at hn
  have hm := (D11.Ch07.SubsequenceUniqueness.inMeasureConverges_iff_native μ f g).mpr
    (tendstoInMeasure_of_tendsto_eLpNorm
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hp)) hn)
  exact ⟨hm, D11.Ch07.SubsequenceUniqueness.exists_ae_subsequence μ f g hm⟩

theorem infinity_convergence : Specs.D11.Ch10.LpConvergenceMeasure.infinity_convergence := by
  intro X 𝕜 _ _ _ _ μ f g h
  rcases h with ⟨hg, hf, hlim⟩
  change Tendsto (fun n => essentialSupNorm μ (f n - g)) atTop (𝓝 0) at hlim
  have hb : ∀ n, essentialSupNorm μ (f n - g) < ∞ := by
    intro n
    have hn := ((D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ (f n)).mp (hf n)).2
    have hg' := ((D11.Ch10.LpDefinition.rawLInfinity_iff_memLp μ g).mp hg).2
    have heq := D11.Ch10.LpDefinition.essentialSupNorm_eq_eLpNorm μ _
      ((hf n).1.sub hg.1)
    exact heq.trans_lt (hn.sub hg').eLpNorm_lt_top
  obtain ⟨N, hN, hbound⟩ := common_exception μ
    (fun n x => ‖f n x - g x‖ ≤ (essentialSupNorm μ (f n - g)).toReal)
    (fun n => essential_bound_attained μ (f n - g) (hb n))
  refine ⟨Nᶜ, hN.1.compl, by simpa using hN.2, ?_⟩
  intro ε hε
  have hreal : Tendsto (fun n => (essentialSupNorm μ (f n - g)).toReal) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hreal.eventually (gt_mem_nhds hε))
  exact ⟨k, fun n hn x hx => (hbound x hx n).trans_lt (hk n hn)⟩

theorem quotient_convergence_bridge :
    Specs.D11.Ch10.LpConvergenceMeasure.quotient_convergence_bridge := by
  intro X 𝕜 _ _ _ _ μ p _ G V F hF f g
  constructor
  · intro h
    simpa only [Function.comp_def, hF] using F.continuous.continuousAt.tendsto.comp h
  · intro h
    have h' : Tendsto (fun n => F (classOf (f n))) atTop (𝓝 (F (classOf g))) := by
      simpa only [hF] using h
    simpa only [Function.comp_def, F.symm_apply_apply] using
      F.symm.continuous.continuousAt.tendsto.comp h'

end D11.Ch10.LpConvergenceMeasure
