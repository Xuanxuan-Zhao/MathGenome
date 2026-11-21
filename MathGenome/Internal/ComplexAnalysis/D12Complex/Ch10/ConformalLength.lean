import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.ConformalLength
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.ArclengthFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.TaylorSmoothness
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal Interval
namespace D12Complex.ConformalLength
open Stieltjes

/-- Weak holomorphy implies a Lipschitz bound on every compact subset of its
open domain, even if that compact set is not convex. -/
theorem lipschitzOn_compact {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, LipschitzOnWith C f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro z hz
  have hs := TaylorSmoothness.holomorphic_real_smooth Ω f hf
  have hc : ContDiffAt ℝ 1 f z :=
    (hs.of_le (by simp)).contDiffAt (hf.1.mem_nhds (hKΩ hz))
  obtain ⟨C, U, hU, hlip⟩ := hc.exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hlip⟩

theorem ac_comp : Specs.D12Complex.Ch10.ConformalLength.ac_comp_type := by
  intro Ω f hf a b hab γ hγ hmaps
  have hc : ContinuousOn γ (Icc a b) := by
    simpa only [uIcc_of_le hab] using hγ.continuousOn
  obtain ⟨C, hlip⟩ := lipschitzOn_compact hf (isCompact_Icc.image_of_continuousOn hc)
    (by rintro z ⟨t, ht, rfl⟩; exact hmaps ht)
  apply hlip.comp_absolutelyContinuousOnInterval _ hγ
  simpa only [uIcc_of_le hab] using (mapsTo_image γ (Icc a b))

theorem ac_chain_rule : Specs.D12Complex.Ch10.ConformalLength.ac_chain_rule_type := by
  intro Ω f hf a b hab γ hγ hmaps
  have hd := (ac_derivative hab γ hγ).2.1
  rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hd] with t ht hmem
  have houter := (hf.2 (γ t) (hmaps (Ioo_subset_Icc_self hmem))).hasDerivAt
  simpa only [smul_apply, one_apply_eq_self,
    smul_eq_mul] using houter.complexToReal_fderiv.comp_hasDerivAt t (ht hmem)

theorem ac_length : Specs.D12Complex.Ch10.ConformalLength.ac_length_type := by
  intro Ω f hf a b hab γ hγ hmaps
  have hac := ac_comp hf hab γ hγ hmaps
  have heq : (fun t => ‖deriv (f ∘ γ) t‖) =ᵐ[volume.restrict (Icc a b)]
      (fun t => ‖deriv f (γ t)‖ * ‖deriv γ t‖) := by
    filter_upwards [ac_chain_rule hf hab γ hγ hmaps] with t ht
    rw [ht.deriv, norm_mul]
  have heq' : (fun t => ‖deriv (f ∘ γ) t‖) =ᵐ[volume.restrict (Ι a b)]
      (fun t => ‖deriv f (γ t)‖ * ‖deriv γ t‖) := by
    rw [uIoc_of_le hab]
    exact heq.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  refine ⟨hac, ac_finite_variation hab _ hac,
    ((ac_derivative hab _ hac).1.norm.congr_ae heq'), ?_⟩
  exact (Arclength.ac_length hab _ hac).trans
    (intervalIntegral.integral_congr_ae_restrict heq')

theorem degenerate_length : Specs.D12Complex.Ch10.ConformalLength.degenerate_length_type := by
  intro f γ a
  simp [totalVariation_degenerate]

theorem rectifiable_length : Specs.D12Complex.Ch10.ConformalLength.rectifiable_length_type := by
  intro Ω f hf γ hγ hmaps
  obtain ⟨σ, hlip, hfac, htrace, hvar⟩ := Arclength.lipschitz_factor γ hγ
  let L := (polygonalLength γ).toReal
  have hL : (0 : ℝ) ≤ L := ENNReal.toReal_nonneg
  have hac : AbsolutelyContinuousOnInterval σ 0 L :=
    (show LipschitzOnWith 1 σ (uIcc 0 L) from by
      simpa only [uIcc_of_le hL] using hlip).absolutelyContinuousOnInterval
  obtain ⟨hcomp, hfin, hi, hlen⟩ := ac_length hf hL σ hac
    (fun t ht => hmaps (htrace ▸ mem_image_of_mem σ ht))
  obtain ⟨_, hm, _, _, himg⟩ := Arclength.accumulated_properties γ hγ
  have heq : totalVariation (f ∘ γ) γ.a γ.b = totalVariation (f ∘ σ) 0 L := by
    rw [← variation_monotone hL γ.ordered (f ∘ σ) (Arclength.accumulated γ) hm himg,
      totalVariation_eq_eVariationOn _ γ.ordered,
      totalVariation_eq_eVariationOn _ γ.ordered]
    apply eVariationOn.congr
    intro t ht
    simp only [Function.comp_apply, ← hfac t ht]
  exact ⟨σ, hlip, hfac, htrace, hvar, hcomp, heq ▸ hfin, hi, by rw [heq]; exact hlen⟩

end D12Complex.ConformalLength
