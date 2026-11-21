import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.PairingNormEndpoint
import MathGenome.Internal.RealAnalysis.D11.Ch20.IntegralPairing
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith

open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace D11.Ch20.PairingNormEndpoint
open Specs.D11.Ch20.PairingNormEndpoint
open D11.Ch20.IntegralPairing

abbrev semifinite {X : Type u} [MeasurableSpace X] (μ : Measure X) : Prop :=
  IsSemifinite μ

/-- Continuity from below on a finite-measure exhaustion gives exactly the
supremum property in the source definition. -/
theorem sigmaFinite_semifinite : Specs.D11.Ch20.PairingNormEndpoint.sigmaFinite_semifinite := by
  intro X _ μ hμ
  obtain ⟨F, hF, hmono, hcover⟩ :=
    (D11.Ch01.ExhaustionRestriction.sigmaFinite_iff_increasing_exhaustion μ).mp hμ
  intro E hE
  apply le_antisymm
  · have hlim : μ E = ⨆ n, μ (E ∩ F n) := by
      rw [← (show Monotone (fun n => E ∩ F n) from
        fun i j hij => inter_subset_inter_right E (hmono hij)).measure_iUnion]
      simp only [← inter_iUnion, hcover, inter_univ]
    rw [hlim]
    refine iSup_le fun n => ?_
    exact le_iSup_of_le (E ∩ F n) (le_iSup_of_le inter_subset_left
      (le_iSup_of_le (hE.inter (hF n).1)
        (le_iSup_of_le ((measure_mono inter_subset_right).trans_lt (hF n).2) le_rfl)))
  · exact iSup_le fun A => iSup_le fun hAE => iSup_le fun _ => iSup_le fun _ =>
      measure_mono hAE

lemma exists_finite_positive_subset {X : Type u} [MeasurableSpace X]
    {μ : Measure X} (hμ : IsSemifinite μ) {E : Set X}
    (hE : MeasurableSet E) (hpos : 0 < μ E) :
    ∃ A : Set X, A ⊆ E ∧ MeasurableSet A ∧ 0 < μ A ∧ μ A < ∞ := by
  by_contra! h
  have hz : μ E = 0 := by
    rw [hμ E hE]
    apply le_antisymm _ bot_le
    refine iSup_le fun A => iSup_le fun hAE => iSup_le fun hA => iSup_le fun hfin => ?_
    exact le_of_not_gt (fun hpos => not_lt_of_ge (h A hAE hA hpos) hfin)
  exact hpos.ne' hz

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

lemma norm_le_of_ae_bound_top {μ : Measure X} (g : Lp 𝕜 ∞ μ)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ c) : ‖g‖ ≤ c := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound h)).trans_eq (ENNReal.toReal_ofReal hc)

lemma ae_norm_le {μ : Measure X} (g : Lp 𝕜 ∞ μ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖g‖ := by
  have h := enorm_ae_le_eLpNormEssSup (g : X → 𝕜) μ
  filter_upwards [h] with x hx
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm] using
    ENNReal.toReal_mono (by
      simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable g)] using Lp.eLpNorm_ne_top g) hx

/-- A finite positive part of a strict superlevel set gives a test in L¹.
Using the conjugate itself avoids any division by pointwise values. -/
lemma finite_test_lower_bound (μ : Measure X) (g : Lp 𝕜 ∞ μ)
    {c : ℝ} (hc : 0 < c) {A : Set X} (hA : MeasurableSet A)
    (hpos : 0 < μ A) (hfin : μ A < ∞)
    (hlevel : ∀ x ∈ A, c < ‖g x‖) :
    c ≤ ‖pairing μ 1 ∞ g‖ := by
  let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hfin.ne
  have hg_bound : ∀ᵐ x ∂μ.restrict A, ‖g x‖ ≤ ‖g‖ :=
    ae_restrict_of_ae (ae_norm_le g)
  have hg_int : Integrable (fun x => g x) (μ.restrict A) :=
    Integrable.of_bound (Lp.aestronglyMeasurable g).restrict ‖g‖ hg_bound
  have hconj_int : Integrable (fun x => conj (g x)) (μ.restrict A) := by
    apply Integrable.of_bound
      (RCLike.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g).restrict) ‖g‖
    simpa only [RCLike.norm_conj] using hg_bound
  have hsq_int : Integrable (fun x => ‖g x‖ ^ 2) (μ.restrict A) := by
    apply Integrable.of_bound ((Lp.aestronglyMeasurable g).restrict.norm.pow 2) (‖g‖ ^ 2)
    filter_upwards [hg_bound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hfi : Integrable (A.indicator (fun x => conj (g x))) μ :=
    IntegrableOn.integrable_indicator hconj_int hA
  let hf := memLp_one_iff_integrable.mpr hfi
  let f : Lp 𝕜 1 μ := hf.toLp _
  have hfnorm : ‖f‖ = ∫ x in A, ‖g x‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    calc
      _ = ∫ x, ‖A.indicator (fun x => conj (g x)) x‖ ∂μ :=
        integral_congr_ae ((MemLp.coeFn_toLp hf).fun_comp norm)
      _ = ∫ x, A.indicator (fun x => ‖g x‖) x ∂μ := by
        congr 1
        ext x
        by_cases hx : x ∈ A <;> simp [hx]
      _ = _ := integral_indicator hA
  have hpair : pairing μ 1 ∞ g f =
      ((∫ x in A, ‖g x‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
    change Specs.D11.Ch20.IntegralPairing.pairing_value μ 1 ∞ g f = _
    rw [(pairing_eq_integral μ 1 ∞ g f).2]
    calc
      _ = ∫ x, A.indicator (fun x => conj (g x) * g x) x ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hf] with x hx
        rw [hx]
        by_cases hxA : x ∈ A <;> simp [hxA]
      _ = ∫ x in A, conj (g x) * g x ∂μ := integral_indicator hA
      _ = _ := by simp only [RCLike.conj_mul, ← RCLike.ofReal_pow, integral_ofReal]
  have hIpos : 0 < ∫ x in A, ‖g x‖ ∂μ := by
    have hlow : c * (μ A).toReal ≤ ∫ x in A, ‖g x‖ ∂μ := by
      calc
        _ = ∫ _ in A, c ∂μ := by simp [integral_const, mul_comm, Measure.real]
        _ ≤ _ := integral_mono_ae (integrable_const c) hg_int.norm
          ((ae_restrict_iff' hA).mpr (ae_of_all μ fun x hx => (hlevel x hx).le))
    exact (mul_pos hc (ENNReal.toReal_pos hpos.ne' hfin.ne)).trans_le hlow
  have hlow : c * (∫ x in A, ‖g x‖ ∂μ) ≤ ∫ x in A, ‖g x‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hg_int.norm.const_mul c) hsq_int
    apply (ae_restrict_iff' hA).mpr
    exact ae_of_all μ fun x hx => by
      nlinarith [hlevel x hx, norm_nonneg (g x)]
  have hupp := (pairing μ 1 ∞ g).le_opNorm f
  rw [hpair, RCLike.norm_ofReal,
    abs_of_nonneg (integral_nonneg (fun x => sq_nonneg ‖g x‖)), hfnorm] at hupp
  exact (mul_le_mul_iff_left₀ hIpos).mp (hlow.trans hupp)

theorem pairing_norm_endpoint : Specs.D11.Ch20.PairingNormEndpoint.pairing_norm_endpoint := by
  intro X 𝕜 _ _ μ hμ g
  apply le_antisymm (pairing_norm_bound μ 1 ∞ g)
  by_contra! hlt
  obtain ⟨c, hTc, hcg⟩ := exists_between hlt
  have hc : 0 < c := (norm_nonneg _).trans_lt hTc
  have hE : MeasurableSet {x | c < ‖g x‖} := by
    exact measurableSet_lt measurable_const (Lp.stronglyMeasurable g).measurable.norm
  have hpos : 0 < μ {x | c < ‖g x‖} := by
    by_contra! hz
    have hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ c := by
      rw [ae_iff]
      simpa only [not_le] using (le_antisymm hz bot_le)
    exact hcg.not_ge (norm_le_of_ae_bound_top g hc.le hbound)
  obtain ⟨A, hAE, hA, hApos, hAfin⟩ := exists_finite_positive_subset hμ hE hpos
  have htest := finite_test_lower_bound μ g hc hA hApos hAfin (fun x hx => hAE hx)
  exact hTc.not_ge htest

section OrdinaryQuotient
variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]
open Specs.D11.Ch10.QuotientConstruction
open D11.Ch10.QuotientConstruction

lemma quotientPairing_norm_endpoint (μ : Measure X) (hμ : IsSemifinite μ)
    (g : QuotientLp (𝕜 := 𝕜) μ ∞) : ‖quotientPairing μ 1 ∞ g‖ = ‖g‖ := by
  apply le_antisymm (quotientPairing_norm_bound μ 1 ∞ g)
  have hn : ‖g‖ = ‖pairing μ 1 ∞ (nativeLinearIsometryEquiv μ ∞ g)‖ :=
    ((nativeLinearIsometryEquiv μ ∞).norm_map g).symm.trans
      (pairing_norm_endpoint μ hμ (nativeLinearIsometryEquiv μ ∞ g)).symm
  rw [hn]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have ht := (quotientPairing μ 1 ∞ g).le_opNorm
    ((nativeLinearIsometryEquiv μ 1).symm f)
  simpa only [quotientPairing_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.norm_map] using ht

theorem ordinary_pairing_norm_endpoint :
    Specs.D11.Ch20.PairingNormEndpoint.ordinary_pairing_norm_endpoint := by
  intro X 𝕜 _ _ _ _ μ hμ
  refine ⟨quotientNormedAddCommGroup μ 1, quotientNormedSpace μ 1,
    quotientNormedAddCommGroup μ ∞, quotientNormedSpace μ ∞,
    quotientPairing μ 1 ∞, norm_classOf μ 1, norm_classOf μ ∞, ?_,
    quotientPairing_norm_endpoint μ hμ⟩
  intro f g
  simpa only [quotientPairing_apply, nativeLinearIsometryEquiv_classOf,
    pairing, Specs.D11.Ch20.IntegralPairing.pairing_value] using
    pairing_on_raw μ 1 ∞ f g

end OrdinaryQuotient
end D11.Ch20.PairingNormEndpoint
