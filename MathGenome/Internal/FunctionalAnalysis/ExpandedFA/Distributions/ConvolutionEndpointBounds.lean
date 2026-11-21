import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ConvolutionEndpointBounds
import MathGenome.RealAnalysis.Topics.D11.Ch10

/-!
Endpoint convolution estimates, paper.tex:17297–17302. The finite-p estimate
uses scalar Minkowski on a sigma-finite product, independently of interpolation
and full Young. The infinity/dual-exponent estimates use Hölder directly.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace ExpandedFA.Distributions
open ConvolutionEndpointBoundsSpec

def scalarConvolution : ConvolutionType := ConvolutionValue

/-- Native extended-norm version of scalar Minkowski on sigma-finite products. -/
lemma minkowski_integral_eLpNorm {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) (F : X × Y → 𝕜) (hF : Measurable F)
    (hfin : (∫⁻ y, eLpNorm (fun x => F (x,y)) p μ ∂ν) < ∞) :
    (∀ᵐ x ∂μ, Integrable (fun y => F (x,y)) ν) ∧
      eLpNorm (fun x => ∫ y, F (x,y) ∂ν) p μ ≤
        ∫⁻ y, eLpNorm (fun x => F (x,y)) p μ ∂ν := by
  have hpR : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).mpr hp
  have hs (y : Y) : Specs.D11.Ch10.LpDefinition.powerNorm_value μ p.toReal
      (fun x => F (x,y)) = eLpNorm (fun x => F (x,y)) p μ := by
    erw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm _ _ _ hpR
      (hF.comp measurable_prodMk_right), ENNReal.ofReal_toReal hpt]
    rfl
  have hR : Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ν
      (fun y => Specs.D11.Ch10.LpDefinition.powerNorm_value μ p.toReal
        (fun x => F (x,y))) = ∫⁻ y, eLpNorm (fun x => F (x,y)) p μ ∂ν := by
    calc
      _ = ∫⁻ y, Specs.D11.Ch10.LpDefinition.powerNorm_value μ p.toReal
          (fun x => F (x,y)) ∂ν := D11.Ch05.NonnegativeIntegral.integral_eq_lintegral _ _
      _ = _ := lintegral_congr hs
  obtain ⟨_, hi, _, _, hg, hb⟩ := D11.Ch10.MinkowskiIntegral.scalar_minkowski
    μ ν inferInstance inferInstance p.toReal hpR F hF (by rw [hR]; exact hfin)
  have he : Specs.D11.Ch08.Fubini.sectionIntegralLeft_value ν F =
      (fun x => ∫ y, F (x,y) ∂ν) :=
    D11.Ch08.Fubini.sectionIntegralLeft_eq_integral ν F hF
  rw [he] at hg hb
  erw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm _ _ _ hpR hg.1,
    ENNReal.ofReal_toReal hpt, hR] at hb
  refine ⟨?_, hb⟩
  apply (D11.Ch04.AeCommonException.almostEverywhere_iff_native _ _).mp at hi
  exact hi.mono fun x hx => (D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mp hx |>.2

lemma scalarConvolution_eq_native {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f g : (Fin d → ℝ) → 𝕜) :
    ConvolutionValue f g = MeasureTheory.convolution f g (ContinuousLinearMap.mul 𝕜 𝕜) volume := rfl

theorem convolution_representative_independence : RepresentativeIndependence := by
  intro d 𝕜 _ f f' g g' hf hg
  have hi (x : Fin d → ℝ) : (fun y => f y * g (x-y)) =ᵐ[volume]
      (fun y => f' y * g' (x-y)) := by
    exact hf.mul ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hg)
  exact ⟨fun x => integrable_congr (hi x), funext fun x => integral_congr_ae (hi x)⟩

theorem convolution_measurable : ConvolutionMeasurable := by
  intro d 𝕜 _ _ _ f g hf hg
  let f' := hf.mk f
  let g' := hg.mk g
  have hff : f =ᵐ[volume] f' := hf.ae_eq_mk
  have hgg : g =ᵐ[volume] g' := hg.ae_eq_mk
  rw [(convolution_representative_independence f f' g g' hff hgg).2]
  have hF : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) =>
      f' z.2 * g' (z.1-z.2)) :=
    (hf.stronglyMeasurable_mk.measurable.comp measurable_snd).mul
      (hg.stronglyMeasurable_mk.measurable.comp (measurable_fst.sub measurable_snd))
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

/-- Hölder gives everywhere absolute existence, including p=1 and p=∞. -/
theorem young_holder_endpoint : HolderEndpoint := by
  intro d 𝕜 _ p q _ f g hf hg
  let L := ContinuousLinearMap.mul 𝕜 𝕜
  have hi := MeasureTheory.ConvolutionExists.of_memLp_memLp L hf hg
  have hm : AEStronglyMeasurable (ConvolutionValue f g) volume :=
    hf.aestronglyMeasurable.convolution L hg.aestronglyMeasurable
  have hb (x : Fin d → ℝ) : ‖ConvolutionValue f g x‖ₑ ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    change ‖MeasureTheory.convolution f g L volume x‖ₑ ≤ _
    simpa [L] using MeasureTheory.enorm_convolution_le L hf.aestronglyMeasurable
      hg.aestronglyMeasurable x
  have hn : eLpNorm (ConvolutionValue f g) ∞ volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    rw [eLpNorm_exponent_top hm]
    exact eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall hb)
  exact ⟨hi, hm, hn.trans_lt (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top),
    hb, hn⟩

/-- Finite-p proof for Borel representatives, including dimension zero. -/
lemma young_l1_lp_measurable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) (f g : (Fin d → ℝ) → 𝕜)
    (hfm : Measurable f) (hgm : Measurable g) (hf : MemLp f 1 volume)
    (hg : MemLp g p volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))) ∧
      eLpNorm (ConvolutionValue f g) p volume ≤ eLpNorm f 1 volume * eLpNorm g p volume := by
  let F : (Fin d → ℝ) × (Fin d → ℝ) → 𝕜 := fun z => f z.2 * g (z.1-z.2)
  have hF : Measurable F := (hfm.comp measurable_snd).mul
    (hgm.comp (measurable_fst.sub measurable_snd))
  have hs (y : Fin d → ℝ) : eLpNorm (fun x => F (x,y)) p volume =
      ‖f y‖ₑ * eLpNorm g p volume := by
    change eLpNorm ((f y) • (fun x => g (x-y))) p volume = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖f y‖ₑ * ·) (eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
      (measurePreserving_sub_right volume y))
  have hR : (∫⁻ y, eLpNorm (fun x => F (x,y)) p volume) =
      eLpNorm f 1 volume * eLpNorm g p volume := by
    simp_rw [hs]
    rw [lintegral_mul_const _ hfm.enorm, ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  obtain ⟨hi, hb⟩ := minkowski_integral_eLpNorm volume volume p hp hpt F hF
    (by rw [hR]; exact ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)
  exact ⟨hi, hb.trans_eq hR⟩

/-- Arbitrary Lp representatives, with ordinary a.e. convergence of the integral. -/
theorem young_l1_lp_endpoint : L1LpEndpoint := by
  intro d 𝕜 _ p hp f g hf hg
  by_cases hpt : p = ∞
  · subst p
    obtain ⟨hi, hm, hmem, _, hb⟩ := young_holder_endpoint 1 ∞ f g hf hg
    exact ⟨Eventually.of_forall hi, hm, hmem, hb⟩
  let : MeasurableSpace 𝕜 := borel 𝕜
  have hfm := hf.aestronglyMeasurable
  have hgm := hg.aestronglyMeasurable
  let f' := hfm.mk f
  let g' := hgm.mk g
  have hff : f =ᵐ[volume] f' := hfm.ae_eq_mk
  have hgg : g =ᵐ[volume] g' := hgm.ae_eq_mk
  have hconv := convolution_representative_independence f f' g g' hff hgg
  have hfn := hf.ae_eq hff
  have hgn := hg.ae_eq hgg
  obtain ⟨hi, hb⟩ := young_l1_lp_measurable p hp hpt f' g'
    hfm.stronglyMeasurable_mk.measurable hgm.stronglyMeasurable_mk.measurable hfn hgn
  have hm : AEStronglyMeasurable (ConvolutionValue f g) volume :=
    hfm.convolution (ContinuousLinearMap.mul 𝕜 𝕜) hgm
  rw [← hconv.2, eLpNorm_congr_ae hff.symm, eLpNorm_congr_ae hgg.symm] at hb
  refine ⟨hi.mono (fun x hx => (hconv.1 x).mpr hx), hm, ?_, hb⟩
  exact hb.trans_lt (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)

/-- Construction and norm bound on the ordinary a.e. quotient. -/
theorem lp_convolution_l1_bound : L1LpQuotientBound := by
  intro d 𝕜 _ p _ f g
  obtain ⟨_, _, hc, hb⟩ := young_l1_lp_endpoint p Fact.out f g (Lp.memLp f) (Lp.memLp g)
  refine ⟨hc.toLp (ConvolutionValue f g), ⟨hc.coeFn_toLp, ?_⟩, ?_⟩
  · rw [Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp f).ne (Lp.memLp g).ne) hb
  · intro h hh
    exact Lp.ext (hh.1.trans hc.coeFn_toLp.symm)

/-- Hölder's endpoint as a uniquely specified essentially bounded class. -/
theorem lp_convolution_holder_bound : HolderQuotientBound := by
  intro d 𝕜 _ p q _ _ _ f g
  obtain ⟨_, _, hc, _, hb⟩ := young_holder_endpoint p q f g (Lp.memLp f) (Lp.memLp g)
  refine ⟨hc.toLp (ConvolutionValue f g), ⟨hc.coeFn_toLp, ?_⟩, ?_⟩
  · rw [Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp f).ne (Lp.memLp g).ne) hb
  · intro h hh
    exact Lp.ext (hh.1.trans hc.coeFn_toLp.symm)

end ExpandedFA.Distributions
