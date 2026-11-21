import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionBound
import MathGenome.Internal.RealAnalysis.D11.Ch11.TranslationContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch10.MinkowskiIntegral
import Mathlib.MeasureTheory.Measure.AEMeasurable

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal
namespace D11.Ch11.ConvolutionBound
open D11.Ch03 D11.Ch03.LebesgueMeasures D11.Ch10
open Specs.D11.Ch03.LebesgueMeasures

abbrev convolution : Specs.D11.Ch11.ConvolutionBound.convolution_type :=
  Specs.D11.Ch11.ConvolutionBound.convolution_value

/-- Equal outer evaluations recover original measurable scalar versions.
The sigma-finite exhaustion is used only to make the hull subtraction finite. -/
lemma aemeasurable_of_equal_outer {X E : Type*}
    {m m' : MeasurableSpace X} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
    (μ : @Measure X m) (ν : @Measure X m') [SigmaFinite μ]
    (hm : m ≤ m') (heq : ∀ s, ν s = μ s) {f : X → E}
    (hf : @Measurable X E m' _ f) : @AEMeasurable X E _ m f μ := by
  let := m
  have hset (s : Set X) (hs : MeasurableSet[m'] s) : @NullMeasurableSet X m s μ := by
    have hn (n : ℕ) : @NullMeasurableSet X m (s ∩ spanningSets μ n) μ := by
      let t := s ∩ spanningSets μ n
      let T := toMeasurable μ t
      have ht : MeasurableSet[m'] t := @MeasurableSet.inter X m' _ _ hs (hm _ (measurableSet_spanningSets μ n))
      have hfin : ν t ≠ ∞ := ne_top_of_le_ne_top
        (by rw [heq]; exact (measure_spanningSets_lt_top μ n).ne)
        (measure_mono inter_subset_right)
      have hT : ν T = ν t := by simp only [heq, T, measure_toMeasurable]
      have hdiff : μ (T \ t) = 0 := by
        rw [← heq, measure_sdiff (subset_toMeasurable μ t) ht.nullMeasurableSet hfin, hT, tsub_self]
      refine ⟨T, measurableSet_toMeasurable μ t, ae_eq_set.mpr ⟨?_, hdiff⟩⟩
      rw [sdiff_eq_empty.mpr (subset_toMeasurable μ t), measure_empty]
    have he : s = ⋃ n, s ∩ spanningSets μ n := by
      rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
    rw [he]
    exact NullMeasurableSet.iUnion hn
  exact (show @NullMeasurable X E m _ f μ from fun s hs => hset _ (hf hs)).aemeasurable

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]

/-- The reflection-translation x-y preserves completed Lebesgue measure. -/
lemma measurePreserving_const_sub (x : Point d) :
    @MeasurePreserving _ _ (lebesgueSpace_value d) (lebesgueSpace_value d)
      (fun y => x-y) (lebesgue_value d) (lebesgue_value d) := by
  let := lebesgueSpace_value d
  have hpre (s : Set (Point d)) :
      (fun y => x-y) ⁻¹' s = (fun y => x + (-1 : ℝ) • y) '' s := by
    ext y
    simp only [mem_preimage, mem_image, neg_one_smul]
    constructor
    · intro hy
      exact ⟨x-y, hy, by abel⟩
    · rintro ⟨z, hz, rfl⟩
      have hh : x - (x + -z) = z := by abel
      rwa [hh]
  have hm : Measurable (fun y : Point d => x-y) := by
    intro s hs
    rw [hpre]
    exact (TranslationDilation.lebesgue_affine d x (-1) s hs).1
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, hpre]
  simpa using (TranslationDilation.lebesgue_affine d x (-1) s hs).2

/-- Borel scalar versions, compared using original null envelopes. -/
lemma borel_version [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜) (hf : @Measurable _ _ (lebesgueSpace_value d) _ f) :
    ∃ g : Point d → 𝕜, Measurable g ∧
      f =ᵐ[lebesgue_value d] g := by
  have ha : AEMeasurable f (volume : Measure (Point d)) :=
    aemeasurable_of_equal_outer volume (lebesgue_value d) (native_borel_le d)
      (EuclideanRegularity.lebesgue_eq_volume d) hf
  refine ⟨ha.mk f, ha.measurable_mk, ?_⟩
  apply ae_iff.mpr
  exact (EuclideanRegularity.lebesgue_eq_volume d _).trans (ae_iff.mp ha.ae_eq_mk)

/-- Scalar integrands from Borel versions are measurable on the product of
completed factors. This does not assert completed-valued joint subtraction. -/
lemma borel_integrand_measurable [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {k f : Point d → 𝕜} (hk : Measurable k) (hf : Measurable f) :
    @Measurable _ _ ((lebesgueSpace_value d).prod (lebesgueSpace_value d)) _
      (fun z : Point d × Point d => k z.2 * f (z.1-z.2)) := by
  have hi : @Measurable (Point d) (Point d) (lebesgueSpace_value d) _ id :=
    measurable_id'' (native_borel_le d)
  letI : MeasurableSpace (Point d × Point d) := (lebesgueSpace_value d).prod (lebesgueSpace_value d)
  exact (hk.comp (hi.comp measurable_snd)).mul
    (hf.comp ((hi.comp measurable_fst).sub (hi.comp measurable_snd)))

section Completed
local instance : MeasurableSpace (Point d) := lebesgueSpace_value d

lemma integrand_congr {k k' f f' : Point d → 𝕜}
    (hk : k =ᵐ[lebesgue_value d] k') (hf : f =ᵐ[lebesgue_value d] f') (x : Point d) :
    (fun y => k y * f (x-y)) =ᵐ[lebesgue_value d] (fun y => k' y * f' (x-y)) := by
  filter_upwards [hk, (measurePreserving_const_sub x).quasiMeasurePreserving.ae hf]
    with y hy hz
  rw [hy, hz]

theorem representative_independence :
    Specs.D11.Ch11.ConvolutionBound.representative_independence := by
  intro d _ 𝕜 _
  let := lebesgueSpace_value d
  intro k k' f f' hk hf
  exact ⟨fun x => integrable_congr (integrand_congr hk hf x),
    funext fun x => integral_congr_ae (integrand_congr hk hf x)⟩

theorem zero_extension : Specs.D11.Ch11.ConvolutionBound.zero_extension := by
  intro d _ 𝕜 _ k f x hx
  exact integral_undef hx

theorem bilinearity : Specs.D11.Ch11.ConvolutionBound.bilinearity := by
  intro d _ 𝕜 _
  let := lebesgueSpace_value d
  intro k k' f f' x
  change (_ → _ → (∫ y, (k+k') y * f (x-y) ∂lebesgue_value d) = _) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h h'
    simpa only [Specs.D11.Ch11.ConvolutionBound.convolution_value, Pi.add_apply, add_mul] using integral_add h h'
  · intro h h'
    simpa only [Specs.D11.Ch11.ConvolutionBound.convolution_value, Pi.add_apply, mul_add] using integral_add h h'
  · intro c
    simpa only [Specs.D11.Ch11.ConvolutionBound.convolution_value, Pi.smul_apply, smul_eq_mul, mul_assoc] using
      integral_const_mul (μ := lebesgue_value d) c (fun y => k y * f (x-y))
  · intro c
    simpa only [Specs.D11.Ch11.ConvolutionBound.convolution_value, Pi.smul_apply, smul_eq_mul, mul_left_comm] using
      integral_const_mul (μ := lebesgue_value d) c (fun y => k y * f (x-y))

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Finite exponents for a jointly measurable scalar convolution integrand. -/
lemma young_finite {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {k f : Point d → 𝕜} (hk : Measurable k) (hf : Measurable f)
    (hk1 : MemLp k 1 (lebesgue_value d)) (hfp : MemLp f p (lebesgue_value d))
    (hF : Measurable (fun z : Point d × Point d => k z.2 * f (z.1-z.2))) :
    (∀ᵐ x ∂lebesgue_value d, Integrable (fun y => k y * f (x-y)) (lebesgue_value d)) ∧
      Measurable (convolution d k f) ∧ MemLp (convolution d k f) p (lebesgue_value d) ∧
      eLpNorm (convolution d k f) p (lebesgue_value d) ≤
        eLpNorm k 1 (lebesgue_value d) * eLpNorm f p (lebesgue_value d) := by
  letI : SigmaFinite (lebesgue_value d) := lebesgue_sigmaFinite d
  have hpR : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).mpr hp
  have hsection (y : Point d) :
      Specs.D11.Ch10.LpDefinition.powerNorm_value (lebesgue_value d) p.toReal (fun x => k y * f (x-y)) =
        ‖k y‖ₑ * eLpNorm f p (lebesgue_value d) := by
    erw [LpDefinition.powerNorm_eq_eLpNorm _ _ _ hpR
      (hF.comp measurable_prodMk_right), ENNReal.ofReal_toReal hpt]
    change eLpNorm ((k y) • (fun x => f (x-y))) p (lebesgue_value d) = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖k y‖ₑ * ·)
      (eLpNorm_comp_measurePreserving hfp.aestronglyMeasurable
        (TranslationContinuity.measurePreserving_sub_const y))
  have hR : Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value (lebesgue_value d)
      (fun y => Specs.D11.Ch10.LpDefinition.powerNorm_value (lebesgue_value d) p.toReal
        (fun x => k y * f (x-y))) =
        eLpNorm k 1 (lebesgue_value d) * eLpNorm f p (lebesgue_value d) := by
    calc
      _ = ∫⁻ y, Specs.D11.Ch10.LpDefinition.powerNorm_value (lebesgue_value d)
          p.toReal (fun x => k y * f (x-y)) ∂lebesgue_value d :=
        D11.Ch05.NonnegativeIntegral.integral_eq_lintegral _ _
      _ = ∫⁻ y, ‖k y‖ₑ * eLpNorm f p (lebesgue_value d) ∂lebesgue_value d :=
        lintegral_congr hsection
      _ = _ := by
        rw [lintegral_mul_const _ hk.enorm,
          ← eLpNorm_one_eq_lintegral_enorm hk1.aestronglyMeasurable]
  obtain ⟨_, hi, _, _, hg, hbound⟩ := MinkowskiIntegral.scalar_minkowski
    (lebesgue_value d) (lebesgue_value d) inferInstance inferInstance p.toReal hpR
      (fun z : Point d × Point d => k z.2 * f (z.1-z.2)) hF
      (by rw [hR]; exact ENNReal.mul_lt_top hk1.eLpNorm_lt_top hfp.eLpNorm_lt_top)
  have hgeq : Specs.D11.Ch08.Fubini.sectionIntegralLeft_value (lebesgue_value d)
      (fun z : Point d × Point d => k z.2 * f (z.1-z.2)) = convolution d k f :=
    D11.Ch08.Fubini.sectionIntegralLeft_eq_integral _ _ hF
  rw [hgeq] at hg hbound
  have hgm : Measurable (convolution d k f) := hg.1
  have hgnorm := LpDefinition.powerNorm_eq_eLpNorm (lebesgue_value d) p.toReal
    (convolution d k f) hpR hgm
  rw [ENNReal.ofReal_toReal hpt] at hgnorm
  have hb : eLpNorm (convolution d k f) p (lebesgue_value d) ≤
      eLpNorm k 1 (lebesgue_value d) * eLpNorm f p (lebesgue_value d) := by
    rw [← hgnorm]
    exact hbound.trans_eq hR
  refine ⟨?_, hgm, hb.trans_lt (ENNReal.mul_lt_top hk1.eLpNorm_lt_top hfp.eLpNorm_lt_top), hb⟩
  apply (D11.Ch04.AeCommonException.almostEverywhere_iff_native _ _).mp at hi
  exact hi.mono fun x hx => (D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mp hx |>.2

/-- The infinity endpoint has absolute existence at every point. -/
lemma young_top {k f : Point d → 𝕜} (_hk : Measurable k) (_hf : Measurable f)
    (hk1 : MemLp k 1 (lebesgue_value d)) (hfp : MemLp f ∞ (lebesgue_value d))
    (hF : Measurable (fun z : Point d × Point d => k z.2 * f (z.1-z.2))) :
    (∀ x, Integrable (fun y => k y * f (x-y)) (lebesgue_value d)) ∧
      Measurable (convolution d k f) ∧ MemLp (convolution d k f) ∞ (lebesgue_value d) ∧
      eLpNorm (convolution d k f) ∞ (lebesgue_value d) ≤
        eLpNorm k 1 (lebesgue_value d) * eLpNorm f ∞ (lebesgue_value d) := by
  letI : SigmaFinite (lebesgue_value d) := lebesgue_sigmaFinite d
  have hb (x : Point d) : eLpNorm (fun y => k y * f (x-y)) 1 (lebesgue_value d) ≤
      eLpNorm k 1 (lebesgue_value d) * eLpNorm f ∞ (lebesgue_value d) := by
    have H := eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top_of_pos
      (μ := lebesgue_value d) (φ := k) (f := fun y => f (x-y)) 1 zero_lt_one
    have he := eLpNorm_comp_measurePreserving (p := ∞) hfp.aestronglyMeasurable
      (measurePreserving_const_sub x)
    change eLpNorm (fun y => f (x-y)) ∞ (lebesgue_value d) = _ at he
    rw [he] at H
    exact H
  have hi (x : Point d) : Integrable (fun y => k y * f (x-y)) (lebesgue_value d) := by
    apply memLp_one_iff_integrable.mp
    exact (hb x).trans_lt (ENNReal.mul_lt_top hk1.eLpNorm_lt_top hfp.eLpNorm_lt_top)
  have hm : Measurable (convolution d k f) := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hbn : eLpNorm (convolution d k f) ∞ (lebesgue_value d) ≤
      eLpNorm k 1 (lebesgue_value d) * eLpNorm f ∞ (lebesgue_value d) := by
    rw [eLpNorm_exponent_top hm.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    exact Eventually.of_forall fun x =>
      (enorm_integral_le_lintegral_enorm _).trans
        ((lintegral_enorm_le_eLpNorm_one).trans (hb x))
  exact ⟨hi, hm, hbn.trans_lt (ENNReal.mul_lt_top hk1.eLpNorm_lt_top hfp.eLpNorm_lt_top), hbn⟩

/-- Full Young bound for every measurable representative in the completed
Lebesgue space, including both endpoints. -/
theorem young : Specs.D11.Ch11.ConvolutionBound.young := by
  intro d _ 𝕜 _ _ _ p hp
  let := lebesgueSpace_value d
  intro k f hk hf hk1 hfp
  obtain ⟨kB, hkB, hkkB⟩ := borel_version k hk
  obtain ⟨fB, hfB, hffB⟩ := borel_version f hf
  have hkBm : Measurable kB := hkB.mono (native_borel_le d) le_rfl
  have hfBm : Measurable fB := hfB.mono (native_borel_le d) le_rfl
  have hkB1 := hk1.ae_eq hkkB
  have hfBp := hfp.ae_eq hffB
  have hFB := borel_integrand_measurable hkB hfB
  have H := (representative_independence d 𝕜 k kB f fB hkkB hffB)
  have hy :
      (∀ᵐ x ∂lebesgue_value d, Integrable (fun y => kB y * fB (x-y)) (lebesgue_value d)) ∧
      Measurable (convolution d kB fB) ∧ MemLp (convolution d kB fB) p (lebesgue_value d) ∧
      eLpNorm (convolution d kB fB) p (lebesgue_value d) ≤
        eLpNorm kB 1 (lebesgue_value d) * eLpNorm fB p (lebesgue_value d) := by
    by_cases hpt : p = ∞
    · subst p
      obtain ⟨hi, hm, hmem, hb⟩ := young_top hkBm hfBm hkB1 hfBp hFB
      exact ⟨Eventually.of_forall hi, hm, hmem, hb⟩
    · exact young_finite hp hpt hkBm hfBm hkB1 hfBp hFB
  refine ⟨hy.1.mono (fun x hx => (H.1 x).mpr hx), ?_, ?_, ?_⟩
  · simpa only [H.2] using hy.2.1
  · simpa only [H.2] using hy.2.2.1
  · simpa only [H.2, eLpNorm_congr_ae hkkB, eLpNorm_congr_ae hffB] using hy.2.2.2

/-- Young's inequality expressed with actual quotient norms. -/
theorem quotient_bound : Specs.D11.Ch11.ConvolutionBound.quotient_bound := by
  intro d _ 𝕜 _ _ _ p _
  let := lebesgueSpace_value d
  intro k f hk hf hk1 hfp
  obtain ⟨_, _, hc, hb⟩ := young d 𝕜 p Fact.out k f hk hf hk1 hfp
  refine ⟨hc, ?_⟩
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hk1.ne hfp.ne) hb

/-- The resulting ordinary Lp class depends only on the two input classes. -/
theorem quotient_independence : Specs.D11.Ch11.ConvolutionBound.quotient_independence := by
  intro d _ 𝕜 _ p
  let := lebesgueSpace_value d
  intro k k' f f' hk hk' hf hf' hc hc' hkk hff
  apply MemLp.toLp_congr hc hc'
  have hke := (MemLp.toLp_eq_toLp_iff hk hk').mp hkk
  have hfe := (MemLp.toLp_eq_toLp_iff hf hf').mp hff
  exact EventuallyEq.of_eq (representative_independence d 𝕜 k k' f f' hke hfe).2

end Completed
end D11.Ch11.ConvolutionBound
