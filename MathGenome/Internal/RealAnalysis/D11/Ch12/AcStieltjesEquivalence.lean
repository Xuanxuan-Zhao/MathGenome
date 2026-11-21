import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcStieltjesEquivalence
import MathGenome.Internal.RealAnalysis.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcBasic
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcGlobalVariation
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcPositiveStieltjesNull
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNSignedComplex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch12.AcStieltjesEquivalence
open ScalarStieltjesCorrespondence

/-- Small-set control of one L¹ norm gives a single modulus on all of ℝ. -/
theorem density_ac : Specs.D11.Ch12.AcStieltjesEquivalence.density_ac := by
  intro K _ F f hf hF ε hε
  obtain ⟨η, hη, hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    hf.hasFiniteIntegral.ne (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨δ, _, hδ, hδη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  refine ⟨δ, ENNReal.ofReal_pos.mp hδ, ?_⟩
  intro n u v huv _ hdis hlength
  let E : Fin n → Set ℝ := fun j => Ioc (u j) (v j)
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    simpa only [E, Ioc_disjoint_Ioc, Ioo_disjoint_Ioo] using hdis hij
  have hmass : volume (⋃ j, E j) < η := by
    calc
      _ ≤ ∑ j, volume (E j) := measure_iUnion_fintype_le volume E
      _ = ENNReal.ofReal (∑ j, (v j - u j)) := by
        simp only [E, Real.volume_Ioc]
        exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => sub_nonneg.mpr (huv j).le)).symm
      _ < η := (ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp hδ)).mpr hlength |>.trans hδη
  have hsum : ENNReal.ofReal (∑ j, ‖F (v j) - F (u j)‖) ≤
      ∫⁻ t in ⋃ j, E j, ‖f t‖ₑ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _),
      lintegral_iUnion (fun _ => measurableSet_Ioc) hEd, tsum_fintype]
    apply Finset.sum_le_sum
    intro j _
    rw [ofReal_norm, hF, hF, intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn,
      intervalIntegral.integral_of_le (huv j).le]
    exact enorm_integral_le_lintegral_enorm _
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp (hsum.trans_lt (hsmall _ hmass))

/-- Differentiate the cumulative integral using the global interval
Lebesgue differentiation theorem, with no exceptional x in reconstruction. -/
theorem density_derivative : Specs.D11.Ch12.AcStieltjesEquivalence.density_derivative := by
  intro K _ F f hf hF
  have hformula (x : ℝ) : F x = (∫ t in Iic (0 : ℝ), f t) + ∫ t in (0 : ℝ)..x, f t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn, hF]
    abel
  have hd : ∀ᵐ x ∂volume, HasDerivAt F (f x) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf.locallyIntegrable] with x hx
    have heq : F = fun x => (∫ t in Iic (0 : ℝ), f t) + ∫ t in (0 : ℝ)..x, f t :=
      funext hformula
    rw [heq]
    exact (hx 0).const_add _
  have heq : deriv F =ᵐ[volume] f := hd.mono (fun _ hx => hx.deriv)
  refine ⟨hd, hf.congr heq.symm, ?_⟩
  intro x
  rw [hF x]
  exact integral_congr_ae (ae_restrict_of_ae heq.symm)

/-- Equality to an integrable density implies the required variation-null
condition. Tests are on the original Borel domain. -/
lemma variation_ac_of_density {K : Type*} [RCLike K]
    (ν : VectorMeasure ℝ K) (f : ℝ → K)
    (hr : ∀ E, MeasurableSet E → ν E = ∫ t in E, f t) :
    ν.variation ≪ volume := by
  apply (Ch15.AbsoluteContinuity.scalar_iff ν volume).mpr
  intro E hE hzero
  rw [hr E hE, Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]

/-- Real RN relative to sigma-finite Borel Lebesgue measure. -/
theorem measure_density_real : Specs.D11.Ch12.AcStieltjesEquivalence.measure_density_real := by
  intro F _
  constructor
  · intro hac
    obtain ⟨f, hm, hi, hr, _⟩ := Ch15.RNSignedComplex.rn_signed volume
      (stieltjesMeasure F) hac
    exact ⟨f, hm, hi, hr⟩
  · rintro ⟨f, _, _, hr⟩
    exact variation_ac_of_density _ f hr

/-- Complex RN has the same hypotheses and Borel-set conclusions. -/
theorem measure_density_complex : Specs.D11.Ch12.AcStieltjesEquivalence.measure_density_complex := by
  intro F _
  constructor
  · intro hac
    obtain ⟨f, hm, hi, hr, _⟩ := Ch15.RNSignedComplex.rn_complex volume
      (stieltjesMeasure F) hac
    exact ⟨f, hm, hi, hr⟩
  · rintro ⟨f, _, _, hr⟩
    exact variation_ac_of_density _ f hr

/-- Assembly of the density direction, generic in the scalar field. -/
lemma measure_ac_of_density {K : Type*} [RCLike K]
    (F : ℝ → K) (hF : NBV F) (f : ℝ → K) (hi : Integrable f volume)
    (hr : ∀ E, MeasurableSet E → stieltjesMeasure F E = ∫ t in E, f t) :
    AbsolutelyContinuous F ∧ Integrable (deriv F) volume ∧
      (∀ᵐ x ∂volume, HasDerivAt F (deriv F x) x) ∧
      ∀ x, F x = ∫ t in Iic x, deriv F t := by
  have hcum (x : ℝ) : F x = ∫ t in Iic x, f t := by
    rw [← congrFun (cumulative_measure F hF) x]
    exact hr _ measurableSet_Iic
  obtain ⟨hd, hdi, hrec⟩ := density_derivative F f hi hcum
  refine ⟨density_ac F f hi hcum, hdi, ?_, hrec⟩
  filter_upwards [hd] with x hx
  simpa only [hx.deriv] using hx

theorem measure_ac_real : Specs.D11.Ch12.AcStieltjesEquivalence.measure_ac_real := by
  intro F hF hac
  obtain ⟨f, _, hi, hr⟩ := (measure_density_real F hF).mp hac
  exact measure_ac_of_density F hF f hi hr

theorem measure_ac_complex : Specs.D11.Ch12.AcStieltjesEquivalence.measure_ac_complex := by
  intro F hF hac
  obtain ⟨f, _, hi, hr⟩ := (measure_density_complex F hF).mp hac
  exact measure_ac_of_density F hF f hi hr

/-- The genuine initial variation is globally AC. Its positive Stieltjes
measure is exactly the scalar total variation, so the positive null-set
criterion proves the forward implication without assuming a density. -/
theorem ac_measure : Specs.D11.Ch12.AcStieltjesEquivalence.ac_measure := by
  intro K _ F hF hAC
  obtain ⟨hACV, hV, heq⟩ := AcGlobalVariation.global_variation F hF hAC
  change (stieltjesMeasure F).variation ≪ volume
  rw [heq]
  exact AcPositiveStieltjesNull.absolutely_continuous _ hV hACV

/-- Full real-line equivalence, with integrable classical derivative and
cumulative reconstruction at every point. -/
theorem global_real : Specs.D11.Ch12.AcStieltjesEquivalence.global_real := by
  intro F hF
  refine ⟨⟨ac_measure F hF, fun h => (measure_ac_real F hF h).1⟩, ?_⟩
  intro hAC
  exact (measure_ac_real F hF (ac_measure F hF hAC)).2

/-- The complex statement retains total variation absolute continuity. -/
theorem global_complex : Specs.D11.Ch12.AcStieltjesEquivalence.global_complex := by
  intro F hF
  refine ⟨⟨ac_measure F hF, fun h => (measure_ac_complex F hF h).1⟩, ?_⟩
  intro hAC
  exact (measure_ac_complex F hF (ac_measure F hF hAC)).2

/-- Clamping preserves the uniform disjoint-interval modulus, including
intervals crossing an endpoint and intervals collapsing to a point. -/
lemma compactNormalization_ac_iff {K : Type*} [RCLike K]
    (F : ℝ → K) {a b : ℝ} (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval F a b ↔
      AbsolutelyContinuous (NormalizedStieltjes.compactNormalization F a b) := by
  let c : ℝ → ℝ := fun x => max a (min b x)
  have hcm (x : ℝ) : c x ∈ Icc a b := NormalizedStieltjes.clamp_mem hab x
  have hcmon : Monotone c := NormalizedStieltjes.clamp_mono a b
  have hsub (u v : ℝ) : Ioo (c u) (c v) ⊆ Ioo u v := by
    intro x hx
    dsimp [c] at hx
    simp only [mem_Ioo] at hx ⊢
    constructor <;> grind
  constructor
  · intro hF ε hε
    obtain ⟨δ, hδ, hd⟩ := hF ε hε
    refine ⟨δ, hδ, ?_⟩
    intro n u v huv _ hdis hlen
    have hlen' : (∑ j, (c (v j) - c (u j))) < δ := by
      apply lt_of_le_of_lt (Finset.sum_le_sum (fun j _ => ?_)) hlen
      have h := (huv j).le
      dsimp [c]
      grind
    have h := AcBasic.finite_family_le hd (c ∘ u) (c ∘ v)
      (fun j => hcmon (huv j).le) (fun j => ⟨hcm _, hcm _⟩)
      (fun i j hij => (hdis hij).mono (hsub _ _) (hsub _ _)) hlen'
    simpa only [NormalizedStieltjes.compactNormalization, Function.comp_apply,
      sub_sub_sub_cancel_right] using h
  · intro hG ε hε
    obtain ⟨δ, hδ, hd⟩ := hG ε hε
    refine ⟨δ, hδ, ?_⟩
    intro n u v huv hmem hdis hlen
    have h := hd n u v huv (fun j => ⟨mem_univ _, mem_univ _⟩) hdis hlen
    simpa only [(NormalizedStieltjes.compact_values F hab).2.1 _ (hmem _).1,
      (NormalizedStieltjes.compact_values F hab).2.1 _ (hmem _).2,
      sub_sub_sub_cancel_right] using h

/-- AC provides exactly the continuous normalized extension, so its Stieltjes
measure has no atoms anywhere, including at a and b. -/
lemma compactNormalization_properties {K : Type*} [RCLike K]
    (F : ℝ → K) {a b : ℝ} (hab : a < b)
    (hF : AbsolutelyContinuousOnInterval F a b) :
    NBV (NormalizedStieltjes.compactNormalization F a b) ∧
      Continuous (NormalizedStieltjes.compactNormalization F a b) ∧
      ∀ x, stieltjesMeasure (NormalizedStieltjes.compactNormalization F a b) {x} = 0 := by
  have hc := (AcBasic.uniformContinuousOn hab.le hF).continuousOn
  obtain ⟨hn, hcont, _⟩ := NormalizedStieltjes.compact_continuous F hab (AcBasic.bv hab.le hF) hc
  refine ⟨hn, hcont, ?_⟩
  intro x
  rw [NormalizedStieltjes.atom_formula _ hn, (hcont.continuousAt.continuousWithinAt).leftLim_eq, sub_self]

/-- Transfer a cumulative L¹ representation of the normalized constant
extension back to the original function, retaining both endpoint values. -/
lemma compact_density_reconstruction {K : Type*} [RCLike K]
    (F f : ℝ → K) {a b : ℝ} (hab : a < b) (hf : Integrable f volume)
    (hr : ∀ x, NormalizedStieltjes.compactNormalization F a b x = ∫ t in Iic x, f t) :
    IntegrableOn (deriv F) (Icc a b) ∧
      (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (deriv F x) x) ∧
      ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, deriv F t := by
  let G := NormalizedStieltjes.compactNormalization F a b
  have hvalues (x : ℝ) (hx : x ∈ Icc a b) : G x = F x - F a :=
    (NormalizedStieltjes.compact_values F hab.le).2.1 x hx
  have hd := (density_derivative G f hf hr).1
  have hFd : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (f x) x := by
    filter_upwards [hd] with x hx hxi
    apply (hx.add_const (F a)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
    rw [hvalues y (Ioo_subset_Icc_self hy)]
    abel
  have heq : deriv F =ᵐ[volume.restrict (Icc a b)] f := by
    rw [Filter.EventuallyEq, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hFd] with x hx hxi
    exact (hx hxi).deriv
  refine ⟨hf.integrableOn.congr heq.symm, ?_, ?_⟩
  · filter_upwards [hFd] with x hx hxi
    simpa only [(hx hxi).deriv] using hx hxi
  · intro x hx
    have hcongr : (∫ t in a..x, deriv F t) = ∫ t in a..x, f t := by
      apply intervalIntegral.integral_congr_ae
      have heq' := (ae_restrict_iff' measurableSet_Icc).mp heq
      filter_upwards [heq'] with t ht htx
      apply ht
      rw [uIoc_of_le hx.1] at htx
      exact ⟨htx.1.le, htx.2.trans hx.2⟩
    rw [hcongr, ← intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn,
      ← hr x, ← hr a]
    change F x = F a + (G x - G a)
    rw [hvalues x hx, hvalues a ⟨le_rfl, hab.le⟩]
    abel

/-- Transfer the complete global theorem through the exact normalized
constant extension. The derivative of the extension itself is an L¹ density,
so no separate density assumption is needed in the compact conclusion. -/
lemma compact_of_measure_ac {K : Type*} [RCLike K]
    (hreverse : ∀ G : ℝ → K, NBV G → (stieltjesMeasure G).variation ≪ volume →
      AbsolutelyContinuous G ∧ Integrable (deriv G) volume ∧
        (∀ᵐ x ∂volume, HasDerivAt G (deriv G x) x) ∧
        ∀ x, G x = ∫ t in Iic x, deriv G t) :
    Specs.D11.Ch12.AcStieltjesEquivalence.compact_statement K := by
  intro F a b hab
  let G := NormalizedStieltjes.compactNormalization F a b
  have hforward (hAC : AbsolutelyContinuousOnInterval F a b) :
      NBV G ∧ Continuous G ∧ (stieltjesMeasure G).variation ≪ volume := by
    obtain ⟨hn, hc, _⟩ := compactNormalization_properties F hab hAC
    exact ⟨hn, hc, ac_measure G hn ((compactNormalization_ac_iff F hab.le).mp hAC)⟩
  refine ⟨⟨hforward, ?_⟩, ?_⟩
  · rintro ⟨hn, _, hm⟩
    exact (compactNormalization_ac_iff F hab.le).mpr (hreverse G hn hm).1
  · intro hAC
    obtain ⟨hn, _, hm⟩ := hforward hAC
    obtain ⟨_, hi, _, hr⟩ := hreverse G hn hm
    exact ⟨(compactNormalization_properties F hab hAC).2.2,
      compact_density_reconstruction F (deriv G) hab hi hr⟩

/-- Compact real equivalence, absence of endpoint atoms, and the
every-point integral formula for the original function. -/
theorem compact_real : Specs.D11.Ch12.AcStieltjesEquivalence.compact_real :=
  compact_of_measure_ac measure_ac_real

/-- Compact complex equivalence with the same endpoint convention. -/
theorem compact_complex : Specs.D11.Ch12.AcStieltjesEquivalence.compact_complex :=
  compact_of_measure_ac measure_ac_complex

end D11.Ch12.AcStieltjesEquivalence
