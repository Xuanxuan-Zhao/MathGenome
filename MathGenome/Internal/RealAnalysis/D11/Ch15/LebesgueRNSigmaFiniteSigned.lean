import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned
import MathGenome.Internal.RealAnalysis.D11.Ch14.ExtendedSignedVariant
import MathGenome.Internal.RealAnalysis.D11.Ch15.LebesgueDecompositionSigmaFinite
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNPositiveSigmaFinite

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch15.LebesgueRNSigmaFiniteSigned
open D11.Ch01.MeasureDefinitions D11.Ch14.ScalarInterfaces
open D11.Ch14.ExtendedSignedVariant

variable {X : Type u} [MeasurableSpace X]

/-- Extensionality is only over the original measurable sets. -/
theorem ext (ν η : ExtendedSignedMeasure X) (h : ∀ E, ν.value E = η.value E) : ν = η := by
  cases ν; cases η
  congr
  exact funext h

/-- Restriction commutes with both canonical Jordan measures. -/
theorem restrict_jordan (ν : ExtendedSignedMeasure X) (Z : Set X) (hZ : MeasurableSet Z) :
    positivePart (restrict ν Z hZ) = (positivePart ν).restrict Z ∧
    negativePart (restrict ν Z hZ) = (negativePart ν).restrict Z := by
  have hj := jordan_decomposition ν
  have h := jordan_unique (restrict ν Z hZ) _ _
    ⟨hj.1.mono_ac Measure.absolutelyContinuous_restrict
        Measure.absolutelyContinuous_restrict,
      hj.2.1.imp
        (fun h => ne_top_of_le_ne_top h (Measure.le_iff'.mp Measure.restrict_le_self univ))
        (fun h => ne_top_of_le_ne_top h (Measure.le_iff'.mp Measure.restrict_le_self univ)),
      fun E hE => by
        simpa only [restrict, Measure.restrict_apply hE] using hj.2.2 (E ∩ Z) (hE.inter hZ)⟩
  exact ⟨h.1.symm, h.2.symm⟩

theorem restrict_variation (ν : ExtendedSignedMeasure X) (Z : Set X) (hZ : MeasurableSet Z) :
    variation (restrict ν Z hZ) = (variation ν).restrict Z := by
  rw [variation, (restrict_jordan ν Z hZ).1, (restrict_jordan ν Z hZ).2,
    variation, Measure.restrict_add]

/-- A variation-null measurable set has zero signed value. -/
theorem value_zero_of_variation_zero (ν : ExtendedSignedMeasure X)
    (E : MeasurableDomain X) (hz : variation ν E.1 = 0) : ν.value E = 0 := by
  have hparts : positivePart ν E.1 = 0 ∧ negativePart ν E.1 = 0 := by
    simpa only [variation, Measure.add_apply, add_eq_zero] using hz
  rw [(jordan_decomposition ν).2.2 E.1 E.2, hparts.1, hparts.2]
  simp

theorem value_split (ν : ExtendedSignedMeasure X) (E : MeasurableDomain X)
    (Z : Set X) (hZ : MeasurableSet Z) :
    ν.value E = ν.value ⟨E.1 ∩ Z, E.2.inter hZ⟩ +
      ν.value ⟨E.1 ∩ Zᶜ, E.2.inter hZ.compl⟩ := by
  have h := value_union ν (E.1 ∩ Z) (E.1 ∩ Zᶜ) (E.2.inter hZ)
    (E.2.inter hZ.compl) (disjoint_compl_right.mono inter_subset_right inter_subset_right)
  simpa only [← inter_union_distrib_left, union_compl_self, inter_univ] using h

theorem value_inter_compl (ν : ExtendedSignedMeasure X) (E : MeasurableDomain X)
    (Z : Set X) (hZ : MeasurableSet Z) (hz : variation ν Z = 0) :
    ν.value E = ν.value ⟨E.1 ∩ Zᶜ, E.2.inter hZ.compl⟩ := by
  have hzero := value_zero_of_variation_zero ν ⟨E.1 ∩ Z,E.2.inter hZ⟩
    (measure_mono_null inter_subset_right hz)
  simpa only [hzero, zero_add] using value_split ν E Z hZ

/-- Positive decomposition of the variation supplies a single common null
support. Restrictions automatically inherit the globally omitted infinity. -/
theorem decomposition_exists :
    Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.decomposition_exists := by
  intro X _ μ _ ν hν
  let : SigmaFinite (variation ν) := hν
  obtain ⟨Z, hZ, hμZ, hac⟩ :=
    LebesgueDecompositionSigmaFinite.exists_null_support μ (variation ν)
  refine ⟨Z, hZ, hμZ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change SigmaFinite (variation (restrict ν Zᶜ hZ.compl))
    rw [restrict_variation]
    infer_instance
  · change SigmaFinite (variation (restrict ν Z hZ))
    rw [restrict_variation]
    infer_instance
  · intro E
    rcases ν.omitsInfinity with h | h
    · exact ⟨Or.inl (h _), Or.inr (h _)⟩
    · exact ⟨Or.inr (h _), Or.inl (h _)⟩
  · intro E
    simpa only [restrict, compl_compl] using value_split ν E Zᶜ hZ.compl
  · change variation (restrict ν Zᶜ hZ.compl) ≪ μ
    rwa [restrict_variation]
  · refine ⟨Z, hZ, ?_, hμZ⟩
    change variation (restrict ν Z hZ) Zᶜ = 0
    rw [restrict_variation, Measure.restrict_apply hZ.compl, compl_inter_self, measure_empty]

/-- On a common null support, every AC/singular decomposition is forced
pointwise; this argument never cancels infinite signed values. -/
theorem parts_from_null_support (μ : Measure X) (ν a s : ExtendedSignedMeasure X)
    (Z : Set X) (hZ : MeasurableSet Z) (hμZ : μ Z = 0)
    (hs : variation s Zᶜ = 0) (heq : ∀ E, ν.value E = a.value E + s.value E)
    (ha : variation a ≪ μ) : a = restrict ν Zᶜ hZ.compl ∧ s = restrict ν Z hZ := by
  constructor
  · apply ext; intro E
    change a.value E = ν.value ⟨E.1 ∩ Zᶜ,E.2.inter hZ.compl⟩
    rw [heq]
    have hz := value_zero_of_variation_zero s ⟨E.1 ∩ Zᶜ,E.2.inter hZ.compl⟩
      (measure_mono_null inter_subset_right hs)
    rw [hz, add_zero]
    exact value_inter_compl a E Z hZ (ha hμZ)
  · apply ext; intro E
    change s.value E = ν.value ⟨E.1 ∩ Z,E.2.inter hZ⟩
    rw [heq]
    have hz := value_zero_of_variation_zero a ⟨E.1 ∩ Z,E.2.inter hZ⟩
      (measure_mono_null inter_subset_right (ha hμZ))
    rw [hz, zero_add]
    simpa only [compl_compl] using value_inter_compl s E Zᶜ hZ.compl hs

theorem decomposition_unique :
    Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.decomposition_unique := by
  intro X _ μ ν a s a' s' h h'
  obtain ⟨Z, hZ, hsZ, hμZ⟩ := h.2.2.2.2.2
  obtain ⟨B, hB, hsB, hμB⟩ := h'.2.2.2.2.2
  have hm : MeasurableSet (Z ∪ B) := hZ.union hB
  have hn : μ (Z ∪ B) = 0 := measure_union_null hμZ hμB
  have h1 := parts_from_null_support μ ν a s (Z ∪ B) hm hn
    (measure_mono_null (compl_subset_compl.mpr subset_union_left) hsZ)
    h.2.2.2.1 h.2.2.2.2.1
  have h2 := parts_from_null_support μ ν a' s' (Z ∪ B) hm hn
    (measure_mono_null (compl_subset_compl.mpr subset_union_right) hsB)
    h'.2.2.2.1 h'.2.2.2.2.1
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

/-- RN for the AC variation, followed by the Hahn sign, avoids subtraction
of infinite pointwise densities. -/
theorem density_exists : Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.density_exists := by
  intro X _ μ _ a hva hac
  classical
  let : SigmaFinite (variation a) := hva
  have hs := (jordan_decomposition a).1
  let S := hs.nullSet
  have hS : MeasurableSet S := hs.measurableSet_nullSet
  obtain ⟨h, hm, hn, hrep⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_real μ (variation a) hac
  have hd : μ.withDensity (fun x => ENNReal.ofReal (h x)) = variation a := by
    ext E hE
    rw [withDensity_apply _ hE, hrep E hE]
    exact (Ch05.NonnegativeIntegral.integral_eq_lintegral _ _).symm
  have hp : (variation a).restrict Sᶜ = positivePart a := by
    rw [variation, Measure.restrict_add, hs.restrict_compl_nullSet',
      hs.restrict_compl_nullSet, add_zero]
  have hn' : (variation a).restrict S = negativePart a := by
    rw [variation, Measure.restrict_add, hs.restrict_nullSet,
      hs.restrict_nullSet', zero_add]
  let f : X → ℝ := S.piecewise (fun x => -h x) h
  have hfm : Measurable f := hm.neg.piecewise hS hm
  have hfp : (fun x => ENNReal.ofReal (f x)) = Sᶜ.indicator (fun x => ENNReal.ofReal (h x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp [f, hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hn x))]
    · simp [f, hx]
  have hfn : (fun x => ENNReal.ofReal (-f x)) = S.indicator (fun x => ENNReal.ofReal (h x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp [f, hx]
    · simp [f, hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hn x))]
  have hpos : μ.withDensity (fun x => ENNReal.ofReal (f x)) = positivePart a := by
    rw [hfp, withDensity_indicator hS.compl, ← restrict_withDensity hS.compl, hd, hp]
  have hneg : μ.withDensity (fun x => ENNReal.ofReal (-f x)) = negativePart a := by
    rw [hfn, withDensity_indicator hS, ← restrict_withDensity hS, hd, hn']
  have hpint (E : Set X) (hE : MeasurableSet E) :
      ∫⁻ x in E, ENNReal.ofReal (f x) ∂μ = positivePart a E := by
    rw [← withDensity_apply _ hE, hpos]
  have hnint (E : Set X) (hE : MeasurableSet E) :
      ∫⁻ x in E, ENNReal.ofReal (-f x) ∂μ = negativePart a E := by
    rw [← withDensity_apply _ hE, hneg]
  refine ⟨f, hfm, ?_, ?_⟩
  · have hfinite := (jordan_decomposition a).2.1
    have hpint' := hpint univ MeasurableSet.univ
    have hnint' := hnint univ MeasurableSet.univ
    simp only [Measure.restrict_univ] at hpint' hnint'
    rwa [hpint', hnint']
  · intro E hE
    rw [hpint E hE, hnint E hE]
    exact (jordan_decomposition a).2.2 E hE

/-- A density with one finite sign integral has precisely these Jordan
measures, by disjointness of its positive and negative supports. -/
theorem density_jordan (μ : Measure X) (a : ExtendedSignedMeasure X) (f : X → ℝ)
    (hf : Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.Density μ a f) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) = positivePart a ∧
    μ.withDensity (fun x => ENNReal.ofReal (-f x)) = negativePart a := by
  apply jordan_unique a
  refine ⟨withDensity_ofReal_mutuallySingular hf.1, ?_, ?_⟩
  · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hf.2.1
  · intro E hE
    simpa only [withDensity_apply _ hE] using hf.2.2 E hE

theorem real_parts (t : ℝ) :
    t = (ENNReal.ofReal t).toReal - (ENNReal.ofReal (-t)).toReal := by
  by_cases ht : 0 ≤ t
  · simp [ENNReal.toReal_ofReal ht, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr ht)]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    simp [ENNReal.ofReal_eq_zero.mpr ht', ENNReal.toReal_ofReal (neg_nonneg.mpr ht')]

theorem density_unique : Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.density_unique := by
  intro X _ μ _ a _ f g hf hg
  have hfj := density_jordan μ a f hf
  have hgj := density_jordan μ a g hg
  have hp := (withDensity_eq_iff_of_sigmaFinite hf.1.ennreal_ofReal.aemeasurable
    hg.1.ennreal_ofReal.aemeasurable).mp (hfj.1.trans hgj.1.symm)
  have hn := (withDensity_eq_iff_of_sigmaFinite hf.1.neg.ennreal_ofReal.aemeasurable
    hg.1.neg.ennreal_ofReal.aemeasurable).mp (hfj.2.trans hgj.2.symm)
  filter_upwards [hp, hn] with x hpx hnx
  change ENNReal.ofReal (-f x) = ENNReal.ofReal (-g x) at hnx
  calc
    f x = (ENNReal.ofReal (f x)).toReal - (ENNReal.ofReal (-f x)).toReal := real_parts _
    _ = (ENNReal.ofReal (g x)).toReal - (ENNReal.ofReal (-g x)).toReal := by rw [hpx, hnx]
    _ = g x := (real_parts _).symm

theorem absolute_parts (t : ℝ) :
    ENNReal.ofReal |t| = ENNReal.ofReal t + ENNReal.ofReal (-t) := by
  by_cases ht : 0 ≤ t
  · simp [abs_of_nonneg ht, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr ht)]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    simp [abs_of_nonpos ht', ENNReal.ofReal_eq_zero.mpr ht']

theorem density_variation : Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.density_variation := by
  intro X _ μ a f hf E hE
  have hj := density_jordan μ a f hf
  change (positivePart a + negativePart a) E = _
  rw [Measure.add_apply, ← hj.1, ← hj.2, withDensity_apply _ hE, withDensity_apply _ hE,
    ← lintegral_add_left hf.1.ennreal_ofReal]
  exact lintegral_congr fun x => (absolute_parts (f x)).symm

theorem density_local_integrable :
    Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.density_local_integrable := by
  intro X _ μ a f hf E hE hfinite
  apply (integrable_indicator_iff hE).2
  refine ⟨hf.1.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [density_variation μ a f hf E hE] at hfinite
  simpa only [Real.norm_eq_abs] using hfinite

theorem ac_singular_part_zero :
    Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.ac_singular_part_zero := by
  intro X _ μ ν a s h hac E
  obtain ⟨Z, hZ, hsZ, hμZ⟩ := h.2.2.2.2.2
  have hp := parts_from_null_support μ ν a s Z hZ hμZ hsZ h.2.2.2.1 h.2.2.2.2.1
  rw [hp.2]
  exact value_zero_of_variation_zero ν ⟨E.1 ∩ Z,E.2.inter hZ⟩
    (measure_mono_null inter_subset_right (hac hμZ))

/-- Assemble the conclusions for the same decomposition and representative. -/
theorem lebesgue_rn_sigmafinite_signed :
    Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.lebesgue_rn_sigmafinite_signed := by
  intro X _ μ _ ν hν
  obtain ⟨Z, hZ, _, hdec⟩ := decomposition_exists μ ν
  let a := restrict ν Zᶜ hZ.compl
  let s := restrict ν Z hZ
  let : SigmaFinite (Specs.D11.Ch14.ExtendedSignedVariant.variation_value a) := hdec.1
  obtain ⟨f, hf⟩ := density_exists μ a hdec.2.2.2.2.1
  refine ⟨a, s, hdec, ?_, f, hf, ?_, ?_, ?_⟩
  · intro a' s' h'
    exact decomposition_unique μ ν a' s' a s h' hdec
  · intro g hg
    exact density_unique μ a f g hf hg
  · exact density_local_integrable μ a f hf
  · exact ac_singular_part_zero μ ν a s hdec

end D11.Ch15.LebesgueRNSigmaFiniteSigned
