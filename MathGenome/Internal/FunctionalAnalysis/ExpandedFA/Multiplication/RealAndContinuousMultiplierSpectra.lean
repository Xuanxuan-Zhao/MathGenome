import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.RealAndContinuousMultiplierSpectra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.LpMultiplierSpectrum

noncomputable section
open MeasureTheory Filter
attribute [local instance] Measure.Subtype.measureSpace
open scoped ENNReal Topology
namespace ExpandedFA.Multiplication
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A real symbol cannot have a nonreal point in its essential range. -/
theorem real_essentialRange_subset (a : Ω → ℝ) :
    multiplierEssentialRange μ (fun x => (a x : ℂ)) ⊆ Set.range Complex.ofReal := by
  intro z hz
  have hi : z.im = 0 := by
    by_contra h
    apply ((not_mem_essentialRange_iff (fun x => (a x : ℂ)) z).mpr ?_) hz
    refine ⟨|z.im|, abs_pos.mpr h, Eventually.of_forall fun x => ?_⟩
    simpa using Complex.abs_im_le_norm (z - (a x : ℂ))
  exact ⟨z.re, Complex.ext (by simp) (by simp [hi])⟩

theorem real_multiplier_spectrum : RealAndContinuousMultiplierSpectraSpec.RealSpectrum := by
  intro Ω _ μ hμ p _ hp1 hp a ha
  rw [multiplier_real_spectrum μ hμ p hp1 hp a ha]
  exact real_essentialRange_subset a

/-- An a.e. real interval also bounds the ordinary complex essential range. -/
theorem real_essentialRange_subset_interval (a : Ω → ℝ) (α β : ℝ)
    (hl : ∀ᵐ x ∂μ, α ≤ a x) (hu : ∀ᵐ x ∂μ, a x ≤ β) :
    multiplierEssentialRange μ (fun x => (a x : ℂ)) ⊆
      Complex.ofReal '' Set.Icc α β := by
  intro z hz
  obtain ⟨r, rfl⟩ := real_essentialRange_subset a hz
  refine ⟨r, ⟨?_, ?_⟩, rfl⟩
  · by_contra h
    have hr : r < α := lt_of_not_ge h
    apply ((not_mem_essentialRange_iff (fun x => (a x : ℂ)) (r : ℂ)).mpr ?_) hz
    refine ⟨α - r, sub_pos.mpr hr, ?_⟩
    filter_upwards [hl] with x hx
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : r - a x ≤ 0)]
    linarith
  · by_contra h
    have hr : β < r := lt_of_not_ge h
    apply ((not_mem_essentialRange_iff (fun x => (a x : ℂ)) (r : ℂ)).mpr ?_) hz
    refine ⟨r - β, sub_pos.mpr hr, ?_⟩
    filter_upwards [hu] with x hx
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ r - a x)]
    linarith

/-- Finite essential endpoints are themselves essential values. -/
theorem real_essentialRange_endpoints [NeZero μ] (a : Ω → ℝ)
    (hl : IsBoundedUnder (· ≥ ·) (ae μ) a)
    (hu : IsBoundedUnder (· ≤ ·) (ae μ) a) :
    ((essInf a μ : ℝ) : ℂ) ∈ multiplierEssentialRange μ (fun x => (a x : ℂ)) ∧
    ((essSup a μ : ℝ) : ℂ) ∈ multiplierEssentialRange μ (fun x => (a x : ℂ)) := by
  constructor
  · by_contra h
    obtain ⟨c, hc, hb⟩ :=
      (not_mem_essentialRange_iff (fun x => (a x : ℂ)) _).mp h
    have hnew : ∀ᵐ x ∂μ, essInf a μ + c ≤ a x := by
      filter_upwards [hb, ae_essInf_le hl] with x hx ha
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr ha)] at hx
      linarith
    have hle := le_essInf_of_ae_le (essInf a μ + c) hnew hu.isCoboundedUnder_ge
    linarith
  · by_contra h
    obtain ⟨c, hc, hb⟩ :=
      (not_mem_essentialRange_iff (fun x => (a x : ℂ)) _).mp h
    have hnew : ∀ᵐ x ∂μ, a x ≤ essSup a μ - c := by
      filter_upwards [hb, ae_le_essSup hu] with x hx ha
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ha)] at hx
      linarith
    have hle := essSup_le_of_ae_le (essSup a μ - c) hnew hl.isCoboundedUnder_le
    linarith

theorem bounded_real_multiplier_spectrum :
    RealAndContinuousMultiplierSpectraSpec.BoundedRealSpectrum := by
  intro Ω _ μ hμ p _ hp1 hp _ a ha hbd
  have hμne : μ ≠ 0 := by
    intro hz
    obtain ⟨f, hf⟩ : ∃ f : Lp ℂ p μ, f ≠ 0 := exists_ne 0
    apply hf
    apply Lp.ext
    rw [show ae μ = ⊥ from ae_eq_bot.mpr hz]
    exact Filter.eventually_bot
  have : NeZero μ := ⟨hμne⟩
  have hnorm := ae_le_lpNorm_exponent_top hbd
  have hl : IsBoundedUnder (· ≥ ·) (ae μ) a :=
    ⟨-lpNorm a ∞ μ, hnorm.mono fun x hx =>
      (neg_le_neg hx).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le (a x))⟩
  have hu : IsBoundedUnder (· ≤ ·) (ae μ) a :=
    ⟨lpNorm a ∞ μ, hnorm.mono fun x hx => (le_abs_self (a x)).trans hx⟩
  have hi := ae_essInf_le hl
  have hs := ae_le_essSup hu
  rw [multiplier_real_spectrum μ hμ p hp1 hp a ha]
  obtain ⟨hα, hβ⟩ := real_essentialRange_endpoints a hl hu
  have hI := real_essentialRange_subset_interval a (essInf a μ) (essSup a μ) hi hs
  refine ⟨hα, hβ, hI, ?_⟩
  constructor
  · intro heq
    have hα0 : essInf a μ = 0 := by
      have : ((essInf a μ : ℝ) : ℂ) = 0 := by simpa [heq] using hα
      exact Complex.ofReal_eq_zero.mp this
    have hβ0 : essSup a μ = 0 := by
      have : ((essSup a μ : ℝ) : ℂ) = 0 := by simpa [heq] using hβ
      exact Complex.ofReal_eq_zero.mp this
    filter_upwards [hi, hs] with x hx hy
    change a x = 0
    rw [hα0] at hx
    rw [hβ0] at hy
    exact le_antisymm hy hx
  · intro hae
    have hα0 : essInf a μ = 0 := by
      rw [essInf_congr_ae hae]
      exact essInf_const 0 hμne
    have hβ0 : essSup a μ = 0 := by
      rw [essSup_congr_ae hae]
      exact essSup_const 0 hμne
    apply Set.Subset.antisymm
    · simpa [hα0, hβ0] using hI
    · simpa [hα0] using Set.singleton_subset_iff.mpr hα

/-- A nonzero real Lp space has a nonzero natural complexification. -/
theorem lp_complex_nontrivial_of_real (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [Nontrivial (Lp ℝ p μ)] : Nontrivial (Lp ℂ p μ) := by
  obtain ⟨u, hu⟩ : ∃ u : Lp ℝ p μ, u ≠ 0 := exists_ne 0
  obtain ⟨f, _, hr, _⟩ := (lp_ambient_complexification μ p).2 u 0
  apply nontrivial_of_ne f 0
  intro hf
  apply hu
  rw [hf] at hr
  exact hr.symm.trans ((Complex.reCLM.compLpL p μ).map_zero)

theorem bounded_real_space_multiplier_spectrum :
    RealAndContinuousMultiplierSpectraSpec.RealSpaceBoundedSpectrum := by
  intro Ω _ μ hμ p _ hp1 hp _ a ha hbd
  have : Nontrivial (Lp ℂ p μ) := lp_complex_nontrivial_of_real p
  exact bounded_real_multiplier_spectrum μ hμ p hp1 hp a ha hbd

/-- Sigma-finite measures satisfy the finite-positive-subset interface. -/
theorem semifinite_of_sigmaFinite (μ : Measure Ω) [SigmaFinite μ] : Semifinite μ := by
  intro E hE hpos
  obtain ⟨F, hF, hFE, hFpos, hFtop⟩ := Measure.exists_subset_measure_lt_top hE hpos
  exact ⟨F, hFE, hF, hFpos, hFtop⟩

/-- For full-support measures the essential range of a continuous symbol is
exactly the closure of its range. Neither boundedness nor nonemptiness is needed. -/
theorem continuous_essentialRange [TopologicalSpace Ω] [BorelSpace Ω]
    [μ.IsOpenPosMeasure] (a : Ω → ℂ) (ha : Continuous a) :
    multiplierEssentialRange μ a = closure (Set.range a) := by
  apply Set.Subset.antisymm
  · intro z hz
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hpos := hz ε hε
    have hne : {x | ‖a x - z‖ < ε}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hpos
      exact (lt_irrefl _ hpos)
    obtain ⟨x, hx⟩ := hne
    exact ⟨a x, ⟨x, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hx⟩
  · apply closure_minimal
    · rintro _ ⟨x, rfl⟩ ε hε
      have hopen : IsOpen {y | ‖a y - a x‖ < ε} :=
        isOpen_lt (ha.sub continuous_const).norm continuous_const
      exact hopen.measure_pos μ ⟨x, by simpa using hε⟩
    · exact multiplier_essentialRange_closed μ a

/-- Continuous symbols over a full-support semifinite measure. -/
theorem continuous_multiplier_spectrum [TopologicalSpace Ω] [BorelSpace Ω]
    [μ.IsOpenPosMeasure] (hμ : Semifinite μ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (a : Ω → ℂ) (ha : Continuous a) :
    multiplierSpectrum μ p a = closure (Set.range a) := by
  rw [multiplier_spectrum μ hμ p hp1 hp a ha.measurable,
    continuous_essentialRange a ha]

theorem continuous_euclidean_multiplier_spectrum :
    RealAndContinuousMultiplierSpectraSpec.ContinuousSpectrum := by
  intro n U hU _hne p _ hp1 hp a ha
  have : (volume : Measure U).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume hU.isOpenEmbedding_subtypeVal
  have : SigmaFinite (volume : Measure U) := by
    apply SigmaFinite.of_map (volume : Measure U) measurable_subtype_coe.aemeasurable
    rw [Measure.Subtype.volume_def,
      (MeasurableEmbedding.subtype_coe hU.measurableSet).map_comap]
    infer_instance
  exact continuous_multiplier_spectrum (semifinite_of_sigmaFinite volume) p hp1 hp a ha

theorem logistic_range : RealAndContinuousMultiplierSpectraSpec.LogisticRange :=
  Real.range_sigmoid

theorem logistic_multiplier_spectrum : RealAndContinuousMultiplierSpectraSpec.LogisticSpectrum := by
  intro p _ hp1 hp
  change multiplierSpectrum volume p (fun x : ℝ => (Real.sigmoid x : ℂ)) = _
  rw [continuous_multiplier_spectrum (semifinite_of_sigmaFinite volume) p hp1 hp
    (fun x : ℝ => (Real.sigmoid x : ℂ))
    (Complex.continuous_ofReal.comp continuous_sigmoid)]
  change closure (Set.range (Complex.ofReal ∘ Real.sigmoid)) = _
  rw [Set.range_comp Complex.ofReal Real.sigmoid, Real.range_sigmoid,
    Complex.isometry_ofReal.isClosedEmbedding.closure_image_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]

end ExpandedFA.Multiplication
