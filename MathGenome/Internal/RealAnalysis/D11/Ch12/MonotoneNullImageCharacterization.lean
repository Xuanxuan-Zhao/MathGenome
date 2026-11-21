import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.MonotoneNullImageCharacterization
import MathGenome.Internal.RealAnalysis.D11.Ch03.PositiveOuterNonmeasurable
import Mathlib.MeasureTheory.Measure.Regular
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcStieltjesEquivalence

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open scoped ENNReal

namespace D11.Ch12.MonotoneNullImageCharacterization

/-- The selected preimage is a subset of a null set. No measurability of the
preimage of the nonmeasurable target set is used. -/
theorem measurableImages_implies_nullImages :
    Specs.D11.Ch12.MonotoneNullImageCharacterization.measurableImages_implies_nullImages := by
  intro F s hM N hNs hN
  by_contra hFN
  obtain ⟨B, hB, hnB⟩ :=
    Ch03.PositiveOuterNonmeasurable.positive_set_nonmeasurable_subset
      (F '' N) (pos_iff_ne_zero.mpr hFN)
  have hP : volume (N ∩ F ⁻¹' B) = 0 := measure_mono_null inter_subset_left hN
  have heq : F '' (N ∩ F ⁻¹' B) = B := by
    ext y
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hxN, rfl⟩ := hB hy
      exact ⟨x, ⟨hxN, hy⟩, rfl⟩
  apply hnB
  rw [← heq]
  exact hM _ (inter_subset_left.trans hNs) (NullMeasurableSet.of_null hP)

/-- A completed measurable finite-volume set has countably many compact
subsets whose union leaves only a null remainder. The compact subsets are
inside the original set, not just inside a measurable envelope. -/
lemma exists_compact_sequence_mod_null {E : Set ℝ}
    (hE : NullMeasurableSet E volume) (hfin : volume E ≠ ∞) :
    ∃ K : ℕ → Set ℝ, (∀ n, K n ⊆ E) ∧ (∀ n, IsCompact (K n)) ∧
      volume (E \ ⋃ n, K n) = 0 := by
  classical
  obtain ⟨T, hTE, hTm, hTeq⟩ := hE.exists_measurable_subset_ae_eq
  have hTfin : volume T ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hTE)
  have happ (n : ℕ) : ∃ K : Set ℝ, K ⊆ T ∧ IsCompact K ∧
      volume (T \ K) < (n : ℝ≥0∞)⁻¹ := by
    exact hTm.exists_isCompact_sdiff_lt hTfin (by simp)
  choose K hKT hK hsmall using happ
  have hrem : volume (T \ ⋃ n, K n) = 0 := by
    by_contra hn
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hn
    have hle : volume (T \ ⋃ n, K n) ≤ volume (T \ K n) :=
      measure_mono (sdiff_subset_sdiff Subset.rfl (subset_iUnion K n))
    exact (not_lt_of_ge hle) ((hsmall n).trans hn)
  refine ⟨K, fun n => (hKT n).trans hTE, hK, ?_⟩
  have hdiff : volume (E \ T) = 0 := (ae_eq_set.mp hTeq).2
  apply measure_mono_null (show E \ ⋃ n, K n ⊆
      (E \ T) ∪ (T \ ⋃ n, K n) from ?_) (measure_union_null hdiff hrem)
  intro x hx
  by_cases hxT : x ∈ T
  · exact Or.inr ⟨hxT, hx.2⟩
  · exact Or.inl ⟨hx.1, hxT⟩

/-- Compact images are Borel and the image of the null remainder is null.
Only continuity on the interval is required. -/
theorem nullImages_implies_measurableImages :
    Specs.D11.Ch12.MonotoneNullImageCharacterization.nullImages_implies_measurableImages := by
  intro F a b hF hN E hEsub hE
  have hfin : volume E ≠ ∞ :=
    ne_top_of_le_ne_top (by simp : volume (Icc a b) ≠ ∞) (measure_mono hEsub)
  obtain ⟨K, hKE, hK, hrem⟩ := exists_compact_sequence_mod_null hE hfin
  have hm : NullMeasurableSet (F '' (⋃ n, K n)) volume := by
    rw [image_iUnion]
    apply MeasurableSet.nullMeasurableSet
    exact MeasurableSet.iUnion (fun n =>
      ((hK n).image_of_continuousOn (hF.mono ((hKE n).trans hEsub))).measurableSet)
  have hmrem : NullMeasurableSet (F '' (E \ ⋃ n, K n)) volume :=
    NullMeasurableSet.of_null (hN _ (sdiff_subset.trans hEsub) hrem)
  have hUE : (⋃ n, K n) ⊆ E := iUnion_subset hKE
  have heq : (⋃ n, K n) ∪ (E \ ⋃ n, K n) = E := union_sdiff_cancel hUE
  rw [← heq, image_union]
  exact hm.union hmrem

/-- The two image conditions are equivalent, including every subset admitted
by completion. This part does not need monotonicity. -/
theorem nullImages_iff_measurableImages :
    Specs.D11.Ch12.MonotoneNullImageCharacterization.nullImages_iff_measurableImages := by
  intro F a b hF
  exact ⟨nullImages_implies_measurableImages F a b hF,
    measurableImages_implies_nullImages F (Icc a b)⟩

/-- Constant functions have zero increments and images contained in a singleton.
No nondegenerate-range assumption is needed, even for an empty domain. -/
theorem constant_case :
    Specs.D11.Ch12.MonotoneNullImageCharacterization.constant_case := by
  intro F a b c hF
  have hN : NullImagesOn F (Icc a b) := by
    intro N hNs _
    apply measure_mono_null (show F '' N ⊆ {c} from ?_) (by simp)
    rintro y ⟨x, hx, rfl⟩
    exact hF x (hNs hx)
  refine ⟨?_, hN, ?_⟩
  · intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro n u v _ hmem _ _
    simpa only [hF _ (hmem _).1, hF _ (hmem _).2, sub_self,
      norm_zero, Finset.sum_const_zero] using hε
  · intro E hEs _
    apply NullMeasurableSet.of_null
    apply measure_mono_null (show F '' E ⊆ {c} from ?_) (by simp)
    rintro y ⟨x, hx, rfl⟩
    exact hF x (hEs hx)

/-- The Stieltjes covering cost dominates outer length of images. This tests
all sets, with no Borel or completed-measurability premise on the set or image. -/
lemma image_volume_le_stieltjes (f : StieltjesFunction ℝ) (E : Set ℝ) :
    volume (f '' E) ≤ f.measure E := by
  have hle : OuterMeasure.comap f volume.toOuterMeasure ≤ f.outer := by
    apply OuterMeasure.le_ofFunction.mpr
    intro s
    change volume (f '' s) ≤ f.length s
    rw [f.length_eq]
    refine le_iInf fun u => le_iInf fun v => le_iInf fun h => ?_
    have hs : s ⊆ Ioc u v := by
      intro x hx
      apply h
      refine ⟨hx, ?_⟩
      change ¬ IsBot x
      intro hb
      have hh := hb (x - 1)
      linarith
    calc
      volume (f '' s) ≤ volume (Icc (f u) (f v)) := by
        apply measure_mono
        rintro y ⟨x, hx, rfl⟩
        exact ⟨f.mono (hs hx).1.le, f.mono (hs hx).2⟩
      _ = ENNReal.ofReal (f v - f u) := Real.volume_Icc
  rw [StieltjesFunction.measure]
  exact hle E

/-- Finite total mass and the complementary-set inequality force equality on
Borel sets. This uses outer length throughout and assumes no measurable images. -/
lemma image_volume_eq_stieltjes (f : StieltjesFunction ℝ) [IsFiniteMeasure f.measure]
    (htotal : volume (f '' univ) = f.measure univ)
    {E : Set ℝ} (hE : MeasurableSet E) : volume (f '' E) = f.measure E := by
  apply le_antisymm (image_volume_le_stieltjes f E)
  apply ENNReal.le_of_add_le_add_right (measure_ne_top f.measure Eᶜ)
  calc
    f.measure E + f.measure Eᶜ = f.measure univ := measure_add_measure_compl hE
    _ = volume (f '' univ) := htotal.symm
    _ = volume (f '' E ∪ f '' Eᶜ) := by rw [← image_union, union_compl_self]
    _ ≤ volume (f '' E) + volume (f '' Eᶜ) := measure_union_le _ _
    _ ≤ volume (f '' E) + f.measure Eᶜ :=
      add_le_add_right (image_volume_le_stieltjes f Eᶜ) _

/-- Translation invariance is used for arbitrary subsets, including images
whose measurability has not been established. -/
lemma image_sub_const_volume (F : ℝ → ℝ) (c : ℝ) (E : Set ℝ) :
    volume ((fun x => F x - c) '' E) = volume (F '' E) := by
  have heq : (fun x => F x - c) '' E = (fun y => y + -c) '' (F '' E) := by
    rw [image_image]
    simp only [sub_eq_add_neg]
  rw [heq, image_add_right, measure_preimage_add_right]

/-- The null-image property respects the literal normalized constant extension.
Values off the interval add at most the two endpoint images. -/
lemma compactNormalization_nullImages_iff (F : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    NullImagesOn (NormalizedStieltjes.compactNormalization F a b) univ ↔
      NullImagesOn F (Icc a b) := by
  let H := NormalizedStieltjes.compactNormalization F a b
  have hval := NormalizedStieltjes.compact_values F hab
  have himage (E : Set ℝ) (hE : E ⊆ Icc a b) :
      volume (H '' E) = volume (F '' E) := by
    have heq : H '' E = (fun x => F x - F a) '' E := by
      apply image_congr
      intro x hx
      exact hval.2.1 x (hE hx)
    rw [heq, image_sub_const_volume]
  constructor
  · intro hN N hNs hNzero
    rw [← himage N hNs]
    exact hN N (subset_univ _) hNzero
  · intro hN N _ hNzero
    have hNi : volume (H '' (N ∩ Icc a b)) = 0 := by
      rw [himage _ inter_subset_right]
      exact hN _ inter_subset_right (measure_mono_null inter_subset_left hNzero)
    apply measure_mono_null (show H '' N ⊆
        (H '' (N ∩ Icc a b)) ∪ ({0, F b - F a} : Set ℝ) from ?_)
      (measure_union_null hNi ((Set.toFinite {0, F b - F a}).measure_zero volume))
    rintro y ⟨x, hx, rfl⟩
    by_cases hxi : x ∈ Icc a b
    · exact Or.inl ⟨x, ⟨hx, hxi⟩, rfl⟩
    · right
      rcases lt_or_ge x a with hxa | hax
      · simp only [H, hval.1 x hxa.le, mem_insert_iff, mem_singleton_iff, true_or]
      · have hbx : b ≤ x := le_of_not_ge (fun hxb => hxi ⟨hax, hxb⟩)
        simp only [H, hval.2.2 x hbx, mem_insert_iff, mem_singleton_iff, or_true]

/-- A finite positive Stieltjes measure with the full range-length identity
characterizes null images. In the reverse direction RN provides a density,
whose cumulative integral is uniformly AC on the whole real line. -/
lemma positive_stieltjes_ac_iff_nullImages (H : ℝ → ℝ)
    (hH : PositiveStieltjes.PositiveGenerator H)
    (htotal : volume (H '' univ) = PositiveStieltjes.stieltjesMeasure H hH univ) :
    AbsolutelyContinuous H ↔ NullImagesOn H univ := by
  let f : StieltjesFunction ℝ := ⟨H, hH.1, hH.2.1⟩
  let μ := PositiveStieltjes.stieltjesMeasure H hH
  haveI : IsFiniteMeasure μ := PositiveStieltjes.stieltjesMeasure_finite H hH
  haveI : IsFiniteMeasure f.measure := inferInstanceAs (IsFiniteMeasure μ)
  constructor
  · intro hAC E _ hE
    have hμ : μ ≪ volume := AcPositiveStieltjesNull.absolutely_continuous H hH hAC
    exact measure_mono_null (Subset.rfl : H '' E ⊆ f '' E)
      (le_antisymm ((image_volume_le_stieltjes f E).trans_eq (hμ hE)) bot_le)
  · intro hN
    have hμ : μ ≪ volume := Measure.AbsolutelyContinuous.mk (by
      intro E hE hz
      change f.measure E = 0
      rw [← image_volume_eq_stieltjes f htotal hE]
      exact hN E (subset_univ _) hz)
    let g : ℝ → ℝ := fun x => (μ.rnDeriv volume x).toReal
    have hgi : Integrable g volume := by
      have hi := Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := volume)
        (measure_ne_top μ univ)
      simpa only [integrableOn_univ] using hi
    apply AcStieltjesEquivalence.density_ac H g hgi
    intro x
    rw [Measure.setIntegral_toReal_rnDeriv hμ]
    exact (PositiveStieltjes.cumulative_stieltjesMeasure H hH x).symm

/-- Absolute continuity is equivalent to the null-image condition for the
original compact-interval function. Normalization includes both endpoints and
works also when the range has length zero. -/
theorem ac_iff_nullImages :
    Specs.D11.Ch12.MonotoneNullImageCharacterization.ac_iff_nullImages := by
  intro F a b hab hF hmono
  let H := NormalizedStieltjes.compactNormalization F a b
  have hclamp (x : ℝ) := NormalizedStieltjes.clamp_mem hab.le x
  have hHm : Monotone H := by
    intro x y hxy
    exact sub_le_sub_right (hmono (hclamp x) (hclamp y)
      (NormalizedStieltjes.clamp_mono a b hxy)) _
  have hHc : Continuous H :=
    (hF.comp_continuous (NormalizedStieltjes.clamp_continuous a b) hclamp).sub continuous_const
  have hval := NormalizedStieltjes.compact_values F hab.le
  have hbounds (x : ℝ) : 0 ≤ H x ∧ H x ≤ F b - F a := by
    constructor
    · exact sub_nonneg.mpr (hmono (left_mem_Icc.mpr hab.le) (hclamp x) (hclamp x).1)
    · exact sub_le_sub_right (hmono (hclamp x) (right_mem_Icc.mpr hab.le) (hclamp x).2) _
  have hpos : PositiveStieltjes.PositiveGenerator H :=
    ⟨hHm, fun x => hHc.continuousAt.continuousWithinAt,
      NormalizedStieltjes.compactNormalization_tendsto F hab.le,
      ⟨F b - F a, fun x => by rw [abs_of_nonneg (hbounds x).1]; exact (hbounds x).2⟩⟩
  have htop : Tendsto H atTop (𝓝 (F b - F a)) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop b] with x hx
    exact (hval.2.2 x hx).symm
  have ha : H a = 0 := hval.1 a le_rfl
  have hb : H b = F b - F a := hval.2.2 b le_rfl
  have hrange : H '' univ = Icc 0 (F b - F a) := by
    apply subset_antisymm
    · rintro y ⟨x, _, rfl⟩
      exact hbounds x
    · have hI : H '' Icc a b = Icc 0 (F b - F a) := by
        simpa only [ha, hb] using
          hHc.continuousOn.image_Icc_of_monotoneOn hab.le (hHm.monotoneOn _)
      rw [← hI]
      exact image_mono (subset_univ _)
  have htotal : volume (H '' univ) = PositiveStieltjes.stieltjesMeasure H hpos univ := by
    rw [hrange, Real.volume_Icc]
    exact ((StieltjesFunction.mk H hpos.1 hpos.2.1).measure_univ hpos.2.2.1 htop).symm
  exact (AcStieltjesEquivalence.compactNormalization_ac_iff F hab.le).trans
    ((positive_stieltjes_ac_iff_nullImages H hpos htotal).trans
      (compactNormalization_nullImages_iff F hab.le))

/-- The full equivalence, on the completed Lebesgue domain and with the uniform
finite disjoint-interval definition of AC. -/
theorem characterization :
    Specs.D11.Ch12.MonotoneNullImageCharacterization.characterization := by
  intro F a b hab hc hm
  exact ⟨ac_iff_nullImages F hab hc hm, nullImages_iff_measurableImages F a b hc⟩

end D11.Ch12.MonotoneNullImageCharacterization
