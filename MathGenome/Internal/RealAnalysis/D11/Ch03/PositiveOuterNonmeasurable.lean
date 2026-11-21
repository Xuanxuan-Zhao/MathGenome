import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.PositiveOuterNonmeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Filter Metric Bornology
open scoped ENNReal Pointwise Topology

namespace D11.Ch03.PositiveOuterNonmeasurable

/-- A finite-outer-mass set passing the splitting test is measurable for the
ordinary completion. This uses a measurable envelope, not Borel measurability
of the original set. -/
theorem nullMeasurableSet_of_caratheodory_of_ne_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s : Set α} (hs : μ.toOuterMeasure.IsCaratheodory s)
    (hfin : μ s ≠ ∞) : NullMeasurableSet s μ := by
  have hst := subset_toMeasurable μ s
  have ht := hs (toMeasurable μ s)
  change μ (toMeasurable μ s) = μ (toMeasurable μ s ∩ s) +
    μ (toMeasurable μ s \ s) at ht
  rw [measure_toMeasurable, inter_eq_right.mpr hst] at ht
  have hn : μ (toMeasurable μ s \ s) = 0 := by
    apply (ENNReal.add_left_inj hfin).mp
    simpa only [zero_add, add_comm] using ht.symm
  exact (measurableSet_toMeasurable μ s).nullMeasurableSet.congr
    (ae_eq_set.mpr ⟨hn, by simp [sdiff_eq_empty.mpr hst]⟩)

/-- Sigma-finiteness supplies the converse inclusion of the Carathéodory
sigma-algebra in the ordinary completion. -/
theorem nullMeasurableSet_of_caratheodory {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] {s : Set α}
    (hs : μ.toOuterMeasure.IsCaratheodory s) : NullMeasurableSet s μ := by
  have h : ∀ n, NullMeasurableSet (s ∩ spanningSets μ n) μ := by
    intro n
    apply nullMeasurableSet_of_caratheodory_of_ne_top μ
    · exact μ.toOuterMeasure.isCaratheodory_inter hs
        (le_toOuterMeasure_caratheodory μ _ (measurableSet_spanningSets μ n))
    · exact ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne
        (measure_mono inter_subset_right)
  have heq : (⋃ n, s ∩ spanningSets μ n) = s := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rw [← heq]
  exact NullMeasurableSet.iUnion h

section Transversal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Choice of one representative for each rational-translation class meeting
an arbitrary set. The representative always belongs to the original set. -/
theorem exists_rational_transversal (B : Set E) (v : E) :
    ∃ V ⊆ B,
      (B ⊆ ⋃ q : ℚ, {(q : ℝ) • v} + V) ∧
      (∀ x ∈ V, ∀ y ∈ V, (∃ q : ℚ, x - y = (q : ℝ) • v) → x = y) := by
  classical
  let r : Setoid B :=
    { r := fun x y => ∃ q : ℚ, (x : E) - y = (q : ℝ) • v
      iseqv := {
        refl := by intro x; exact ⟨0, by simp⟩
        symm := by
          intro x y h
          obtain ⟨q, hq⟩ := h
          refine ⟨-q, ?_⟩
          rw [Rat.cast_neg, neg_smul, ← hq, neg_sub]
        trans := by
          intro x y z hxy hyz
          obtain ⟨q, hq⟩ := hxy
          obtain ⟨t, ht⟩ := hyz
          refine ⟨q + t, ?_⟩
          rw [Rat.cast_add, add_smul, ← hq, ← ht, sub_add_sub_cancel] } }
  let V : Set E := range (fun k : Quotient r => (k.out : E))
  refine ⟨V, ?_, ?_, ?_⟩
  · rintro x ⟨k, rfl⟩
    exact k.out.property
  · intro x hx
    let k : Quotient r := Quotient.mk r ⟨x, hx⟩
    obtain ⟨q, hq⟩ := Quotient.mk_out (s := r) (⟨x, hx⟩ : B)
    apply mem_iUnion.mpr
    refine ⟨-q, ?_⟩
    simp only [singleton_add, mem_image]
    refine ⟨(k.out : E), mem_range_self k, ?_⟩
    rw [Rat.cast_neg, neg_smul]
    change (k.out : E) - x = (q : ℝ) • v at hq
    rw [← hq]
    abel
  · rintro x ⟨k, rfl⟩ y ⟨l, rfl⟩ h
    have hkl : k = l := Quotient.out_equiv_out.mp h
    rw [hkl]

end Transversal

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- A rational transversal has zero outer measure if it is measurable for
completion. Borel inner representatives allow the Haar lemma to be applied
without imposing a Borel hypothesis on the transversal itself. -/
theorem rational_transversal_null {V : Set E} (v : E) (hv : v ≠ 0)
    (hV : ∀ x ∈ V, ∀ y ∈ V, (∃ q : ℚ, x - y = (q : ℝ) • v) → x = y)
    (hm : NullMeasurableSet V μ) : μ V = 0 := by
  obtain ⟨T, hTV, hTm, hTeq⟩ := hm.exists_measurable_subset_ae_eq
  let u : ℕ → E := fun n => ((1 / 2 : ℝ) ^ n) • v
  have hu : IsBounded (range u) := by
    apply isBounded_range_of_tendsto u
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).smul_const v
  have hd : Pairwise (Function.onFun Disjoint (fun n => {u n} + T)) := by
    intro m n hmn
    change Disjoint ({u m} + T) ({u n} + T)
    rw [disjoint_left]
    intro z hzm hzn
    simp only [singleton_add, mem_image] at hzm hzn
    obtain ⟨x, hx, hxz⟩ := hzm
    obtain ⟨y, hy, hyz⟩ := hzn
    have hxy : x = y := by
      apply hV x (hTV hx) y (hTV hy)
      refine ⟨(1 / 2 : ℚ) ^ n - (1 / 2 : ℚ) ^ m, ?_⟩
      push_cast
      dsimp [u] at hxz hyz
      rw [sub_smul]
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm] using hxz.trans hyz.symm
    have hpow : (1 / 2 : ℝ) ^ m = (1 / 2 : ℝ) ^ n := by
      apply smul_left_injective ℝ hv
      dsimp [u] at hxz hyz
      simpa [hxy] using hxz.trans hyz.symm
    exact hmn ((pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).injective hpow)
  rw [← measure_congr hTeq]
  exact μ.addHaar_eq_zero_of_disjoint_translates u hu hd hTm

/-- Vitali's argument for any positive-outer-measure set in a finite-dimensional
real space with a specified nonzero direction. -/
theorem exists_non_nullMeasurable_subset (v : E) (hv : v ≠ 0)
    (B : Set E) (hB : 0 < μ B) : ∃ V ⊆ B, ¬ NullMeasurableSet V μ := by
  obtain ⟨V, hVB, hcover, hV⟩ := exists_rational_transversal B v
  refine ⟨V, hVB, ?_⟩
  intro hm
  have hzero := rational_transversal_null μ v hv hV hm
  have hz : μ (⋃ q : ℚ, {(q : ℝ) • v} + V) = 0 := by
    apply measure_iUnion_null
    intro q
    simpa only [singleton_add, image_add_left, measure_preimage_add] using hzero
  exact (ne_of_gt hB) (measure_mono_null hcover hz)

end Haar

/-- Source corollary on the real line, with ordinary completed Lebesgue
measurability and no measurability assumption on the containing set. -/
theorem positive_set_nonmeasurable_subset :
    Specs.D11.Ch03.PositiveOuterNonmeasurable.positive_set_nonmeasurable_subset := by
  intro B hB
  exact exists_non_nullMeasurable_subset volume (1 : ℝ) one_ne_zero B hB

/-- The conclusion for the original shared covering outer measure and the
full splitting-test measurable space, rather than only Borel measurability. -/
theorem positive_outer_nonmeasurable_subset :
    Specs.D11.Ch03.PositiveOuterNonmeasurable.positive_outer_nonmeasurable_subset := by
  intro B hB
  have hB' : 0 < volume B := by
    rwa [LebesgueMeasures.native_outer_agreement 1 B]
  let v : Point 1 := EuclideanSpace.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (fun x : Point 1 => x 0) h
    norm_num [v, EuclideanSpace.single, PiLp.single_apply] at this
  obtain ⟨V, hVB, hV⟩ := exists_non_nullMeasurable_subset volume v hv B hB'
  refine ⟨V, hVB, ?_⟩
  intro hm
  apply hV
  apply nullMeasurableSet_of_caratheodory
  intro T
  have ht := hm T
  change volume T = volume (T ∩ V) + volume (T \ V)
  rw [LebesgueMeasures.native_outer_agreement 1 T,
    LebesgueMeasures.native_outer_agreement 1 (T ∩ V),
    LebesgueMeasures.native_outer_agreement 1 (T \ V)]
  exact ht

end D11.Ch03.PositiveOuterNonmeasurable
