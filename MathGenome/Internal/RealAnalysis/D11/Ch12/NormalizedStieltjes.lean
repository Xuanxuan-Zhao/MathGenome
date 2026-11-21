import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.ScalarStieltjesCorrespondence

/-! Exact function/measure variation bridge for normalized Stieltjes measures. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace D11.Ch12.NormalizedStieltjes
open ScalarStieltjesCorrespondence
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem atom_formula (F : ℝ → E) (hF : NBV F) (x : ℝ) :
    stieltjesMeasure F {x} = F x - Function.leftLim F x :=
  measure_atom F hF x

/-- Right continuity is the precise bridge from variation on (a,b] to the
classical endpoint partition variation on [a,b]. -/
theorem variation_interval (F : ℝ → E) (hF : NBV F) (a b : ℝ) (_hab : a ≤ b) :
    (stieltjesMeasure F).variation (Ioc a b) = variation F a b := by
  rw [stieltjesMeasure_eq hF, BoundedVariationOn.variation_vectorMeasure_Ioc,
    hF.rightLim_eq, eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt (hF.2.1 a),
    variation_eq_eVariationOn]

/-- Recover the mass of an initial ray as a supremum of bounded intervals. -/
lemma measure_Iic_eq_iSup_Ioc (μ : Measure ℝ) (x : ℝ) :
    μ (Iic x) = ⨆ a : ℝ, μ (Ioc a x) := by
  apply le_antisymm
  · obtain ⟨u, hu, ht⟩ := Filter.exists_seq_antitone_tendsto_atTop_atBot ℝ
    have hs : (⋃ n : ℕ, Ioc (u n) x) = Iic x := by
      ext y
      simp only [mem_iUnion, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨n, _, hy⟩; exact hy
      · intro hy
        obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_atBot y)).exists
        exact ⟨n, hn, hy⟩
    have hm : Monotone (fun n => Ioc (u n) x) :=
      fun i j hij => Ioc_subset_Ioc_left (hu hij)
    rw [← hs, hm.measure_iUnion]
    exact iSup_le fun n => le_iSup (fun a => μ (Ioc a x)) (u n)
  · exact iSup_le fun a => measure_mono Ioc_subset_Iic_self

theorem variation_initial (F : ℝ → E) (hF : NBV F) (x : ℝ) :
    (stieltjesMeasure F).variation (Iic x) = initialVariation F x := by
  rw [measure_Iic_eq_iSup_Ioc, initialVariation]
  congr 1
  funext a
  by_cases hax : a ≤ x
  · exact variation_interval F hF a x hax
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hax), measure_empty,
      variation_eq_eVariationOn, Icc_eq_empty_of_lt (lt_of_not_ge hax)]
    simp

omit [CompleteSpace E] in
/-- Adjoining the value zero at −∞ does not lose an initial increment. -/
theorem initial_variation_with_zero (F : ℝ → E) (hF : NBV F) (x : ℝ) :
    initialVariation F x = ⨆ a : ℝ, ⨆ (_ : a ≤ x), ‖F a‖ₑ + variation F a x := by
  apply le_antisymm
  · apply iSup_le
    intro a
    by_cases hax : a ≤ x
    · exact (le_add_left le_rfl).trans (le_iSup_of_le a (le_iSup_of_le hax le_rfl))
    · simp [variation_eq_eVariationOn, Icc_eq_empty_of_lt (lt_of_not_ge hax)]
  · refine iSup_le fun a => iSup_le fun hax => ?_
    have hn : ‖F a‖ₑ ≤ initialVariation F a := by
      rw [← ofReal_norm, ENNReal.ofReal_le_iff_le_toReal (initialVariation_finite hF.1 a).ne]
      exact norm_le_initialVariation hF a
    calc
      ‖F a‖ₑ + variation F a x ≤ initialVariation F a + variation F a x := add_le_add hn le_rfl
      _ = initialVariation F x := by
        rw [initialVariation_add hax, variation_eq_eVariationOn]

theorem variation_global (F : ℝ → E) (hF : NBV F) :
    (stieltjesMeasure F).variation univ = globalVariation F := by
  apply le_antisymm
  · rw [stieltjesMeasure_eq hF, globalVariation_eq_eVariationOn]
    exact hF.boundedVariationOn.variation_vectorMeasure_univ_le
  · apply iSup_le
    intro a
    apply iSup_le
    intro b
    by_cases hab : a ≤ b
    · rw [← variation_interval F hF a b hab]
      exact measure_mono (subset_univ _)
    · simp [variation_eq_eVariationOn, Icc_eq_empty_of_lt (lt_of_not_ge hab)]

theorem corresponding_variation (F : ℝ → E) (hF : NBV F) (ν : VectorMeasure ℝ E)
    (hν : ∀ a b : ℝ, a < b → ν (Ioc a b) = F b - F a) :
    (∀ a b : ℝ, a ≤ b → ν.variation (Ioc a b) = variation F a b) ∧
    (∀ x : ℝ, ν.variation (Iic x) = initialVariation F x) ∧
    (∀ x : ℝ, ν {x} = F x - Function.leftLim F x) := by
  rw [measure_unique F hF ν hν]
  exact ⟨variation_interval F hF, variation_initial F hF, atom_formula F hF⟩

theorem cumulative_variation (ν : VectorMeasure ℝ E) (hν : IsFiniteMeasure ν.variation) :
    (∀ a b : ℝ, a ≤ b → ν.variation (Ioc a b) = variation (cumulative ν) a b) ∧
    (∀ x : ℝ, ν.variation (Iic x) = initialVariation (cumulative ν) x) := by
  have hF := cumulative_properties ν hν
  have heq := measure_cumulative ν hν
  exact ⟨by simpa only [heq] using variation_interval (cumulative ν) hF,
    by simpa only [heq] using variation_initial (cumulative ν) hF⟩

/-- Clamp the argument to [a,b], then fix the additive constant at a. -/
def compactNormalization (F : ℝ → E) (a b x : ℝ) : E :=
  F (max a (min b x)) - F a

/-- Canonical normalization of an arbitrary global BV function. -/
noncomputable def rightNormalization (F : ℝ → E) (x : ℝ) : E :=
  F.rightLim x - limUnder atBot F

/-- Right limits of the constant extension, normalized at the left endpoint. -/
noncomputable def compactRightNormalization (F : ℝ → E) (a b : ℝ) : ℝ → E :=
  compactNormalization (compactNormalization F a b).rightLim a b

omit [CompleteSpace E] in
lemma variation_sub_const (F : ℝ → E) (c : E) (s : Set ℝ) :
    eVariationOn (fun x => F x - c) s = eVariationOn F s := by
  simp only [eVariationOn, edist_sub_right]

lemma clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    max a (min b x) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma clamp_mono (a b : ℝ) : Monotone (fun x : ℝ => max a (min b x)) := by
  intro x y hxy
  exact max_le_max_left a (min_le_min_left b hxy)

lemma clamp_continuous (a b : ℝ) : Continuous (fun x : ℝ => max a (min b x)) :=
  continuous_const.max (continuous_const.min continuous_id)

omit [CompleteSpace E] in
theorem compact_values (F : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∀ x, x ≤ a → compactNormalization F a b x = 0) ∧
    (∀ x ∈ Icc a b, compactNormalization F a b x = F x - F a) ∧
    (∀ x, b ≤ x → compactNormalization F a b x = F b - F a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp [compactNormalization, max_eq_left ((min_le_right b x).trans hx)]
  · intro x hx
    simp [compactNormalization, min_eq_right hx.2, max_eq_right hx.1]
  · intro x hx
    simp [compactNormalization, min_eq_left hx, max_eq_right hab]

omit [CompleteSpace E] in
lemma compactNormalization_variation_le (F : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    globalVariation (compactNormalization F a b) ≤ variation F a b := by
  rw [globalVariation_eq_eVariationOn, variation_eq_eVariationOn]
  change eVariationOn (fun x => (F ∘ (fun y => max a (min b y))) x - F a) univ ≤ _
  rw [variation_sub_const]
  exact eVariationOn.comp_le_of_monotoneOn F _ ((clamp_mono a b).monotoneOn univ)
    (fun x _ => clamp_mem hab x)

omit [CompleteSpace E] in
lemma compactNormalization_globallyBV (F : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hF : BV F a b) : GloballyBV (compactNormalization F a b) := by
  exact (compactNormalization_variation_le F hab).trans_lt hF

omit [CompleteSpace E] in
lemma compactNormalization_tendsto (F : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (compactNormalization F a b) atBot (𝓝 0) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_le_atBot a] with x hx
  exact ((compact_values F hab).1 x hx).symm

lemma compactNormalization_nbv (F : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hF : BV F a b)
    (hc : ∀ x ∈ Icc a b, ContinuousWithinAt F (Icc a b ∩ Ici x) x) :
    NBV (compactNormalization F a b) := by
  refine ⟨compactNormalization_globallyBV F hab hF, ?_, compactNormalization_tendsto F hab⟩
  intro x
  have hcomp : ContinuousWithinAt (F ∘ fun y : ℝ => max a (min b y)) (Ici x) x :=
    (hc _ (clamp_mem hab x)).comp (f := fun y : ℝ => max a (min b y))
      (clamp_continuous a b).continuousWithinAt
      (fun y hy => ⟨clamp_mem hab y, clamp_mono a b hy⟩)
  exact hcomp.sub continuousWithinAt_const

theorem compact_continuous (F : ℝ → E) {a b : ℝ} (hab : a < b)
    (hF : BV F a b) (hc : ContinuousOn F (Icc a b)) :
    NBV (compactNormalization F a b) ∧
    Continuous (compactNormalization F a b) ∧
    (∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      stieltjesMeasure (compactNormalization F a b) (Ioc u v) = F v - F u) ∧
    (stieltjesMeasure (compactNormalization F a b)).variation (Ioc a b) = variation F a b := by
  have hn := compactNormalization_nbv F hab.le hF
    (fun x hx => (hc x hx).mono inter_subset_left)
  refine ⟨hn, (hc.comp_continuous (clamp_continuous a b) (clamp_mem hab.le)).sub
    continuous_const, ?_, ?_⟩
  · intro u v hau huv hvb
    rcases huv.eq_or_lt with rfl | huv
    · simp
    rw [measure_interval _ hn _ _ huv,
      (compact_values F hab.le).2.1 v ⟨hau.trans huv.le, hvb⟩,
      (compact_values F hab.le).2.1 u ⟨hau, huv.le.trans hvb⟩]
    abel
  · rw [variation_interval _ hn a b hab.le, variation_eq_eVariationOn,
      variation_eq_eVariationOn]
    calc
      eVariationOn (compactNormalization F a b) (Icc a b) =
          eVariationOn (fun x => F x - F a) (Icc a b) :=
        eVariationOn.eq_of_eqOn (fun x hx => (compact_values F hab.le).2.1 x hx)
      _ = eVariationOn F (Icc a b) := variation_sub_const F (F a) _

lemma rightNormalization_nbv (F : ℝ → E) (hF : GloballyBV F) :
    NBV (rightNormalization F) := by
  have hb := (globallyBV_iff_boundedVariationOn F).mp hF
  refine ⟨?_, ?_, ?_⟩
  · rw [GloballyBV, globalVariation_eq_eVariationOn]
    change eVariationOn (fun x => F.rightLim x - limUnder atBot F) univ < ⊤
    rw [variation_sub_const]
    exact hb.rightLim.lt_top
  · intro x
    exact (continuousWithinAt_rightLim_Ici (hb.tendsto_rightLim x)).sub
      continuousWithinAt_const
  · change Tendsto (fun x => F.rightLim x - limUnder atBot F) atBot (𝓝 0)
    simpa only [sub_self] using
      (tendsto_rightLim_atBot_of_tendsto hb.tendsto_atBot_limUnder).sub_const (limUnder atBot F)

lemma rightNormalization_measure (F : ℝ → E) (hF : GloballyBV F) :
    stieltjesMeasure (rightNormalization F) =
      ((globallyBV_iff_boundedVariationOn F).mp hF).vectorMeasure := by
  apply (measure_unique _ (rightNormalization_nbv F hF) _ ?_).symm
  intro a b hab
  rw [BoundedVariationOn.vectorMeasure_Ioc _ hab.le]
  simp only [rightNormalization]
  abel

theorem right_normalization (F : ℝ → E) (hF : GloballyBV F) :
    NBV (rightNormalization F) ∧
    (∀ x, Tendsto F (𝓝[>] x) (𝓝 (F.rightLim x))) ∧
    (∀ u v : ℝ, u < v → stieltjesMeasure (rightNormalization F) (Ioc u v) =
      F.rightLim v - F.rightLim u) ∧
    (∀ x, stieltjesMeasure (rightNormalization F) {x} = F.rightLim x - F.leftLim x) := by
  have hb := (globallyBV_iff_boundedVariationOn F).mp hF
  refine ⟨rightNormalization_nbv F hF, hb.tendsto_rightLim, ?_, ?_⟩
  · intro u v huv
    rw [rightNormalization_measure F hF, BoundedVariationOn.vectorMeasure_Ioc _ huv.le]
  · intro x
    rw [rightNormalization_measure F hF, BoundedVariationOn.vectorMeasure_singleton]

lemma compactNormalization_rightLim (F : ℝ → E) {a b : ℝ} (hab : a < b)
    (hF : BV F a b) (x : ℝ) (hx : x ∈ Ico a b) :
    (compactNormalization F a b).rightLim x = F.rightLim x - F a := by
  have ht := tendsto_rightLim_of_tendsto ((bv_one_sided_limits F hab hF).2 x hx)
  apply rightLim_eq_of_tendsto
  apply (ht.sub_const (F a)).congr'
  filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy
  exact ((compact_values F hab.le).2.1 y ⟨hx.1.trans hy.1.le, hy.2.le⟩).symm

omit [CompleteSpace E] in
lemma compactNormalization_rightLim_at_right (F : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (compactNormalization F a b).rightLim b = F b - F a := by
  apply rightLim_eq_of_tendsto
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ((compact_values F hab).2.2 x hx.le).symm

theorem compact_right_normalization (F : ℝ → E) {a b : ℝ} (hab : a < b)
    (hF : BV F a b) :
    NBV (compactRightNormalization F a b) ∧
    (∀ x ∈ Ico a b, compactRightNormalization F a b x = F.rightLim x - F.rightLim a) ∧
    compactRightNormalization F a b b = F b - F.rightLim a ∧
    (∀ x, x ≤ a → compactRightNormalization F a b x = 0) ∧
    (∀ x, b ≤ x → compactRightNormalization F a b x = F b - F.rightLim a) := by
  have hG := compactNormalization_globallyBV F hab.le hF
  have hb := (globallyBV_iff_boundedVariationOn _).mp hG
  have hH := compactNormalization_nbv (compactNormalization F a b).rightLim hab.le
    ((bv_iff_boundedVariationOn _ a b).mpr (hb.rightLim.mono (subset_univ _)))
    (fun x _ => (continuousWithinAt_rightLim_Ici (hb.tendsto_rightLim x)).mono
      inter_subset_right)
  have hleft := compactNormalization_rightLim F hab hF a ⟨le_rfl, hab⟩
  have hright := compactNormalization_rightLim_at_right F hab.le
  have hinside (x : ℝ) (hx : x ∈ Ico a b) :
      compactRightNormalization F a b x = F.rightLim x - F.rightLim a := by
    rw [compactRightNormalization, (compact_values _ hab.le).2.1 x ⟨hx.1, hx.2.le⟩,
      compactNormalization_rightLim F hab hF x hx, hleft]
    abel
  have hend : compactRightNormalization F a b b = F b - F.rightLim a := by
    rw [compactRightNormalization, (compact_values _ hab.le).2.1 b ⟨hab.le, le_rfl⟩,
      hright, hleft]
    abel
  refine ⟨hH, hinside, hend, (compact_values _ hab.le).1, ?_⟩
  intro x hx
  change compactNormalization _ a b x = _
  rw [(compact_values _ hab.le).2.2 x hx, hright, hleft]
  abel

theorem compact_right_variation_bound (F : ℝ → E) {a b : ℝ} (hab : a < b)
    (_hF : BV F a b) :
    globalVariation (compactRightNormalization F a b) ≤ variation F a b := by
  change globalVariation (compactNormalization _ a b) ≤ _
  calc
    globalVariation (compactNormalization (compactNormalization F a b).rightLim a b)
        ≤ variation (compactNormalization F a b).rightLim a b :=
      compactNormalization_variation_le _ hab.le
    _ ≤ globalVariation (compactNormalization F a b) := by
      rw [variation_eq_eVariationOn, globalVariation_eq_eVariationOn]
      exact (eVariationOn.mono _ (subset_univ _)).trans
        (eVariationOn.eVariationOn_rightLim_le isOpen_univ)
    _ ≤ variation F a b := compactNormalization_variation_le F hab.le

theorem signed_bijection : Specs.D11.Ch12.NormalizedStieltjes.signed_bijection := by
  obtain ⟨e, he, hback⟩ := ScalarStieltjesCorrespondence.signed_bijection
  refine ⟨e, he, hback, ?_⟩
  intro F
  have heq : e F = stieltjesMeasure F.val := by
    apply vectorMeasure_ext_of_Iic
    intro x
    exact (he F x).trans (congrFun (cumulative_measure F.val F.property) x).symm
  change (∀ a b : ℝ, a < b → e F (Ioc a b) = F.val b - F.val a) ∧
    (∀ x : ℝ, e F {x} = F.val x - Function.leftLim F.val x) ∧
    (∀ a b : ℝ, a ≤ b → (e F).variation (Ioc a b) = variation F.val a b) ∧
    (∀ x : ℝ, (e F).variation (Iic x) = initialVariation F.val x)
  rw [heq]
  exact ⟨measure_interval F.val F.property, atom_formula F.val F.property,
    variation_interval F.val F.property, variation_initial F.val F.property⟩

theorem complex_bijection : Specs.D11.Ch12.NormalizedStieltjes.complex_bijection := by
  obtain ⟨e, he, hback⟩ := ScalarStieltjesCorrespondence.complex_bijection
  refine ⟨e, he, hback, ?_⟩
  intro F
  have heq : e F = stieltjesMeasure F.val := by
    apply vectorMeasure_ext_of_Iic
    intro x
    exact (he F x).trans (congrFun (cumulative_measure F.val F.property) x).symm
  change (∀ a b : ℝ, a < b → e F (Ioc a b) = F.val b - F.val a) ∧
    (∀ x : ℝ, e F {x} = F.val x - Function.leftLim F.val x) ∧
    (∀ a b : ℝ, a ≤ b → (e F).variation (Ioc a b) = variation F.val a b) ∧
    (∀ x : ℝ, (e F).variation (Iic x) = initialVariation F.val x)
  rw [heq]
  exact ⟨measure_interval F.val F.property, atom_formula F.val F.property,
    variation_interval F.val F.property, variation_initial F.val F.property⟩

end D11.Ch12.NormalizedStieltjes
