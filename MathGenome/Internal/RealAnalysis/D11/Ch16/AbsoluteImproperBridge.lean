import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.AbsoluteImproperBridge
import MathGenome.Internal.RealAnalysis.D11.Ch16.ProperIntegralEquality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace D11.Ch16.AbsoluteImproperBridge
open SingleVariableAnalysis.Riemann

lemma norm_bounded {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) {a b : ℝ}
    (h : RiemannIntegrable f a b) : BoundedOnInterval (fun x => ‖f x‖) a b := by
  obtain ⟨lr, hlr⟩ := h.1.choose_spec.choose.1
  obtain ⟨ur, hur⟩ := h.1.choose_spec.choose.2
  obtain ⟨li, hli⟩ := h.2.choose_spec.choose.1
  obtain ⟨ui, hui⟩ := h.2.choose_spec.choose.2
  refine ⟨⟨0, ?_⟩, ⟨|lr| + |ur| + |li| + |ui|, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_nonneg _
  · rintro _ ⟨x, hx, rfl⟩
    have hr : |RCLike.re (f x)| ≤ |lr| + |ur| := by
      have hl := hlr (mem_image_of_mem _ hx)
      have hu := hur (mem_image_of_mem _ hx)
      rw [abs_le]
      constructor <;> linarith [neg_abs_le lr, le_abs_self ur, abs_nonneg lr, abs_nonneg ur]
    have hi : |RCLike.im (f x)| ≤ |li| + |ui| := by
      have hl := hli (mem_image_of_mem _ hx)
      have hu := hui (mem_image_of_mem _ hx)
      rw [abs_le]
      constructor <;> linarith [neg_abs_le li, le_abs_self ui, abs_nonneg li, abs_nonneg ui]
    have hn : ‖f x‖ ≤ |RCLike.re (f x)| + |RCLike.im (f x)| := by
      calc
        ‖f x‖ = ‖(RCLike.re (f x) : 𝕜) + (RCLike.im (f x) : 𝕜) * RCLike.I‖ :=
          congrArg norm (RCLike.re_add_im (f x)).symm
        _ ≤ ‖(RCLike.re (f x) : 𝕜)‖ + ‖(RCLike.im (f x) : 𝕜) * RCLike.I‖ := norm_add_le _ _
        _ ≤ |RCLike.re (f x)| + |RCLike.im (f x)| := by
          simp only [norm_mul, RCLike.norm_ofReal]
          have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
            rw [RCLike.norm_I]; split <;> norm_num
          exact add_le_add_right (mul_le_of_le_one_right (abs_nonneg _) hI) _
    linarith

theorem norm_riemann {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (a b : ℝ)
    (h : RiemannIntegrable f a b) : RealRiemann (fun x => ‖f x‖) a b := by
  rcases h.1.choose.eq_or_lt with hab | hab
  · subst b
    exact realIntegrable_degenerate _ a
  · apply (D11.Ch16.RiemannCriterion.riemann_criterion _ a b hab (norm_bounded f h)).mpr
    have hr := (D11.Ch16.RiemannCriterion.riemann_criterion _ a b hab
      h.1.choose_spec.choose).mp h.1
    have hi := (D11.Ch16.RiemannCriterion.riemann_criterion _ a b hab
      h.2.choose_spec.choose).mp h.2
    apply measure_mono_null (t :=
      {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt (fun x => RCLike.re (f x)) (Icc a b) x} ∪
      {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt (fun x => RCLike.im (f x)) (Icc a b) x}) _
      (measure_union_null hr hi)
    intro x hx
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_and] at hn
    have hcr := not_not.mp (hn.1 hx.1)
    have hci := not_not.mp (hn.2 hx.1)
    have hc : ContinuousWithinAt f (Icc a b) x := by
      have hh := ((RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt hcr).add
        ((RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt hci).mul_const
          (RCLike.I : 𝕜)))
      change ContinuousWithinAt (fun y => (RCLike.re (f y) : 𝕜) +
        (RCLike.im (f y) : 𝕜) * RCLike.I) (Icc a b) x at hh
      simpa only [RCLike.re_add_im] using hh
    exact hx.2 hc.norm

local notation "mL" => lebesgueSpace
local notation "μL" => lebesgueMeasure

lemma completed_measurableSet {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet[mL] S := hS.nullMeasurableSet

lemma proper_integrable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) {a b : ℝ} (h : RiemannIntegrable f a b) :
    IntegrableOn f (Icc a b) μL := by
  have hr := ProperIntegralEquality.real_indicator_integrable _ h.1
  have hi := ProperIntegralEquality.real_indicator_integrable _ h.2
  have heq : (Icc a b).indicator f = fun x =>
      (RCLike.ofReal ((Icc a b).indicator (fun x => RCLike.re (f x)) x) : 𝕜) +
      (RCLike.ofReal ((Icc a b).indicator (fun x => RCLike.im (f x)) x) : 𝕜) * RCLike.I := by
    ext x
    by_cases hx : x ∈ Icc a b
    · simpa only [indicator_of_mem hx] using (RCLike.re_add_im (f x)).symm
    · simp [hx]
  apply (integrable_indicator_iff (completed_measurableSet measurableSet_Icc)).mp
  rw [heq]
  exact (hr.ofReal (𝕜 := 𝕜)).add ((hi.ofReal (𝕜 := 𝕜)).mul_const _)

lemma proper_value_eq {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) {a b : ℝ} (h : RiemannIntegrable f a b) :
    properValue f a b = ∫ x in Icc a b, f x ∂μL := by
  rw [properValue, dite_eq_left h]
  have hint := (proper_integrable f h).integrable_indicator
    (completed_measurableSet measurableSet_Icc)
  have heq := @integral_re_add_im ℝ mL μL 𝕜 inferInstance _ hint
  have hr : (fun x => RCLike.re ((Icc a b).indicator f x)) =
      (Icc a b).indicator (fun x => RCLike.re (f x)) := by
    ext x
    by_cases hx : x ∈ Icc a b <;> simp [hx]
  have hi : (fun x => RCLike.im ((Icc a b).indicator f x)) =
      (Icc a b).indicator (fun x => RCLike.im (f x)) := by
    ext x
    by_cases hx : x ∈ Icc a b <;> simp [hx]
  rw [hr, hi, ← ProperIntegralEquality.real_integral_eq _ h.1,
    ← ProperIntegralEquality.real_integral_eq _ h.2] at heq
  exact heq.trans (integral_indicator (completed_measurableSet measurableSet_Icc))

lemma absolute_value_eq {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → 𝕜) {a b : ℝ} (h : RiemannIntegrable f a b) :
    absoluteValue f a b = ∫ x in Icc a b, ‖f x‖ ∂μL := by
  rw [absoluteValue, dite_eq_left (norm_riemann f a b h)]
  exact (ProperIntegralEquality.real_integral_eq _ (norm_riemann f a b h)).trans
    (integral_indicator (completed_measurableSet measurableSet_Icc))

lemma absolute_value_ofReal_eq {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → 𝕜) {a b : ℝ} (h : RiemannIntegrable f a b) :
    ENNReal.ofReal (absoluteValue f a b) =
      ∫⁻ x in Icc a b, ENNReal.ofReal ‖f x‖ ∂μL := by
  rw [absolute_value_eq f h]
  have hn := ProperIntegralEquality.real_indicator_integrable _ (norm_riemann f a b h)
  have hn' := (integrable_indicator_iff (completed_measurableSet measurableSet_Icc)).mp hn
  exact ofReal_integral_eq_lintegral_ofReal hn' (Eventually.of_forall fun x => norm_nonneg _)

lemma inL1_iff {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (S : Set ℝ) (hm : @Measurable ℝ 𝕜 mL _ (S.indicator f))
    (hs : MeasurableSet[mL] S) : InL1 f S ↔ IntegrableOn f S μL := by
  exact (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff ℝ 𝕜 mL _ _ _ μL _).trans
    ((and_iff_right hm).trans (integrable_indicator_iff hs))

theorem exhaustion_bridge : Specs.D11.Ch16.AbsoluteImproperBridge.exhaustion_bridge := by
  intro 𝕜 ι _ _ _ f S u v l _ _ hs hR hc
  classical
  let : (μL).IsComplete := by
    change (volume : Measure ℝ).completion.IsComplete
    infer_instance
  let φ : ι → Set ℝ := fun i =>
    if RiemannIntegrable f (u i) (v i) ∧ Icc (u i) (v i) ⊆ S
      then Icc (u i) (v i) else ∅
  have hφ : ∀ i, MeasurableSet[mL] (φ i) := by
    intro i
    dsimp [φ]
    split
    · exact completed_measurableSet measurableSet_Icc
    · exact @MeasurableSet.empty ℝ mL
  have cover : @AECover ℝ ι mL ((μL).restrict S) l φ := by
    refine @AECover.mk ℝ ι mL ((μL).restrict S) l φ ?_ hφ
    filter_upwards [@ae_restrict_mem ℝ mL μL S hs] with x hx
    filter_upwards [hR, hc x hx] with i hi hxi
    simpa only [φ, ite_eq_left hi] using hxi
  have hfi : ∀ i, IntegrableOn f (φ i) μL := by
    intro i
    dsimp [φ]
    split_ifs with h
    · exact proper_integrable f h.1
    · exact @integrableOn_empty ℝ 𝕜 mL f μL _ _
  have hfiS : ∀ i, IntegrableOn f (φ i) ((μL).restrict S) :=
    fun i => (hfi i).mono_measure Measure.restrict_le_self
  have hfm : @AEStronglyMeasurable ℝ 𝕜 _ mL mL f ((μL).restrict S) :=
    @AECover.aestronglyMeasurable ℝ ι mL _ l 𝕜 _ _ _ _ f φ cover
      (fun i => (hfiS i).aestronglyMeasurable)
  have hm : @Measurable ℝ 𝕜 mL _ (S.indicator f) := by
    have ha : AEMeasurable (S.indicator f) μL :=
      (aemeasurable_indicator_iff hs).mpr hfm.aemeasurable
    exact ha.nullMeasurable.measurable_of_complete
  have hproper : (fun i => properValue f (u i) (v i)) =ᶠ[l]
      (fun i => ∫ x in φ i, f x ∂(μL).restrict S) := by
    filter_upwards [hR] with i hi
    simp only [φ, ite_eq_left hi, Measure.restrict_restrict_of_subset hi.2]
    exact proper_value_eq f hi.1
  have habs : (fun i => absoluteValue f (u i) (v i)) =ᶠ[l]
      (fun i => ∫ x in φ i, ‖f x‖ ∂(μL).restrict S) := by
    filter_upwards [hR] with i hi
    simp only [φ, ite_eq_left hi, Measure.restrict_restrict_of_subset hi.2]
    exact absolute_value_eq f hi.1
  have hext : (fun i => ENNReal.ofReal (absoluteValue f (u i) (v i))) =ᶠ[l]
      (fun i => ∫⁻ x in φ i, ENNReal.ofReal ‖f x‖ ∂(μL).restrict S) := by
    filter_upwards [hR] with i hi
    simp only [φ, ite_eq_left hi, Measure.restrict_restrict_of_subset hi.2]
    exact absolute_value_ofReal_eq f hi.1
  refine ⟨hm, ?_, ?_, ?_⟩
  · exact (@AECover.lintegral_tendsto_of_countably_generated ℝ ι mL _ l _ φ cover _
      (ENNReal.measurable_ofReal.comp_aemeasurable hfm.norm.aemeasurable)).congr' hext.symm
  · constructor
    · rintro ⟨A, hA⟩
      exact (inL1_iff f S hm hs).mpr
        (@AECover.integrable_of_integral_norm_tendsto ℝ ι 𝕜 mL _ l _ _ _ φ cover
          f A hfiS (hA.congr' habs))
    · intro hL
      have hi := (inL1_iff f S hm hs).mp hL
      exact ⟨∫ x in S, ‖f x‖ ∂μL,
        (@AECover.integral_tendsto_of_countably_generated ℝ ι ℝ mL _ l _ _ _ φ
          cover _ hi.norm).congr' habs.symm⟩
  · intro hL
    have hi := (inL1_iff f S hm hs).mp hL
    have he := (@AECover.integral_tendsto_of_countably_generated ℝ ι 𝕜 mL _ l _ _ _ φ
      cover _ hi).congr' hproper.symm
    change Tendsto _ _ (𝓝 (∫ x, S.indicator f x ∂μL))
    rw [integral_indicator hs]
    exact he

theorem right_infinite : Specs.D11.Ch16.AbsoluteImproperBridge.right_infinite := by
  intro 𝕜 _ _ _ f a hR
  apply exhaustion_bridge f (Ici a) (fun _ => a) id atTop
    (completed_measurableSet measurableSet_Ici)
  · filter_upwards [eventually_ge_atTop a] with R hRge
    exact ⟨hR R hRge, fun _ hx => hx.1⟩
  · intro x hx
    filter_upwards [eventually_ge_atTop x] with R hRge
    exact ⟨hx, hRge⟩

theorem left_infinite : Specs.D11.Ch16.AbsoluteImproperBridge.left_infinite := by
  intro 𝕜 _ _ _ f b hR
  apply exhaustion_bridge f (Iic b) id (fun _ => b) atBot
    (completed_measurableSet measurableSet_Iic)
  · filter_upwards [eventually_le_atBot b] with r hrle
    exact ⟨hR r hrle, fun _ hx => hx.2⟩
  · intro x hx
    filter_upwards [eventually_le_atBot x] with r hrle
    exact ⟨hrle, hx⟩

theorem left_singular : Specs.D11.Ch16.AbsoluteImproperBridge.left_singular := by
  intro 𝕜 _ _ _ f a b hab hR
  apply exhaustion_bridge f (Ioc a b) id (fun _ => b) (𝓝[>] a)
    (completed_measurableSet measurableSet_Ioc)
  · filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hab).filter_mono
      nhdsWithin_le_nhds] with r hr hrb
    exact ⟨hR r ⟨hr, hrb.le⟩, fun x hx => ⟨hr.trans_le hx.1, hx.2⟩⟩
  · intro x hx
    filter_upwards [(eventually_lt_nhds hx.1).filter_mono nhdsWithin_le_nhds] with r hr
    exact ⟨hr.le, hx.2⟩

theorem right_singular : Specs.D11.Ch16.AbsoluteImproperBridge.right_singular := by
  intro 𝕜 _ _ _ f a b hab hR
  apply exhaustion_bridge f (Ico a b) (fun _ => a) id (𝓝[<] b)
    (completed_measurableSet measurableSet_Ico)
  · filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hab).filter_mono
      nhdsWithin_le_nhds] with R hRlt haR
    exact ⟨hR R ⟨haR.le, hRlt⟩, fun x hx => ⟨hx.1, hx.2.trans_lt hRlt⟩⟩
  · intro x hx
    filter_upwards [(eventually_gt_nhds hx.2).filter_mono nhdsWithin_le_nhds] with R hRgt
    exact ⟨hx.1, hRgt.le⟩

lemma domains_union (a b : Option ℝ) (c : ℝ) (hc : c ∈ improperDomain a b) :
    leftDomain a c ∪ rightDomain b c = improperDomain a b := by
  cases a <;> cases b <;> ext x <;>
    simp_all only [leftDomain, rightDomain, improperDomain, mem_union,
      mem_Iic, mem_Ici, mem_Ioc, mem_Ico, mem_ofPred_eq] <;> grind

lemma left_domain_measurable (a : Option ℝ) (c : ℝ) :
    MeasurableSet[mL] (leftDomain a c) := by
  cases a
  · exact completed_measurableSet measurableSet_Iic
  · exact completed_measurableSet measurableSet_Ioc

lemma right_domain_measurable (b : Option ℝ) (c : ℝ) :
    MeasurableSet[mL] (rightDomain b c) := by
  cases b
  · exact completed_measurableSet measurableSet_Ici
  · exact completed_measurableSet measurableSet_Ico

lemma domains_aedisjoint (a b : Option ℝ) (c : ℝ) :
    AEDisjoint μL (leftDomain a c) (rightDomain b c) := by
  change μL (leftDomain a c ∩ rightDomain b c) = 0
  apply measure_mono_null (t := {c})
  · intro x hx
    have hl : x ≤ c := by
      cases a with
      | none => exact hx.1
      | some A => exact hx.1.2
    have hr : c ≤ x := by
      cases b with
      | none => exact hx.2
      | some B => exact hx.2.1
    exact le_antisymm hl hr
  · change (volume : Measure ℝ) {c} = 0
    simp

theorem two_sided : Specs.D11.Ch16.AbsoluteImproperBridge.two_sided := by
  intro 𝕜 _ _ _ f a b c hc hR
  classical
  have hU := domains_union a b c hc
  have hLm := left_domain_measurable a c
  have hRm := right_domain_measurable b c
  have hLs : leftDomain a c ⊆ improperDomain a b := by
    rw [← hU]; exact subset_union_left
  have hRs : rightDomain b c ⊆ improperDomain a b := by
    rw [← hU]; exact subset_union_right
  have hLB : Bridge f (leftDomain a c) id (fun _ => c) (leftFilter a) := by
    cases a with
    | none =>
      exact left_infinite f c (fun r hr => hR r c hr (fun x hx => hLs hx.2))
    | some A =>
      have hAc : A < c := hc.1
      exact left_singular f A c hAc (fun r hr =>
        hR r c hr.2 (fun x hx => hLs ⟨hr.1.trans_le hx.1, hx.2⟩))
  have hRB : Bridge f (rightDomain b c) (fun _ => c) id (rightFilter b) := by
    cases b with
    | none =>
      exact right_infinite f c (fun r hr => hR c r hr (fun x hx => hRs hx.1))
    | some B =>
      have hcB : c < B := hc.2
      exact right_singular f c B hcB (fun r hr =>
        hR c r hr.1 (fun x hx => hRs ⟨hx.1, hx.2.trans_lt hr.2⟩))
  have hSm : MeasurableSet[mL] (improperDomain a b) := by
    rw [← hU]; exact hLm.union hRm
  have hfm : @Measurable ℝ 𝕜 mL _ ((improperDomain a b).indicator f) := by
    have heq : (improperDomain a b).indicator f =
        (leftDomain a c).piecewise ((leftDomain a c).indicator f)
          ((rightDomain b c).indicator f) := by
      ext x
      rw [← hU]
      by_cases hl : x ∈ leftDomain a c <;>
        by_cases hr : x ∈ rightDomain b c <;> simp [hl, hr]
    rw [heq]
    exact Measurable.piecewise hLm hLB.1 hRB.1
  have hd := domains_aedisjoint a b c
  refine ⟨hLB, hRB, hfm, ?_, ?_, ?_⟩
  · rw [← hU, Measure.restrict_union₀ hd hRm.nullMeasurableSet, lintegral_add_measure]
  · rw [inL1_iff f _ hfm hSm, ← hU, integrableOn_union,
      ← inL1_iff f _ hLB.1 hLm, ← inL1_iff f _ hRB.1 hRm]
    exact and_congr hLB.2.2.1.symm hRB.2.2.1.symm
  · intro hL
    have hi := (inL1_iff f _ hfm hSm).mp hL
    have hparts : IntegrableOn f (leftDomain a c) μL ∧
        IntegrableOn f (rightDomain b c) μL := by
      apply integrableOn_union.mp
      rwa [hU]
    have hl := (inL1_iff f _ hLB.1 hLm).mpr hparts.1
    have hr := (inL1_iff f _ hRB.1 hRm).mpr hparts.2
    refine ⟨∫ x in leftDomain a c, f x ∂μL,
      ∫ x in rightDomain b c, f x ∂μL, ?_, ?_, ?_⟩
    · have hh := hLB.2.2.2 hl
      change Tendsto _ _ (𝓝 (∫ x, (leftDomain a c).indicator f x ∂μL)) at hh
      rwa [integral_indicator hLm] at hh
    · have hh := hRB.2.2.2 hr
      change Tendsto _ _ (𝓝 (∫ x, (rightDomain b c).indicator f x ∂μL)) at hh
      rwa [integral_indicator hRm] at hh
    · change (∫ x, (improperDomain a b).indicator f x ∂μL) = _
      rw [integral_indicator hSm, ← hU]
      exact setIntegral_union₀ hd hRm.nullMeasurableSet hparts.1 hparts.2

lemma real_constant_riemann (z a b : ℝ) (hab : a ≤ b) :
    RealRiemann (fun _ : ℝ => z) a b := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    exact realIntegrable_degenerate _ a
  · apply (D11.Ch16.RiemannCriterion.riemann_criterion _ a b hab
      ⟨⟨z, by rintro _ ⟨x, hx, rfl⟩; rfl⟩,
       ⟨z, by rintro _ ⟨x, hx, rfl⟩; rfl⟩⟩).mpr
    have he : {x : ℝ | x ∈ Icc a b ∧ ¬ ContinuousWithinAt (fun _ : ℝ => z) (Icc a b) x} = ∅ := by
      ext x
      simp [continuousWithinAt_const]
    rw [he]
    exact measure_empty

theorem real_input : Specs.D11.Ch16.AbsoluteImproperBridge.real_input := by
  intro f a b
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, real_constant_riemann 0 a b h.choose⟩

theorem real_value : Specs.D11.Ch16.AbsoluteImproperBridge.real_value := by
  intro f a b h
  rw [properValue, dite_eq_left ((real_input f a b).mpr h)]
  change realValue f h + _ * (0 : ℝ) = realValue f h
  simp

theorem complex_input : Specs.D11.Ch16.AbsoluteImproperBridge.complex_input := by
  intro f a b
  rfl

theorem complex_value : Specs.D11.Ch16.AbsoluteImproperBridge.complex_value := by
  intro f a b h
  rw [properValue, dite_eq_left ((complex_input f a b).mpr h)]
  rfl

end D11.Ch16.AbsoluteImproperBridge
