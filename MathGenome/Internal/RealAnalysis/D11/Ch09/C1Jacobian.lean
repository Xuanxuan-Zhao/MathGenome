import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueCompletion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.C1Jacobian

/-! The completed nonlinear Jacobian theorem (paper.tex:3082–3174).
The inverse function theorem constructs the open image and C¹ inverse.
Mathlib's Borel Jacobian theorem supplies the exact volume and integral
identities. The remaining arguments identify completed measurable sets with
null-measurable Borel sets, transfer the integrals through trim, and prove
measurability of the completed trace compositions using the inverse map.
No global regularity outside the open source is imposed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch09.C1Jacobian
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch09.C1Jacobian
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {n : ℕ} [NeZero n] {U : Set (Point n)} {G : Point n → Point n}

lemma C1Hypotheses.hasFDerivAt (H : C1Hypotheses U G) {x : Point n} (hx : x ∈ U) :
    HasFDerivAt G (fderiv ℝ G x) x :=
  ((H.contDiff x hx).contDiffAt (H.isOpen.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt

/-- Nonsingularity gives the actual continuous linear equivalence used by the IFT. -/
def derivativeEquiv (H : C1Hypotheses U G) (x : Point n) (hx : x ∈ U) :
    Point n ≃L[ℝ] Point n :=
  (LinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (H.det_ne_zero x hx))).toContinuousLinearEquiv

lemma derivativeEquiv_coe (H : C1Hypotheses U G) (x : Point n) (hx : x ∈ U) :
    (derivativeEquiv H x hx : Point n →L[ℝ] Point n) = fderiv ℝ G x := by
  ext z
  simp [derivativeEquiv]

lemma open_restrict (H : C1Hypotheses U G) : IsOpenMap (U.domRestrict G) := by
  intro s hs
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  have hc := (H.contDiff x x.2).contDiffAt (H.isOpen.mem_nhds x.2)
  have hd : HasFDerivAt G (derivativeEquiv H x x.2 : Point n →L[ℝ] Point n) x := by
    rw [derivativeEquiv_coe]
    exact C1Hypotheses.hasFDerivAt H x.2
  have hm := (hc.hasStrictFDerivAt' hd (by decide)).map_nhds_eq_of_equiv
  have ho : IsOpen ((↑) '' s : Set (Point n)) := H.isOpen.isOpenEmbedding_subtypeVal.isOpenMap s hs
  have hmem : (↑) '' s ∈ 𝓝 (x : Point n) := ho.mem_nhds ⟨x, hx, rfl⟩
  have him : G '' ((↑) '' s) ∈ 𝓝 (G x) := by
    rw [← hm]
    exact Filter.image_mem_map hmem
  have heq : G '' ((↑) '' s) = U.domRestrict G '' s := by
    rw [image_image]
    rfl
  rw [heq] at him
  exact him

theorem open_image_inverse : Specs.D11.Ch09.C1Jacobian.open_image_inverse := by
  intro n _ U G H
  let p := H.injOn.toPartialEquiv G U
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p H.contDiff.continuousOn
    (open_restrict H) H.isOpen
  have he : (e : Point n → Point n) = G := rfl
  have ht : e.target = G '' U := rfl
  refine ⟨ht ▸ e.open_target, e, rfl, he, ht, ?_⟩
  intro y hy
  have hx : e.symm y ∈ U := e.map_target hy
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm hy (f₀' := derivativeEquiv H (e.symm y) hx)
  · change HasFDerivAt G _ _
    rw [derivativeEquiv_coe]
    exact C1Hypotheses.hasFDerivAt H hx
  · exact (H.contDiff _ hx).contDiffAt (H.isOpen.mem_nhds hx)

lemma trim_lebesgue : (lebesgue n).trim (native_borel_le n) =
    (volume : Measure (Point n)) := borel_restriction n (native_borel_le n)

/-- Equality also on arbitrary subsets, hence on all null exceptional sets. -/
lemma lebesgue_eval (E : Set (Point n)) : lebesgue n E = volume E := by
  apply le_antisymm
  · calc
      lebesgue n E ≤ (lebesgue n).trim (native_borel_le n) E := le_trim _
      _ = volume E := congrArg (fun μ : Measure (Point n) => μ E)
        (borel_restriction n (native_borel_le n))
  · rw [native_outer_agreement n E]
    change (OuterVolume.outerVolume n) E ≤
      @OuterMeasure.toMeasure _ (lebesgueSpace n) (OuterVolume.outerVolume n) le_rfl E
    exact @le_toMeasure_apply (Point n) (lebesgueSpace n) (OuterVolume.outerVolume n) le_rfl E

lemma completed_measurableSet_iff (E : Set (Point n)) :
    MeasurableSet[lebesgueSpace n] E ↔ NullMeasurableSet E volume := by
  change MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value n] E ↔ _
  rw [LebesgueCompletion.completion_space n]
  rfl

lemma completed_measurable_iff {Y : Type*} [MeasurableSpace Y] (h : Point n → Y) :
    @Measurable (Point n) Y (lebesgueSpace n) _ h ↔ NullMeasurable h volume := by
  constructor <;> intro hh E hE
  · exact (completed_measurableSet_iff _).mp (hh hE)
  · exact (completed_measurableSet_iff _).mpr (hh hE)

lemma ae_completed_eq : ae (lebesgue n) = ae (volume : Measure (Point n)) := by
  ext p
  simp only [mem_ae_iff, lebesgue_eval]

lemma lintegral_completed {h : Point n → ℝ≥0∞} (hh : AEMeasurable h volume) :
    (∫⁻ x, h x ∂lebesgue n) = ∫⁻ x, h x := by
  have ht := lintegral_trim_ae (f := h) (μ := lebesgue n) (native_borel_le n)
  rw [trim_lebesgue] at ht
  exact (ht hh).symm

lemma lintegral_completed_on {h : Point n → ℝ≥0∞} {E : Set (Point n)}
    (hE : MeasurableSet E) (hh : AEMeasurable h (volume.restrict E)) :
    (∫⁻ x in E, h x ∂lebesgue n) = ∫⁻ x in E, h x := by
  have ht := lintegral_trim_ae (f := h) (μ := (lebesgue n).restrict E) (native_borel_le n)
  rw [← restrict_trim _ _ hE, trim_lebesgue] at ht
  exact (ht hh).symm

lemma integral_completed_on {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {h : Point n → 𝕜} {E : Set (Point n)} (hE : MeasurableSet E)
    (hh : AEStronglyMeasurable h (volume.restrict E)) :
    (∫ x in E, h x ∂lebesgue n) = ∫ x in E, h x := by
  have ht := integral_trim_ae (f := h) (μ := (lebesgue n).restrict E) (native_borel_le n)
  rw [← restrict_trim _ _ hE, trim_lebesgue] at ht
  exact ht hh

lemma integrable_completed_on {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {h : Point n → 𝕜} {E : Set (Point n)} (hE : MeasurableSet E)
    (hh : AEStronglyMeasurable h (volume.restrict E)) :
    IntegrableOn h E (lebesgue n) ↔ IntegrableOn h E volume := by
  have ht : ((lebesgue n).restrict E).trim (native_borel_le n) = volume.restrict E := by
    rw [← restrict_trim _ _ hE, trim_lebesgue]
  constructor
  · intro hi
    have ht' := hi.hasFiniteIntegral
    rw [HasFiniteIntegral, ← lintegral_trim_ae (native_borel_le n)] at ht'
    · rw [ht] at ht'
      exact ⟨hh, ht'⟩
    · rw [ht]
      exact hh.enorm
  · intro hi
    apply integrable_of_integrable_trim (native_borel_le n)
    rwa [ht]

/-- Differentiability and injectivity preserve the full completed measurable sets. -/
lemma completed_image_of_differentiable {S : Set (Point n)} {F : Point n → Point n}
    (hS : IsOpen S) (hF : DifferentiableOn ℝ F S) (hi : InjOn F S)
    {E : Set (Point n)} (hES : E ⊆ S) (hE : MeasurableSet[lebesgueSpace n] E) :
    MeasurableSet[lebesgueSpace n] (F '' E) := by
  apply (completed_measurableSet_iff _).mpr
  apply nullMeasurable_image_of_fderivWithin volume
    ((completed_measurableSet_iff E).mp hE) (f' := fderiv ℝ F) _ (hi.mono hES)
  intro x hx
  exact ((hF x (hES hx)).differentiableAt (hS.mem_nhds (hES hx))).hasFDerivAt.hasFDerivWithinAt

theorem measurable_image : Specs.D11.Ch09.C1Jacobian.measurable_image := by
  intro n _ U G H E hEU hE
  exact completed_image_of_differentiable H.isOpen (H.contDiff.differentiableOn (by simp))
    H.injOn hEU hE

/-- The inverse sends completed measurable subsets of the target to such subsets
of the source. This establishes actual measurability, including null subsets. -/
lemma completed_restrict_measurable (H : C1Hypotheses U G) :
    letI : MeasurableSpace (Point n) := lebesgueSpace n
    Measurable (U.domRestrict G) := by
  obtain ⟨_, e, hs, he, ht, hd⟩ := open_image_inverse n U G H
  have hvn : MeasurableSet e.target := e.open_target.measurableSet
  letI : MeasurableSpace (Point n) := lebesgueSpace n
  intro E hE
  have hVm : MeasurableSet e.target := native_borel_le n _ hvn
  have him : MeasurableSet (e.symm '' (E ∩ e.target)) :=
    completed_image_of_differentiable e.open_target (hd.differentiableOn (by simp))
      e.symm.injOn inter_subset_right (hE.inter hVm)
  have heq : (U.domRestrict G) ⁻¹' E =
      (Subtype.val : U → Point n) ⁻¹' (e.symm '' (E ∩ e.target)) := by
    ext x
    constructor
    · intro hx
      change G x ∈ E at hx
      refine ⟨e x, ⟨?_, e.map_source (hs.symm ▸ x.2)⟩, ?_⟩
      · simpa only [he] using hx
      · exact e.left_inv (hs.symm ▸ x.2)
    · rintro ⟨y, ⟨hyE, hyt⟩, hxy⟩
      have : G x = y := by
        rw [← he, ← hxy]
        exact e.right_inv hyt
      change G x ∈ E
      rwa [this]
  rw [heq]
  exact him.preimage measurable_subtype_coe

theorem completed_composition : Specs.D11.Ch09.C1Jacobian.completed_composition := by
  intro n _ U G H Y _ h hh
  letI : MeasurableSpace (Point n) := lebesgueSpace n
  let g : U → G '' U := fun x => ⟨G x, mem_image_of_mem G x.2⟩
  have hg : Measurable g := (completed_restrict_measurable H).subtype_mk
  exact hh.comp hg

lemma jacobian_continuousOn (H : C1Hypotheses U G) : ContinuousOn (jacobian G) U :=
  continuous_abs.comp_continuousOn
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (H.contDiff.continuousOn_fderiv_of_isOpen H.isOpen le_rfl))

lemma jacobian_measurable (H : C1Hypotheses U G) :
    letI : MeasurableSpace (Point n) := lebesgueSpace n
    Measurable (U.domRestrict (jacobian G)) := by
  have hm : Measurable (U.domRestrict (jacobian G)) :=
    (jacobian_continuousOn H).domRestrict.measurable
  exact hm.mono (MeasurableSpace.comap_mono (native_borel_le n)) le_rfl

/-- No Borel assumption on E is introduced in the set formula. -/
theorem set_jacobian : Specs.D11.Ch09.C1Jacobian.set_jacobian := by
  intro n _ U G H E hEU hE
  have hEn : NullMeasurableSet E volume := (completed_measurableSet_iff E).mp hE
  have hd : ∀ x ∈ E, HasFDerivWithinAt G (fderiv ℝ G x) E x :=
    fun x hx => (C1Hypotheses.hasFDerivAt H (hEU hx)).hasFDerivWithinAt
  have hn := lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hEn hd (H.injOn.mono hEU)
  change lebesgue n (G '' E) = ∫⁻ x in E, ENNReal.ofReal (jacobian G x) ∂lebesgue n
  rw [lebesgue_eval]
  rw [← hn]
  have hjE : AEMeasurable (fun x => ENNReal.ofReal (jacobian G x)) (volume.restrict E) :=
    (aemeasurable_ofReal_abs_det_fderivWithin volume
      H.isOpen.measurableSet (fun x hx => (C1Hypotheses.hasFDerivAt H hx).hasFDerivWithinAt)).mono_measure
        (Measure.restrict_mono_set volume hEU)
  have hji : AEMeasurable (E.indicator (fun x => ENNReal.ofReal (jacobian G x))) volume :=
    (aemeasurable_indicator_iff₀ hEn).mpr hjE
  exact (lintegral_indicator₀ (μ := volume) hEn _).symm.trans
    ((lintegral_completed hji).symm.trans (lintegral_indicator (μ := lebesgue n) hE _))

/-- A function measurable for a completed trace has an original Borel version
for the restricted measure. No condition is placed on its off-region values. -/
lemma native_aemeasurable_on {Y : Type*} [MeasurableSpace Y] [Zero Y]
    [MeasurableSpace.CountablyGenerated Y] {E : Set (Point n)} (hE : MeasurableSet E)
    {h : Point n → Y}
    (hh : @Measurable E Y (MeasurableSpace.comap Subtype.val (lebesgueSpace n)) _
      (E.domRestrict h)) : AEMeasurable h (volume.restrict E) := by
  classical
  have hm : @Measurable (Point n) Y (lebesgueSpace n) _ (E.indicator h) := by
    letI : MeasurableSpace (Point n) := lebesgueSpace n
    apply measurable_of_restrict_of_restrict_compl (native_borel_le n E hE)
    · have heq : E.domRestrict (E.indicator h) = E.domRestrict h := by
        ext x
        exact indicator_of_mem x.2 h
      rwa [heq]
    · have heq : Eᶜ.domRestrict (E.indicator h) = fun _ => (0 : Y) := by
        ext x
        exact indicator_of_notMem x.2 h
      rw [heq]
      exact measurable_const
  exact (aemeasurable_indicator_iff hE).mp
    (((completed_measurable_iff _).mp hm).aemeasurable)

lemma native_nonnegative_jacobian (H : C1Hypotheses U G) (h : Point n → ℝ≥0∞) :
    (∫⁻ y in G '' U, h y) = ∫⁻ x in U, ENNReal.ofReal (jacobian G x) * h (G x) :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul volume H.isOpen.measurableSet
    (fun _x hx => (C1Hypotheses.hasFDerivAt H hx).hasFDerivWithinAt) H.injOn h

lemma native_integrable_iff (H : C1Hypotheses U G) {𝕜 : Type} [RCLike 𝕜]
    (h : Point n → 𝕜) : IntegrableOn h (G '' U) volume ↔
      IntegrableOn (fun x => jacobian G x • h (G x)) U volume :=
  integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume H.isOpen.measurableSet
    (fun _x hx => (C1Hypotheses.hasFDerivAt H hx).hasFDerivWithinAt) H.injOn h

lemma native_scalar_jacobian (H : C1Hypotheses U G) {𝕜 : Type} [RCLike 𝕜]
    (h : Point n → 𝕜) :
    (∫ y in G '' U, h y) = ∫ x in U, jacobian G x • h (G x) :=
  integral_image_eq_integral_abs_det_fderiv_smul volume H.isOpen.measurableSet
    (fun _x hx => (C1Hypotheses.hasFDerivAt H hx).hasFDerivWithinAt) H.injOn h

theorem nonnegative_jacobian : Specs.D11.Ch09.C1Jacobian.nonnegative_jacobian := by
  intro n _ U G H
  have hUn : @MeasurableSet (Point n) inferInstance U := H.isOpen.measurableSet
  have hVn : @MeasurableSet (Point n) inferInstance (G '' U) :=
    (open_image_inverse n U G H).1.measurableSet
  letI : MeasurableSpace (Point n) := lebesgueSpace n
  intro h hh
  have hm : Measurable (U.domRestrict (fun x => ENNReal.ofReal (jacobian G x) * h (G x))) :=
    (jacobian_measurable H).ennreal_ofReal.mul (completed_composition n U G H _ h hh)
  refine ⟨hm, ?_⟩
  have hhV := native_aemeasurable_on hVn hh
  have hhU := native_aemeasurable_on hUn hm
  change (∫⁻ y in G '' U, h y ∂lebesgue n) =
    ∫⁻ x in U, ENNReal.ofReal (jacobian G x) * h (G x) ∂lebesgue n
  rw [lintegral_completed_on hVn hhV, lintegral_completed_on hUn hhU]
  exact native_nonnegative_jacobian H h

theorem scalar_integrable_iff : Specs.D11.Ch09.C1Jacobian.scalar_integrable_iff := by
  intro n _ U G H 𝕜 _ _ _
  have hUn : @MeasurableSet (Point n) inferInstance U := H.isOpen.measurableSet
  have hVn : @MeasurableSet (Point n) inferInstance (G '' U) :=
    (open_image_inverse n U G H).1.measurableSet
  letI : MeasurableSpace (Point n) := lebesgueSpace n
  intro h hh
  have hm : Measurable (U.domRestrict (fun x => jacobian G x • h (G x))) :=
    (jacobian_measurable H).smul (completed_composition n U G H _ h hh)
  refine ⟨hm, ?_⟩
  have hhV := (native_aemeasurable_on hVn hh).aestronglyMeasurable
  have hhU := (native_aemeasurable_on hUn hm).aestronglyMeasurable
  change IntegrableOn h (G '' U) (lebesgue n) ↔
    IntegrableOn (fun x => jacobian G x • h (G x)) U (lebesgue n)
  rw [integrable_completed_on hVn hhV, integrable_completed_on hUn hhU]
  exact native_integrable_iff H h

theorem scalar_jacobian : Specs.D11.Ch09.C1Jacobian.scalar_jacobian := by
  intro n _ U G H 𝕜 _ _ _
  have hUn : @MeasurableSet (Point n) inferInstance U := H.isOpen.measurableSet
  have hVn : @MeasurableSet (Point n) inferInstance (G '' U) :=
    (open_image_inverse n U G H).1.measurableSet
  letI : MeasurableSpace (Point n) := lebesgueSpace n
  intro h hh hi
  obtain ⟨hm, hiff⟩ := scalar_integrable_iff n U G H 𝕜 h hh
  refine ⟨hiff.mp hi, ?_⟩
  have hhV := (native_aemeasurable_on hVn hh).aestronglyMeasurable
  have hhU := (native_aemeasurable_on hUn hm).aestronglyMeasurable
  change (∫ y in G '' U, h y ∂lebesgue n) =
    ∫ x in U, jacobian G x • h (G x) ∂lebesgue n
  rw [integral_completed_on hVn hhV, integral_completed_on hUn hhU]
  exact native_scalar_jacobian H h

end D11.Ch09.C1Jacobian
