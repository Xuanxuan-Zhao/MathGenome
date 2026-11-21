import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.CompositionMeasurabilityFailure
import MathGenome.Internal.RealAnalysis.D11.Ch03.PositiveOuterNonmeasurable
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcPrimitive
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic.NormNum

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace D11.Ch09.CompositionMeasurabilityFailure

open Specs.D11.Ch09.CompositionMeasurabilityFailure

/-- A closed nowhere dense positive-measure subset of the real unit interval.
A small open neighborhood of a countable dense set leaves such a set. -/
lemma exists_closed_nowhereDense_positive :
    ∃ K : Set ℝ, K ⊆ Icc 0 1 ∧ IsClosed K ∧ IsNowhereDense K ∧ 0 < volume K := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ
  have hDz : volume D = 0 := hDc.measure_zero volume
  obtain ⟨U, hDU, hUo, hUm⟩ := D.exists_isOpen_lt_of_lt (μ := volume) (1 / 2)
    (by rw [hDz]; norm_num)
  refine ⟨Icc 0 1 \ U, sdiff_subset, isClosed_Icc.sdiff hUo,
    ((isClosed_compl_and_isNowhereDense_compl.mpr ⟨hUo, hDd.mono hDU⟩).2).mono
      (sdiff_subset_compl _ _), ?_⟩
  have hsum := measure_sdiff_add_inter (Icc (0 : ℝ) 1) hUo.measurableSet (μ := volume)
  have hi : volume (Icc (0 : ℝ) 1 ∩ U) < 1 / 2 :=
    (measure_mono inter_subset_right).trans_lt hUm
  have hunit : volume (Icc (0 : ℝ) 1) = 1 := by simp
  rw [hunit] at hsum
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, zero_add] at hsum
  rw [hsum] at hi
  norm_num at hi

lemma density_integrable {K : Set ℝ} (hK : IsClosed K) : Integrable (density K) := by
  exact ((integrableOn_const (C := (1 : ℝ)) (μ := volume)
    (s := Icc (0 : ℝ) 1) (by simp)).mono_set sdiff_subset).integrable_indicator
      (measurableSet_Icc.diff hK.measurableSet)

lemma density_nonneg (K : Set ℝ) (x : ℝ) : 0 ≤ density K x := by
  exact indicator_nonneg (fun _ _ => zero_le_one) x

lemma density_norm_le (K : Set ℝ) (x : ℝ) : ‖density K x‖ ≤ 1 := by
  simpa [density] using (norm_indicator_le_norm_self (s := Icc 0 1 \ K) (fun _ : ℝ => (1 : ℝ)) x)

lemma primitive_increment {K : Set ℝ} (hK : IsClosed K) (x y : ℝ) :
    primitive K y - primitive K x = ∫ t in x..y, density K t := by
  exact intervalIntegral.integral_interval_sub_left
    (density_integrable hK).intervalIntegrable (density_integrable hK).intervalIntegrable

lemma primitive_lipschitz {K : Set ℝ} (hK : IsClosed K) :
    LipschitzWith 1 (primitive K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, ← Real.norm_eq_abs, primitive_increment hK]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => density_norm_le K t)

lemma primitive_ac {K : Set ℝ} (hK : IsClosed K) :
    D11.Ch12.AbsolutelyContinuousOnInterval (primitive K) 0 1 := by
  have h := D11.Ch12.AcPrimitive.primitive_ac (density K) (0 : ℝ)
    (by norm_num : (0 : ℝ) < 1) (density_integrable hK).integrableOn
  have heq : Specs.D11.Ch12.AcPrimitive.primitive_value (density K) (0 : ℝ) 0 =
      primitive K := by
    funext x
    simp [Specs.D11.Ch12.AcPrimitive.primitive_value, primitive]
  rw [heq] at h
  exact h

/-- Every open interval in the unit interval contains a positive-measure
part of the complement, making the prescribed primitive strictly increasing. -/
lemma primitive_strictMonoOn {K : Set ℝ} (hK : IsClosed K) (hn : IsNowhereDense K) :
    StrictMonoOn (primitive K) (Icc 0 1) := by
  intro x hx y hy hxy
  have hdense : Dense Kᶜ := (isClosed_isNowhereDense_iff_compl.mp ⟨hK, hn⟩).2
  have hne : (Ioo x y \ K).Nonempty :=
    hdense.inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.mpr hxy)
  have hpos : 0 < volume (Ioo x y \ K) :=
    (isOpen_Ioo.sdiff hK).measure_pos volume hne
  have hsub : Ioo x y \ K ⊆ Function.support (density K) ∩ Ioc x y := by
    intro t ht
    refine ⟨?_, ht.1.1, ht.1.2.le⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans ht.1.1.le, ht.1.2.le.trans hy.2⟩
    simp [density, htI, ht.2]
  have hi : 0 < ∫ t in x..y, density K t :=
    (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (density_nonneg K)) (density_integrable hK).intervalIntegrable).mpr
      ⟨hxy, hpos.trans_le (measure_mono hsub)⟩
  exact sub_pos.mp ((primitive_increment hK x y).symm ▸ hi)

/-- A Lipschitz real map preserves outer-null sets, including non-Borel sets. -/
lemma lipschitz_image_null {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {N : Set ℝ} (hN : volume N = 0) : volume (f '' N) = 0 := by
  have h := hf.hausdorffMeasure_image_le (d := 1) (by norm_num) N
  rw [hausdorffMeasure_real, hN] at h
  simpa using h

/-- The derivative is zero almost everywhere on K. The null exceptional
set is kept separate, and is sent to a null set by the Lipschitz bound.
Sard's lemma handles the remaining points without a measurability premise. -/
lemma primitive_image_null {K : Set ℝ} (hKI : K ⊆ Icc 0 1) (hK : IsClosed K) :
    volume (primitive K '' K) = 0 := by
  let F := primitive K
  have hd := D11.Ch12.AcPrimitive.primitive_derivative (density K) (0 : ℝ)
    (by norm_num : (0 : ℝ) < 1) (density_integrable hK).integrableOn
  have hz : ∀ᵐ x ∂volume, x ∈ K → HasDerivAt F 0 x := by
    filter_upwards [hd, show ∀ᵐ x ∂volume, x ≠ (0 : ℝ) from by simp [ae_iff],
      show ∀ᵐ x ∂volume, x ≠ (1 : ℝ) from by simp [ae_iff]] with x hx hx0 hx1 hxK
    have hxi : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne (hKI hxK).1 hx0.symm, lt_of_le_of_ne (hKI hxK).2 hx1⟩
    have heq : Specs.D11.Ch12.AcPrimitive.primitive_value (density K) (0 : ℝ) 0 = F := by
      funext t
      simp [Specs.D11.Ch12.AcPrimitive.primitive_value, F, primitive]
    rw [heq] at hx
    simpa [density, hxK] using hx hxi
  let G := {x ∈ K | HasDerivAt F 0 x}
  have hbad : volume (K \ G) = 0 := by
    have heq : K \ G = {x | ¬ (x ∈ K → HasDerivAt F 0 x)} := by
      ext x
      simp only [G, Set.mem_sdiff, mem_ofPred_eq, not_imp]
      tauto
    rw [heq]
    exact ae_iff.mp hz
  have himG : volume (F '' G) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
    · intro x hx
      simpa using hx.2.hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      simp
  have himB : volume (F '' (K \ G)) = 0 :=
    lipschitz_image_null (primitive_lipschitz hK) hbad
  apply measure_mono_null (t := F '' G ∪ F '' (K \ G))
  · rw [← image_union, union_sdiff_cancel (show G ⊆ K from fun _ h => h.1)]
  · exact measure_union_null himG himB

/-- Injectivity on the displayed domain gives the exact inverse image. -/
lemma preimage_image_on_interval {F : ℝ → ℝ} (hF : StrictMonoOn F (Icc 0 1))
    {A : Set ℝ} (hAI : A ⊆ Icc 0 1) : Icc 0 1 ∩ F ⁻¹' (F '' A) = A := by
  ext x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    have heq := hF.injOn (hAI hy) hx hyx
    exact heq ▸ hy
  · intro hx
    exact ⟨hAI hx, x, hx, rfl⟩

/-- A measurable interval composition would make its one-level set
Lebesgue measurable in the ambient line, contradicting the chosen subset. -/
lemma indicator_composition_not_measurable {F : ℝ → ℝ} {E A : Set ℝ}
    (hAI : A ⊆ Icc 0 1) (hA : ¬ NullMeasurableSet A (volume : Measure ℝ))
    (hpre : Icc 0 1 ∩ F ⁻¹' E = A) :
    ¬ @Measurable (Icc (0 : ℝ) 1) ℝ unitLebesgueSpace inferInstance
      (fun x => E.indicator (fun _ => (1 : ℝ)) (F x)) := by
  intro hm
  have hlevel := hm (measurableSet_singleton (1 : ℝ))
  have heq : (fun x : Icc (0 : ℝ) 1 => E.indicator (fun _ => (1 : ℝ)) (F x)) ⁻¹' {1} =
      Subtype.val ⁻¹' A := by
    ext x
    have hh : (x : ℝ) ∈ A ↔ F x ∈ E := by
      rw [← hpre]
      simp only [mem_inter_iff, x.property, mem_preimage, true_and]
    simp only [mem_preimage, mem_singleton_iff]
    by_cases hx : F x ∈ E <;> simp [hx, hh]
  rw [heq] at hlevel
  obtain ⟨B, hB, hBeq⟩ := hlevel
  have hAB : Icc (0 : ℝ) 1 ∩ B = A := by
    ext x
    constructor
    · rintro ⟨hx, hxB⟩
      have hsub : (⟨x, hx⟩ : Icc (0 : ℝ) 1) ∈ Subtype.val ⁻¹' A := by
        rw [← hBeq]
        exact hxB
      exact hsub
    · intro hx
      refine ⟨hAI hx, ?_⟩
      have hsub : (⟨x, hAI hx⟩ : Icc (0 : ℝ) 1) ∈ Subtype.val ⁻¹' B := by
        rw [hBeq]
        exact hx
      exact hsub
  apply hA
  rw [← hAB]
  exact measurableSet_Icc.nullMeasurableSet.inter hB

/-- The full counterexample from paper.tex:3247–3267, for completed
Lebesgue measure and the trace completion on the source interval. -/
theorem counterexample : Specs.D11.Ch09.CompositionMeasurabilityFailure.counterexample := by
  obtain ⟨K, hKI, hK, hn, hpos⟩ := exists_closed_nowhereDense_positive
  obtain ⟨A, hAK, hA⟩ :=
    D11.Ch03.PositiveOuterNonmeasurable.positive_set_nonmeasurable_subset K hpos
  let F := primitive K
  let E := F '' A
  have hAI : A ⊆ Icc 0 1 := hAK.trans hKI
  have hmono : StrictMonoOn F (Icc 0 1) := primitive_strictMonoOn hK hn
  have hcont : Continuous F := (primitive_lipschitz hK).continuous
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hK hKI
  have hnull : volume (F '' K) = 0 := primitive_image_null hKI hK
  have hEK : E ⊆ F '' K := image_mono hAK
  have hE0 : volume E = 0 := measure_mono_null hEK hnull
  have hEm : NullMeasurableSet E (volume : Measure ℝ) := NullMeasurableSet.of_null hE0
  have hpre : Icc 0 1 ∩ F ⁻¹' E = A := preimage_image_on_interval hmono hAI
  refine ⟨K, A, hKI, hK, hn, hpos, hAK, hA, primitive_ac hK,
    hcont, hmono, hKcompact.image hcont, hnull, hEK, hEm, hE0, hpre, ?_, ?_, ?_⟩
  · rwa [hpre]
  · exact measurable_const.indicator hEm
  · exact indicator_composition_not_measurable hAI hA hpre

end D11.Ch09.CompositionMeasurabilityFailure
