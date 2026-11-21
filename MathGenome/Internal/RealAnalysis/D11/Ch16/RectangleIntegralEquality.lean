import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.RectangleIntegralEquality
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge

/-! The published calculus bridge is for the literal coordinate-grid Darboux
integral, not an iterated integral or a totalized Lebesgue definition. Its
`box_bridge` proves the null measurability of the original representative,
absolute integrability, and equality with Borel-volume integration. The trim
lemmas below explicitly transfer these facts to the Borel completion.
No change of variables theorem is used. -/
noncomputable section
open Set MeasureTheory
namespace D11.Ch16.RectangleIntegralEquality

open D04.Darboux
open Specs.D11.Ch16.RectangleIntegralEquality

variable {n : ℕ}

lemma completion_trim (n : ℕ) :
    (completedMeasure n).trim
      (show (inferInstance : MeasurableSpace (D04.E n)) ≤ completedSpace n from
        fun _ hs => hs.nullMeasurableSet) = (volume : Measure (D04.E n)) := by
  ext s hs
  rw [trim_measurableSet_eq _ hs]
  rfl

lemma integrable_completion {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : D04.E n → 𝕜} (hf : MeasureTheory.Integrable f volume) :
    MeasureTheory.Integrable f (completedMeasure n) := by
  have hm : (inferInstance : MeasurableSpace (D04.E n)) ≤ completedSpace n :=
    fun _ hs => hs.nullMeasurableSet
  apply integrable_of_integrable_trim hm
  simpa only [completion_trim] using hf

lemma integral_completion {𝕜 : Type*} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : D04.E n → 𝕜} (hf : MeasureTheory.Integrable f volume) :
    (∫ x, f x ∂completedMeasure n) = ∫ x, f x := by
  have hm : (inferInstance : MeasurableSpace (D04.E n)) ≤ completedSpace n :=
    fun _ hs => hs.nullMeasurableSet
  have hfm : AEStronglyMeasurable f ((completedMeasure n).trim hm) := by
    simpa only [completion_trim] using hf.aestronglyMeasurable
  simpa only [completion_trim] using integral_trim_ae hm hfm

theorem real_rectangle_equality :
    Specs.D11.Ch16.RectangleIntegralEquality.real_rectangle_equality := by
  intro n _ Q f hR
  obtain ⟨hm, hi, he⟩ := D04.MeasureBridge.box_bridge f Q hR
  have hiC := integrable_completion hi
  have hL := (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff
    (D04.E n) ℝ (completedSpace n) _ (borel ℝ) inferInstance
    (completedMeasure n) ((carrier Q).indicator f)).mpr ⟨hm.measurable', hiC⟩
  refine ⟨hL, ?_⟩
  change integral f Q hR = ∫ x, (carrier Q).indicator f x ∂completedMeasure n
  rw [integral_completion hi, integral_indicator (D04.MeasureBridge.measurableSet_carrier Q)]
  exact he

theorem complex_rectangle_equality :
    Specs.D11.Ch16.RectangleIntegralEquality.complex_rectangle_equality := by
  intro n _ Q f hr hi
  obtain ⟨hRe, er⟩ := real_rectangle_equality n Q (fun x => (f x).re) hr
  obtain ⟨hIm, ei⟩ := real_rectangle_equality n Q (fun x => (f x).im) hi
  have hReEq : (fun x => ((carrier Q).indicator f x).re) =
      (carrier Q).indicator (fun x => (f x).re) := by
    ext x
    by_cases hx : x ∈ carrier Q <;> simp [hx]
  have hImEq : (fun x => ((carrier Q).indicator f x).im) =
      (carrier Q).indicator (fun x => (f x).im) := by
    ext x
    by_cases hx : x ∈ carrier Q <;> simp [hx]
  have hL := (@D11.Ch06.ScalarIntegral.complex_integrable_iff_coordinates
    (D04.E n) (completedSpace n) (completedMeasure n) ((carrier Q).indicator f)).mpr
      ⟨by simpa only [hReEq] using hRe, by simpa only [hImEq] using hIm⟩
  refine ⟨hL, ?_⟩
  have hint := (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff
    (D04.E n) ℂ (completedSpace n) _ (borel ℂ) inferInstance
    (completedMeasure n) ((carrier Q).indicator f)).mp hL |>.2
  have heq : (∫ x, (carrier Q).indicator f x ∂completedMeasure n) =
      ((∫ x, (carrier Q).indicator (fun x => (f x).re) x ∂completedMeasure n : ℝ) : ℂ) +
      ((∫ x, (carrier Q).indicator (fun x => (f x).im) x ∂completedMeasure n : ℝ) : ℂ) *
        Complex.I := by
    simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
      RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal, hReEq, hImEq]
      using (@integral_re_add_im (D04.E n) (completedSpace n) (completedMeasure n)
        ℂ inferInstance ((carrier Q).indicator f) hint).symm
  apply Eq.trans _ heq.symm
  exact congrArg₂ (fun r i : ℝ => (r : ℂ) + (i : ℂ) * Complex.I) er ei

theorem real_degenerate : Specs.D11.Ch16.RectangleIntegralEquality.real_degenerate := by
  intro n _ Q hQ f hf
  have hz := degenerate_integrals f Q hQ
  have hR : D04.Darboux.Integrable f Q := ⟨hf, hz.1.trans hz.2.symm⟩
  obtain ⟨hL, he⟩ := real_rectangle_equality n Q f hR
  exact ⟨hR, hL, hz.1, he.symm.trans hz.1⟩

theorem complex_degenerate : Specs.D11.Ch16.RectangleIntegralEquality.complex_degenerate := by
  intro n _ Q hQ f hfr hfi
  have hzr := degenerate_integrals (fun x => (f x).re) Q hQ
  have hzi := degenerate_integrals (fun x => (f x).im) Q hQ
  have hr : D04.Darboux.Integrable (fun x => (f x).re) Q := ⟨hfr, hzr.1.trans hzr.2.symm⟩
  have hi : D04.Darboux.Integrable (fun x => (f x).im) Q := ⟨hfi, hzi.1.trans hzi.2.symm⟩
  obtain ⟨hL, he⟩ := complex_rectangle_equality n Q f hr hi
  have hz : (integral (fun x => (f x).re) Q hr : ℂ) +
      (integral (fun x => (f x).im) Q hi : ℂ) * Complex.I = 0 := by
    change (lowerIntegral (fun x => (f x).re) Q : ℂ) +
      (lowerIntegral (fun x => (f x).im) Q : ℂ) * Complex.I = 0
    simp only [hzr.1, hzi.1, Complex.ofReal_zero, zero_mul, add_zero]
  exact ⟨hr, hi, hL, hz, he.symm.trans hz⟩

theorem coordinate_faces_null : Specs.D11.Ch16.RectangleIntegralEquality.coordinate_faces_null := by
  intro n _ Q i t
  have hz : (volume : Measure (D04.E n)) {x ∈ carrier Q | x i = t} = 0 := by
    apply measure_mono_null (D04.NullCovers.coordinateFace_subset Q i t)
    rw [D04.MeasureBridge.volume_carrier, D04.NullCovers.faceBox_content, ENNReal.ofReal_zero]
  exact ⟨(NullMeasurableSet.of_null hz), hz⟩

end D11.Ch16.RectangleIntegralEquality
