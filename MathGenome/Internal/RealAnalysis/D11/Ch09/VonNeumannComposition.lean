import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.VonNeumannComposition
import MathGenome.Internal.RealAnalysis.D11.Ch12.MonotoneNullImageCharacterization
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

noncomputable section
open Set MeasureTheory

namespace D11.Ch09.VonNeumannComposition

/-- Inclusion of an interval into completed Lebesgue space is a measurable
embedding. This identifies trace measurability with ambient completed
measurability of the image, including arbitrary subsets of null sets. -/
lemma interval_embedding (a b : ℝ) :
    @MeasurableEmbedding (Icc a b) (NullMeasurableSpace ℝ volume)
      (intervalSigma a b) inferInstance Subtype.val := by
  exact MeasurableEmbedding.subtype_coe measurableSet_Icc.nullMeasurableSet

lemma inverseExtension_apply {a b c d : ℝ} (h : Icc a b → Icc c d)
    (hm : StrictMono h) (hs : Function.Surjective h) (y : Icc c d) :
    inverseExtension h hm hs y = ((hm.orderIsoOfSurjective h hs).symm y : ℝ) := by
  simp [inverseExtension, y.property]

lemma inverseExtension_continuousOn {a b c d : ℝ} (h : Icc a b → Icc c d)
    (hm : StrictMono h) (hs : Function.Surjective h) :
    ContinuousOn (inverseExtension h hm hs) (Icc c d) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := continuous_subtype_val.comp (hm.orderIsoOfSurjective h hs).symm.continuous
  exact hc.congr (fun y => (inverseExtension_apply h hm hs y).symm)

lemma inverseExtension_monotoneOn {a b c d : ℝ} (h : Icc a b → Icc c d)
    (hm : StrictMono h) (hs : Function.Surjective h) :
    MonotoneOn (inverseExtension h hm hs) (Icc c d) := by
  intro x hx y hy hxy
  rw [show inverseExtension h hm hs x =
    ((hm.orderIsoOfSurjective h hs).symm ⟨x, hx⟩ : ℝ) from inverseExtension_apply h hm hs ⟨x, hx⟩,
    show inverseExtension h hm hs y =
    ((hm.orderIsoOfSurjective h hs).symm ⟨y, hy⟩ : ℝ) from inverseExtension_apply h hm hs ⟨y, hy⟩]
  exact (hm.orderIsoOfSurjective h hs).symm.monotone hxy

/-- The inverse's image is exactly the original map's inverse image, with
the subtype inclusion displayed on both sides. -/
lemma inverseExtension_image {a b c d : ℝ} (h : Icc a b → Icc c d)
    (hm : StrictMono h) (hs : Function.Surjective h)
    (E : Set ℝ) (hE : E ⊆ Icc c d) :
    inverseExtension h hm hs '' E =
      Subtype.val '' (h ⁻¹' ((Subtype.val : Icc c d → ℝ) ⁻¹' E)) := by
  let e := hm.orderIsoOfSurjective h hs
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e.symm ⟨y, hE hy⟩, ?_, ?_⟩
    · change (h (e.symm ⟨y, hE hy⟩) : ℝ) ∈ E
      have hv := congrArg Subtype.val (e.apply_symm_apply ⟨y, hE hy⟩)
      change (h (e.symm ⟨y, hE hy⟩) : ℝ) = y at hv
      rwa [hv]
    · exact (inverseExtension_apply h hm hs ⟨y, hE hy⟩).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨h z, hz, ?_⟩
    rw [inverseExtension_apply]
    exact congrArg Subtype.val (e.symm_apply_apply z)

/-- The scalar test is precisely measurability of h between the completed
interval sigma-algebras. Indicators test every target measurable set. -/
lemma preserves_real_iff_measurable {a b c d : ℝ} (h : Icc a b → Icc c d) :
    PreservesComposition ℝ h ↔
      @Measurable _ _ (intervalSigma a b) (intervalSigma c d) h := by
  letI : MeasurableSpace (Icc a b) := intervalSigma a b
  letI : MeasurableSpace (Icc c d) := intervalSigma c d
  constructor
  · intro hp S hS
    have hcomp := hp (S.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hS)
    apply (measurable_indicator_const_iff (s := h ⁻¹' S) (1 : ℝ)).mp
    have heq : (h ⁻¹' S).indicator (fun _ => (1 : ℝ)) =
        (S.indicator (fun _ => (1 : ℝ))) ∘ h := by
      rfl
    rw [heq]
    exact hcomp
  · intro hh g hg
    exact hg.comp hh

lemma measurable_iff_inverse_measurableImages {a b c d : ℝ}
    (h : Icc a b → Icc c d) (hm : StrictMono h) (hs : Function.Surjective h) :
    @Measurable _ _ (intervalSigma a b) (intervalSigma c d) h ↔
      Ch12.MonotoneNullImageCharacterization.MeasurableImagesOn
        (inverseExtension h hm hs) (Icc c d) := by
  letI : MeasurableSpace (Icc a b) := intervalSigma a b
  letI : MeasurableSpace (Icc c d) := intervalSigma c d
  constructor
  · intro hh E hE hmE
    rw [inverseExtension_image h hm hs E hE]
    exact (interval_embedding a b).measurableSet_image'
      (hh ((interval_embedding c d).measurable hmE))
  · intro hI S hS
    have hE := (interval_embedding c d).measurableSet_image' hS
    have him := hI (Subtype.val '' S) (by rintro y ⟨x, _, rfl⟩; exact x.property) hE
    rw [inverseExtension_image h hm hs _ (by rintro y ⟨x, _, rfl⟩; exact x.property),
      Subtype.val_injective.preimage_image] at him
    exact (interval_embedding a b).measurableSet_image.mp him

/-- Both implications use the upstream image characterization on the genuine
continuous monotone inverse, not on the original map. -/
theorem real_criterion : Specs.D11.Ch09.VonNeumannComposition.real_criterion := by
  intro a b c d _hab hcd h _hc hm hs
  have hc := inverseExtension_continuousOn h hm hs
  have hmono := inverseExtension_monotoneOn h hm hs
  have hchar := Ch12.MonotoneNullImageCharacterization.characterization
    (inverseExtension h hm hs) hcd hc hmono
  exact (preserves_real_iff_measurable h).trans
    ((measurable_iff_inverse_measurableImages h hm hs).trans (hchar.1.trans hchar.2).symm)

/-- The componentwise bridge works on the exact trace sigma-algebras. -/
lemma complex_iff_real {a b c d : ℝ} (h : Icc a b → Icc c d) :
    PreservesComposition ℂ h ↔ PreservesComposition ℝ h := by
  letI : MeasurableSpace (Icc a b) := intervalSigma a b
  letI : MeasurableSpace (Icc c d) := intervalSigma c d
  constructor
  · intro hp g hg
    have hgC : Measurable (fun y => (g y : ℂ)) := RCLike.measurable_ofReal.comp hg
    have hcomp := (hp _ hgC).re
    simpa only [IntervalMeasurable, Function.comp_def, RCLike.re_to_complex, Complex.ofReal_re] using hcomp
  · intro hp g hg
    exact measurable_of_re_im (hp _ hg.re) (hp _ hg.im)

theorem complex_criterion : Specs.D11.Ch09.VonNeumannComposition.complex_criterion := by
  intro a b c d hab hcd h hc hm hs
  exact (complex_iff_real h).trans (real_criterion hab hcd h hc hm hs)

/-- Restriction and extension by zero compare the two test classes for any
measurable target with a zero, hence for both real and complex scalars. -/
lemma wholeLine_iff_interval {K : Type*} [MeasurableSpace K] [Zero K]
    {a b c d : ℝ} (h : Icc a b → Icc c d) :
    PreservesWholeLineComposition K h ↔ PreservesComposition K h := by
  letI : MeasurableSpace (Icc a b) := intervalSigma a b
  letI : MeasurableSpace (Icc c d) := intervalSigma c d
  constructor
  · intro hp g hg
    let G : ℝ → K := Function.extend (Subtype.val : Icc c d → ℝ) g (fun _ => 0)
    have hG : NullMeasurable G volume :=
      (interval_embedding c d).measurable_extend hg measurable_const
    have heq : (fun x : Icc a b => G (h x)) = g ∘ h := by
      funext x
      exact Subtype.val_injective.extend_apply _ _ (h x)
    exact heq ▸ hp G hG
  · intro hp g hg
    have hrestrict : IntervalMeasurable (fun y : Icc c d => g y) :=
      hg.measurable'.comp (interval_embedding c d).measurable
    exact hp _ hrestrict

theorem real_wholeLine_iff_interval :
    Specs.D11.Ch09.VonNeumannComposition.real_wholeLine_iff_interval := by
  intro a b c d h
  exact wholeLine_iff_interval h

theorem complex_wholeLine_iff_interval :
    Specs.D11.Ch09.VonNeumannComposition.complex_wholeLine_iff_interval := by
  intro a b c d h
  exact wholeLine_iff_interval h

theorem real_wholeLine_criterion :
    Specs.D11.Ch09.VonNeumannComposition.real_wholeLine_criterion := by
  intro a b c d hab hcd h hc hm hs
  exact (wholeLine_iff_interval h).trans (real_criterion hab hcd h hc hm hs)

theorem complex_wholeLine_criterion :
    Specs.D11.Ch09.VonNeumannComposition.complex_wholeLine_criterion := by
  intro a b c d hab hcd h hc hm hs
  exact (wholeLine_iff_interval h).trans (complex_criterion hab hcd h hc hm hs)

end D11.Ch09.VonNeumannComposition
