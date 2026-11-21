import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch05.MarkovZeroFinite
import MathGenome.Internal.RealAnalysis.D11.Ch04.ScalarOperationsLimits

/-! Scalar integrals on arbitrary positive measure spaces (paper.tex:1766–1803).
The public predicate retains actual measurability. The public integral takes
an integrability proof; its real/complex formulas identify the construction
with the earlier nonnegative integral. Extended-real infinities are reset to
zero on a measurable null set, without completing the measurable space. -/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace D11.Ch06.ScalarIntegral
open D11.Ch05.NonnegativeIntegral
open D11.Ch04.AeCommonException

def scalarIntegrable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜) : Prop :=
  Measurable f ∧ nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖) < ∞

def scalarIntegral {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜)
    (_ : scalarIntegrable μ f) : 𝕜 := ∫ x, f x ∂μ

def positivePart {X : Type u} (f : X → ℝ) (x : X) : ℝ := max (f x) 0

def negativePart {X : Type u} (f : X → ℝ) (x : X) : ℝ := max (-f x) 0

def extendedIntegrable {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (f : X → EReal) : Prop :=
  Measurable f ∧ nonnegativeIntegral μ (fun x => (f x).abs) < ∞

def finiteVersion {X : Type u} (f : X → EReal) (x : X) : ℝ := (f x).toReal

def extendedIntegral {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (f : X → EReal) (_ : extendedIntegrable μ f) : ℝ :=
  ∫ x, finiteVersion f x ∂μ

theorem scalarIntegrable_iff {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜) :
    scalarIntegrable μ f ↔ Measurable f ∧ Integrable f μ := by
  rw [scalarIntegrable, integral_eq_lintegral]
  constructor
  · rintro ⟨hm, hi⟩
    exact ⟨hm, hm.aestronglyMeasurable, (hasFiniteIntegral_iff_norm f).mpr hi⟩
  · rintro ⟨hm, hi⟩
    exact ⟨hm, (hasFiniteIntegral_iff_norm f).mp hi.hasFiniteIntegral⟩

theorem native_integrable_iff {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜) (hm : Measurable f) :
    scalarIntegrable μ f ↔ Integrable f μ := by
  exact (scalarIntegrable_iff μ f).trans (and_iff_right hm)

theorem parts_identities : Specs.D11.Ch06.ScalarIntegral.parts_identities := by
  intro X f x
  change 0 ≤ max (f x) 0 ∧ 0 ≤ max (-f x) 0 ∧
    |f x| = max (f x) 0 + max (-f x) 0 ∧ f x = max (f x) 0 - max (-f x) 0
  by_cases h : 0 ≤ f x
  · simp [h, abs_of_nonneg h]
  · have h' : f x ≤ 0 := le_of_not_ge h
    simp [h', abs_of_nonpos h']

theorem measurable_parts : Specs.D11.Ch06.ScalarIntegral.measurable_parts := by
  intro X _ f hf
  exact ⟨hf.max measurable_const, hf.neg.max measurable_const⟩

theorem real_integrable_iff_parts :
    Specs.D11.Ch06.ScalarIntegral.real_integrable_iff_parts := by
  intro X _ μ f hf
  change scalarIntegrable μ f ↔
    nonnegativeIntegral μ (fun x => ENNReal.ofReal (positivePart f x)) < ∞ ∧
    nonnegativeIntegral μ (fun x => ENNReal.ofReal (negativePart f x)) < ∞
  have hp_eq : (fun x => ENNReal.ofReal ‖positivePart f x‖) =
      (fun x => ENNReal.ofReal (positivePart f x)) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have hn_eq : (fun x => ENNReal.ofReal ‖negativePart f x‖) =
      (fun x => ENNReal.ofReal (negativePart f x)) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  constructor
  · intro h
    have hi := (native_integrable_iff μ f hf).mp h
    constructor
    · simpa only [hp_eq] using ((native_integrable_iff μ (positivePart f) (measurable_parts f hf).1).mpr
        hi.pos_part).2
    · simpa only [hn_eq] using ((native_integrable_iff μ (negativePart f) (measurable_parts f hf).2).mpr
        hi.neg_part).2
  · rintro ⟨hp, hn⟩
    have hip := (native_integrable_iff μ (positivePart f) (measurable_parts f hf).1).mp
      ⟨(measurable_parts f hf).1, by simpa only [hp_eq] using hp⟩
    have hin := (native_integrable_iff μ (negativePart f) (measurable_parts f hf).2).mp
      ⟨(measurable_parts f hf).2, by simpa only [hn_eq] using hn⟩
    apply (native_integrable_iff μ f hf).mpr
    have hparts : f = fun x => positivePart f x - negativePart f x :=
      funext (fun x => (parts_identities f x).2.2.2)
    rw [hparts]
    exact hip.sub hin

theorem real_integral_formula : Specs.D11.Ch06.ScalarIntegral.real_integral_formula := by
  intro X _ μ f hf
  change (∫ x, f x ∂μ) =
    (nonnegativeIntegral μ (fun x => ENNReal.ofReal (max (f x) 0))).toReal -
    (nonnegativeIntegral μ (fun x => ENNReal.ofReal (max (-f x) 0))).toReal
  have hi := (scalarIntegrable_iff μ f).mp hf |>.2
  simp only [integral_eq_lintegral]
  simpa using integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi

theorem complex_integrable_iff_coordinates :
    Specs.D11.Ch06.ScalarIntegral.complex_integrable_iff_coordinates := by
  intro X _ μ f
  change scalarIntegrable μ f ↔
    scalarIntegrable μ (fun x => (f x).re) ∧ scalarIntegrable μ (fun x => (f x).im)
  simp only [scalarIntegrable_iff]
  constructor
  · rintro ⟨hm, hi⟩
    exact ⟨⟨Complex.continuous_re.measurable.comp hm, hi.re⟩,
      ⟨Complex.continuous_im.measurable.comp hm, hi.im⟩⟩
  · rintro ⟨⟨hmr, hir⟩, ⟨hmi, hii⟩⟩
    exact ⟨(D11.Ch04.CompositionCoordinates.complex_coordinates _ f).mpr ⟨hmr, hmi⟩, Integrable.re_im_iff.mp ⟨hir, hii⟩⟩

theorem complex_integral_formula : Specs.D11.Ch06.ScalarIntegral.complex_integral_formula := by
  intro X _ μ f hf
  obtain ⟨hr, hi⟩ := (complex_integrable_iff_coordinates μ f).mp hf
  refine ⟨hr, hi, ?_⟩
  change (∫ x, f x ∂μ) =
    ((∫ x, (f x).re ∂μ : ℝ) : ℂ) + Complex.I * ((∫ x, (f x).im ∂μ : ℝ) : ℂ)
  have h := integral_re_add_im ((scalarIntegrable_iff μ f).mp hf).2
  simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im, RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal, mul_comm] using h.symm

theorem simple_nonzero_levels_finite :
    Specs.D11.Ch06.ScalarIntegral.simple_nonzero_levels_finite := by
  intro X 𝕜 _ _ _ _ μ s hs
  exact SimpleFunc.integrable_iff.mp ((scalarIntegrable_iff μ s).mp hs).2

theorem simple_integral_sum : Specs.D11.Ch06.ScalarIntegral.simple_integral_sum := by
  intro X 𝕜 _ _ _ _ μ s hs
  exact s.integral_eq_sum ((scalarIntegrable_iff μ s).mp hs).2

/-- EReal's absolute value is ENNReal-valued, including both infinities. -/
theorem measurable_extended_abs {X : Type u} [MeasurableSpace X]
    {f : X → EReal} (hf : Measurable f) : Measurable (fun x => (f x).abs) := by
  have habs (a : EReal) : a.abs = max a.toENNReal (-a).toENNReal := by
    induction a with
    | bot => simp
    | coe a => simp [EReal.abs_def, ← EReal.coe_neg, ← ENNReal.ofReal_max, abs_eq_max_neg]
    | top => simp
  simp_rw [habs]
  exact hf.ereal_toENNReal.max hf.neg.ereal_toENNReal

theorem extended_exceptional_null :
    Specs.D11.Ch06.ScalarIntegral.extended_exceptional_null := by
  intro X _ μ f hf
  change extendedIntegrable μ f at hf
  have hm := measurable_extended_abs hf.1
  refine ⟨measurableSet_eq_fun hm measurable_const, ?_⟩
  have hfin : (∫⁻ x, (f x).abs ∂μ) < ∞ := by
    simpa only [integral_eq_lintegral] using hf.2
  have hae := (ae_lt_top hm hfin.ne).mono (fun _ h => h.ne)
  simpa only [ae_iff, not_not] using hae

theorem finiteVersion_values : Specs.D11.Ch06.ScalarIntegral.finiteVersion_values := by
  intro X f x
  change ((f x).abs = ∞ → (f x).toReal = 0) ∧
    ((f x).abs ≠ ∞ → ((f x).toReal : EReal) = f x)
  induction f x with
  | bot => simp
  | coe a => simp [EReal.abs_def]
  | top => simp

theorem finiteVersion_integrable :
    Specs.D11.Ch06.ScalarIntegral.finiteVersion_integrable := by
  intro X _ μ f hf
  change extendedIntegrable μ f at hf
  change scalarIntegrable μ (finiteVersion f)
  refine ⟨hf.1.ereal_toReal, ?_⟩
  have hle : ∀ x, ENNReal.ofReal ‖finiteVersion f x‖ ≤ (f x).abs := by
    intro x
    change ENNReal.ofReal ‖(f x).toReal‖ ≤ (f x).abs
    induction f x with
    | bot => simp
    | coe a => simp [EReal.abs_def, Real.norm_eq_abs]
    | top => simp
  rw [integral_eq_lintegral]
  exact lt_of_le_of_lt (lintegral_mono hle) (by
    simpa only [integral_eq_lintegral] using hf.2)

theorem finiteVersion_ae : Specs.D11.Ch06.ScalarIntegral.finiteVersion_ae := by
  intro X _ μ f hf
  change aeEq μ (fun x => (finiteVersion f x : EReal)) f
  obtain ⟨hN, hnull⟩ := extended_exceptional_null μ f hf
  refine ⟨{x | (f x).abs = ∞}, ⟨hN, hnull⟩, ?_⟩
  intro x hx
  exact (finiteVersion_values f x).2 hx

theorem finiteVersion_unique_ae : Specs.D11.Ch06.ScalarIntegral.finiteVersion_unique_ae := by
  intro X _ μ f hf g hgf
  have hfg := (aeEq_iff_native μ _ _).mp (finiteVersion_ae μ f hf)
  have hgf' := (aeEq_iff_native μ _ _).mp hgf
  apply (aeEq_iff_native μ _ _).mpr
  filter_upwards [hfg, hgf'] with x hx hy
  exact EReal.coe_injective (hy.trans hx.symm)

theorem finiteVersion_absolute_integral :
    Specs.D11.Ch06.ScalarIntegral.finiteVersion_absolute_integral := by
  intro X _ μ f hf
  change nonnegativeIntegral μ (fun x => ENNReal.ofReal |finiteVersion f x|) =
    nonnegativeIntegral μ (fun x => (f x).abs)
  simp only [integral_eq_lintegral]
  apply lintegral_congr_ae
  have h := (aeEq_iff_native μ _ _).mp (finiteVersion_ae μ f hf)
  filter_upwards [h] with x hx
  rw [← hx]
  rfl

theorem finiteVersion_unique : Specs.D11.Ch06.ScalarIntegral.finiteVersion_unique := by
  intro X _ μ f hf g hgm hgf
  have hgeq := (aeEq_iff_native μ _ _).mp (finiteVersion_unique_ae μ f hf g hgf)
  have hfin := (scalarIntegrable_iff μ (finiteVersion f)).mp
    (finiteVersion_integrable μ f hf)
  have hgi : scalarIntegrable μ g :=
    (scalarIntegrable_iff μ g).mpr ⟨hgm, hfin.2.congr hgeq.symm⟩
  refine ⟨(aeEq_iff_native μ _ _).mpr hgeq, hgi, ?_⟩
  exact integral_congr_ae hgeq

theorem extended_integral_formula :
    Specs.D11.Ch06.ScalarIntegral.extended_integral_formula := by
  intro X _ μ f hf
  exact ⟨finiteVersion_integrable μ f hf, rfl⟩

end D11.Ch06.ScalarIntegral
