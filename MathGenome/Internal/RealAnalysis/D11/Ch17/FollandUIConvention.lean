import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.FollandUIConvention
import MathGenome.Internal.RealAnalysis.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch06.LinearityOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Folland's signed-integral convention, paper.tex:5228–5236.
The sign sets are chosen separately for each function. The proof retains the
literal strict supremum condition, using epsilon/8 in the reverse direction.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace D11.Ch17.FollandUIConvention
open D11.Ch17.UniformControls D11.Ch06.ScalarIntegral

def signedIntegralSup : Specs.D11.Ch17.FollandUIConvention.signedIntegralSup_type.{u,v} :=
  fun μ F A => ⨆ i, ENNReal.ofReal ‖∫ x in A, F i x ∂μ‖

def signedSmall : Specs.D11.Ch17.FollandUIConvention.signedSmall_type.{u,v} :=
  fun μ F => integrableFamily μ F ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set _, MeasurableSet A → μ A < ENNReal.ofReal δ →
      signedIntegralSup μ F A < ENNReal.ofReal ε

/-- Identification with a finite real integral, only after proving L1 membership. -/
private theorem absoluteIntegral_eq_ofReal_integral_norm
    {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜)
    (hf : Integrable f μ) (A : Set X) :
    absoluteIntegral μ f A = ENNReal.ofReal (∫ x in A, ‖f x‖ ∂μ) := by
  rw [absoluteIntegral_formula]
  exact (ofReal_integral_eq_lintegral_ofReal hf.norm.integrableOn
    (Filter.Eventually.of_forall fun x => norm_nonneg (f x))).symm

theorem signedIntegralSup_le_absolute :
    Specs.D11.Ch17.FollandUIConvention.signedIntegralSup_le_absolute := by
  intro X ι 𝕜 _ _ _ _ μ F hF A
  change (⨆ i, ENNReal.ofReal ‖∫ x in A, F i x ∂μ‖) ≤
    ⨆ i, absoluteIntegral μ (F i) A
  apply iSup_le
  intro i
  have hi := ((scalarIntegrable_iff μ (F i)).mp (hF i)).2
  apply le_trans _ (le_iSup (fun i => absoluteIntegral μ (F i) A) i)
  rw [absoluteIntegral_eq_ofReal_integral_norm μ (F i) hi A]
  exact ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)

/-- The negative piece is strict, so these two measurable pieces partition A. -/
private theorem real_integral_norm_le
    {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hm : Measurable f) (hf : Integrable f μ) (A : Set X) (hA : MeasurableSet A)
    (c : ℝ)
    (hB : ∀ B : Set X, MeasurableSet B → B ⊆ A → ‖∫ x in B, f x ∂μ‖ ≤ c) :
    (∫ x in A, ‖f x‖ ∂μ) ≤ 2 * c := by
  have hp : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hm
  have hn : MeasurableSet {x | f x < 0} := measurableSet_lt hm measurable_const
  have hsplit := integral_norm_eq_pos_sub_neg (μ := μ.restrict A) hf.integrableOn
  rw [← setIntegral_neg_eq_setIntegral_nonpos (μ := μ.restrict A)
    hf.integrableOn.aestronglyMeasurable]
    at hsplit
  have heq : (∫ x in A, ‖f x‖ ∂μ) =
      (∫ x in A ∩ {x | 0 ≤ f x}, f x ∂μ) -
      (∫ x in A ∩ {x | f x < 0}, f x ∂μ) := by
    simpa only [Measure.restrict_restrict' hA, inter_comm] using hsplit
  have hpos := hB (A ∩ {x | 0 ≤ f x}) (hA.inter hp) inter_subset_left
  have hneg := hB (A ∩ {x | f x < 0}) (hA.inter hn) inter_subset_left
  rw [Real.norm_eq_abs] at hpos hneg
  rw [heq]
  linarith [le_abs_self (∫ x in A ∩ {x | 0 ≤ f x}, f x ∂μ),
    neg_le_abs (∫ x in A ∩ {x | f x < 0}, f x ∂μ)]

theorem real_two_piece_estimate :
    Specs.D11.Ch17.FollandUIConvention.real_two_piece_estimate := by
  intro X _ μ f hf A hA c hB
  obtain ⟨hm, hi⟩ := (scalarIntegrable_iff μ f).mp hf
  change absoluteIntegral μ f A ≤ ENNReal.ofReal (2 * c)
  rw [absoluteIntegral_eq_ofReal_integral_norm μ f hi A]
  exact ENNReal.ofReal_le_ofReal (real_integral_norm_le μ f hm hi A hA c hB)

theorem four_piece_estimate :
    Specs.D11.Ch17.FollandUIConvention.four_piece_estimate := by
  intro X 𝕜 _ _ _ _ μ f hf A hA c hB
  obtain ⟨hm, hi⟩ := (scalarIntegrable_iff μ f).mp hf
  have hrm : Measurable (fun x => RCLike.re (f x)) :=
    RCLike.continuous_re.measurable.comp hm
  have him : Measurable (fun x => RCLike.im (f x)) :=
    RCLike.continuous_im.measurable.comp hm
  have hr := real_integral_norm_le μ (fun x => RCLike.re (f x)) hrm hi.re A hA c
    (fun B hBm hBA => by
      rw [integral_re hi.integrableOn, Real.norm_eq_abs]
      exact (RCLike.abs_re_le_norm _).trans (hB B hBm hBA))
  have him' := real_integral_norm_le μ (fun x => RCLike.im (f x)) him hi.im A hA c
    (fun B hBm hBA => by
      rw [integral_im hi.integrableOn, Real.norm_eq_abs]
      exact (RCLike.abs_im_le_norm _).trans (hB B hBm hBA))
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_I]
    split_ifs <;> norm_num
  have hnorm (z : 𝕜) : ‖z‖ ≤ ‖RCLike.re z‖ + ‖RCLike.im z‖ := by
    calc
      ‖z‖ = ‖(RCLike.re z : 𝕜) + (RCLike.im z : 𝕜) * RCLike.I‖ := by
        rw [RCLike.re_add_im]
      _ ≤ ‖(RCLike.re z : 𝕜)‖ + ‖(RCLike.im z : 𝕜) * RCLike.I‖ := norm_add_le _ _
      _ ≤ ‖RCLike.re z‖ + ‖RCLike.im z‖ := by
        simp only [norm_mul, RCLike.norm_ofReal, Real.norm_eq_abs]
        exact add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hI)
  have hsum : (∫ x in A, ‖f x‖ ∂μ) ≤ 4 * c := by
    calc
      (∫ x in A, ‖f x‖ ∂μ) ≤
          ∫ x in A, ‖RCLike.re (f x)‖ + ‖RCLike.im (f x)‖ ∂μ :=
        integral_mono hi.norm.integrableOn (hi.re.norm.add hi.im.norm).integrableOn
          (fun x => hnorm (f x))
      _ = (∫ x in A, ‖RCLike.re (f x)‖ ∂μ) +
          (∫ x in A, ‖RCLike.im (f x)‖ ∂μ) :=
        integral_add hi.re.norm.integrableOn hi.im.norm.integrableOn
      _ ≤ 4 * c := by linarith
  change absoluteIntegral μ f A ≤ ENNReal.ofReal (4 * c)
  rw [absoluteIntegral_eq_ofReal_integral_norm μ f hi A]
  exact ENNReal.ofReal_le_ofReal hsum

theorem signedSmall_iff_uiSmall :
    Specs.D11.Ch17.FollandUIConvention.signedSmall_iff_uiSmall := by
  intro X ι 𝕜 _ _ _ _ μ F
  change signedSmall μ F ↔ uiSmall μ F
  constructor
  · rintro ⟨hF, hs⟩
    refine ⟨hF, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hs (ε / 8) (by positivity)
    refine ⟨δ, hδ, fun A hA hμA => ?_⟩
    have hbound : integralSup μ F A ≤ ENNReal.ofReal (ε / 2) := by
      apply iSup_le
      intro i
      have hpiece := four_piece_estimate μ (F i) (hF i) A hA (ε / 8)
        (fun B hBm hBA => by
          have hsmall := hd B hBm ((measure_mono hBA).trans_lt hμA)
          have hle : ENNReal.ofReal ‖∫ x in B, F i x ∂μ‖ ≤
              signedIntegralSup μ F B :=
            le_iSup (fun j => ENNReal.ofReal ‖∫ x in B, F j x ∂μ‖) i
          exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
            (hle.trans_lt hsmall)))
      convert hpiece using 1 <;> congr 1 <;> ring
    exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
  · rintro ⟨hF, hs⟩
    refine ⟨hF, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hd⟩ := hs ε hε
    exact ⟨δ, hδ, fun A hA hμA =>
      (signedIntegralSup_le_absolute μ F hF A).trans_lt (hd A hA hμA)⟩

end D11.Ch17.FollandUIConvention
