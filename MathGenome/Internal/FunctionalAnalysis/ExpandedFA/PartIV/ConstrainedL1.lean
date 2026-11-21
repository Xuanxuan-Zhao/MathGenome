import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConstrainedL1
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Tactic.Ring

/-!
The L¹ part of `fa2:p4:constrained-support`, paper.tex:21405–21413.
Extend zero on the arbitrary subspace by Hahn–Banach, dominated by the
sublinear interval support function. Its linear growth makes the extension
continuous on any measure space. Only under sigma-finiteness do we invoke
the accepted ordinary L¹ dual representation. Indicators of every measurable
finite-measure set then give the pointwise interval bounds.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section
namespace ExpandedFA.PartIV.ConstrainedL1
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

lemma integrable_product (a : Lp ℝ ∞ μ) (v : Lp ℝ 1 μ) :
    Integrable (fun x => a x * v x) μ :=
  (Lp.memLp a).integrable_mul (Lp.memLp v)

lemma integrable_upper (a b : Lp ℝ ∞ μ) (v : Lp ℝ 1 μ) :
    Integrable (fun x => max (a x * v x) (b x * v x)) μ :=
  (integrable_product a v).sup (integrable_product b v)

lemma lower_eq_neg_upper_neg (a b : Lp ℝ ∞ μ)
    (hab : ∀ᵐ x ∂μ, a x ≤ b x) (v : Lp ℝ 1 μ) :
    lowerIntegral μ a b v = -upperIntegral μ a b (-v) := by
  rw [lowerIntegral, upperIntegral, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hab, Lp.coeFn_neg v] with x hx hv
  simp only [hv, Pi.neg_apply]
  rcases le_total 0 (v x) with hp | hn
  · rw [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp), mul_zero, sub_zero,
      max_eq_left (mul_le_mul_of_nonpos_right hx (neg_nonpos.mpr hp))]
    ring
  · rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), mul_zero, zero_sub,
      max_eq_right (mul_le_mul_of_nonneg_right hx (neg_nonneg.mpr hn))]

lemma upper_subadd (a b : Lp ℝ ∞ μ) (v w : Lp ℝ 1 μ) :
    upperIntegral μ a b (v + w) ≤ upperIntegral μ a b v + upperIntegral μ a b w := by
  simp only [upperIntegral]
  rw [← integral_add (integrable_upper a b v) (integrable_upper a b w)]
  apply integral_mono_ae (integrable_upper a b (v + w))
    ((integrable_upper a b v).add (integrable_upper a b w))
  filter_upwards [Lp.coeFn_add v w] with x hx
  simp only [hx, Pi.add_apply, mul_add]
  exact max_le
    (add_le_add (le_max_left _ _) (le_max_left _ _))
    (add_le_add (le_max_right _ _) (le_max_right _ _))

lemma upper_hom (a b : Lp ℝ ∞ μ) (c : ℝ) (hc : 0 < c) (v : Lp ℝ 1 μ) :
    upperIntegral μ a b (c • v) = c * upperIntegral μ a b v := by
  rw [upperIntegral, upperIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c v] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm (a x) c, mul_left_comm (b x) c]
  exact (mul_max_of_nonneg _ _ hc.le).symm

lemma upper_bound (a b : Lp ℝ ∞ μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Lp ℝ 1 μ, upperIntegral μ a b v ≤ C * ‖v‖ := by
  have ha : eLpNormEssSup (fun x => a x) μ < ∞ := by
    simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable a)] using
      (Lp.memLp a).eLpNorm_lt_top
  have hb : eLpNormEssSup (fun x => b x) μ < ∞ := by
    simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable b)] using
      (Lp.memLp b).eLpNorm_lt_top
  obtain ⟨A, hA⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp ha
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hb
  refine ⟨(A : ℝ) + B, add_nonneg A.coe_nonneg B.coe_nonneg, ?_⟩
  intro v
  rw [L1.norm_eq_integral_norm, ← integral_const_mul]
  apply integral_mono_ae (integrable_upper a b v)
    ((memLp_one_iff_integrable.mp (Lp.memLp v)).norm.const_mul _)
  filter_upwards [hA, hB] with x ha hb
  have ha' : ‖a x‖ ≤ (A : ℝ) := ha
  have hb' : ‖b x‖ ≤ (B : ℝ) := hb
  apply max_le
  · calc
      a x * v x ≤ ‖a x * v x‖ := le_abs_self _
      _ = ‖a x‖ * ‖v x‖ := norm_mul _ _
      _ ≤ ((A : ℝ) + B) * ‖v x‖ := mul_le_mul_of_nonneg_right
        (ha'.trans (le_add_of_nonneg_right B.coe_nonneg)) (norm_nonneg _)
  · calc
      b x * v x ≤ ‖b x * v x‖ := le_abs_self _
      _ = ‖b x‖ * ‖v x‖ := norm_mul _ _
      _ ≤ ((A : ℝ) + B) * ‖v x‖ := mul_le_mul_of_nonneg_right
        (hb'.trans (le_add_of_nonneg_left A.coe_nonneg)) (norm_nonneg _)

/-- The dominated continuous-dual conclusion, without sigma-finiteness. -/
theorem dominated_dual : Spec.DominatedDual.{u} := by
  intro X _ μ M a b hab
  constructor
  · rintro ⟨L, hM, hL⟩ v
    exact (hL v).1.trans_eq (hM v)
  · intro htest
    obtain ⟨F, hFM, hF⟩ := exists_extension_of_le_sublinear
      (LinearPMap.mk M (0 : M →ₗ[ℝ] ℝ)) (upperIntegral μ a b)
      (upper_hom a b) (upper_subadd a b) (by
        intro v
        have ht := htest (-v)
        rw [lower_eq_neg_upper_neg a b hab] at ht
        simp only [Submodule.coe_neg, neg_neg] at ht
        simpa using neg_nonpos.mp ht)
    obtain ⟨C, hC, hbound⟩ := upper_bound a b
    have hnorm : ∀ v, ‖F v‖ ≤ C * ‖v‖ := by
      intro v
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have hn := (hF (-v)).trans (hbound (-v))
        simpa only [map_neg, norm_neg, neg_le] using hn
      · exact (hF v).trans (hbound v)
    refine ⟨F.mkContinuous C hnorm, ?_, ?_⟩
    · intro v
      exact hFM v
    · intro v
      refine ⟨?_, hF v⟩
      rw [lower_eq_neg_upper_neg a b hab]
      have hn := hF (-v)
      rw [map_neg] at hn
      exact neg_le.mp hn

lemma linfty_integrableOn (a : Lp ℝ ∞ μ) (s : Set X) (hs : μ s < ∞) :
    IntegrableOn (fun x => a x) s μ := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hs⟩
  exact MemLp.integrable le_top (MemLp.mono_measure Measure.restrict_le_self (Lp.memLp a))

/-- The library order test uses all finite-measure sets and a sigma-finite
exhaustion, rather than presuming that the entire measure is finite. -/
theorem finite_measure_tests : Spec.FiniteMeasureTests.{u} := by
  intro X _ μ _ a b h htest
  have hlo : ∀ᵐ x ∂μ, 0 ≤ h x - a x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro s hs hμs
      exact (linfty_integrableOn h s hμs).sub (linfty_integrableOn a s hμs)
    · intro s hs hμs
      rw [integral_sub (linfty_integrableOn h s hμs) (linfty_integrableOn a s hμs)]
      exact sub_nonneg.mpr (htest s hs hμs).1
  have hhi : ∀ᵐ x ∂μ, 0 ≤ b x - h x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro s hs hμs
      exact (linfty_integrableOn b s hμs).sub (linfty_integrableOn h s hμs)
    · intro s hs hμs
      rw [integral_sub (linfty_integrableOn b s hμs) (linfty_integrableOn h s hμs)]
      exact sub_nonneg.mpr (htest s hs hμs).2
  filter_upwards [hlo, hhi] with x hx hy
  exact ⟨sub_nonneg.mp hx, sub_nonneg.mp hy⟩

lemma lower_indicator (a b : Lp ℝ ∞ μ) (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s < ∞) :
    lowerIntegral μ a b (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) = ∫ x in s, a x ∂μ := by
  rw [lowerIntegral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))]
    with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

lemma upper_indicator (a b : Lp ℝ ∞ μ) (hab : ∀ᵐ x ∂μ, a x ≤ b x)
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s < ∞) :
    upperIntegral μ a b (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) = ∫ x in s, b x ∂μ := by
  rw [upperIntegral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [hab,
    indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))] with x habx hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs, max_eq_right habx]

lemma product_indicator (h : Lp ℝ ∞ μ)
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s < ∞) :
    (∫ x, (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) x * h x ∂μ) = ∫ x in s, h x ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))]
    with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

lemma density_le_upper (a b h : Lp ℝ ∞ μ)
    (hh : ∀ᵐ x ∂μ, a x ≤ h x ∧ h x ≤ b x) (v : Lp ℝ 1 μ) :
    (∫ x, h x * v x ∂μ) ≤ upperIntegral μ a b v := by
  apply integral_mono_ae (integrable_product h v) (integrable_upper a b v)
  filter_upwards [hh] with x hx
  rcases le_total 0 (v x) with hp | hn
  · exact (mul_le_mul_of_nonneg_right hx.2 hp).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hx.1 hn).trans (le_max_left _ _)

lemma lower_le_density (a b h : Lp ℝ ∞ μ)
    (hh : ∀ᵐ x ∂μ, a x ≤ h x ∧ h x ≤ b x) (v : Lp ℝ 1 μ) :
    lowerIntegral μ a b v ≤ ∫ x, h x * v x ∂μ := by
  rw [lower_eq_neg_upper_neg a b (hh.mono (fun x hx => hx.1.trans hx.2))]
  have hneg := density_le_upper a b h hh (-v)
  have heq : (∫ x, h x * (-v) x ∂μ) = -(∫ x, h x * v x ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg v] with x hx
    simp only [hx, Pi.neg_apply, mul_neg]
  rw [heq] at hneg
  exact neg_le.mp hneg

/-- The full constrained L¹ equivalence, with ordinary L∞ and a.e. bounds. -/
theorem constrained_existence : Spec.ConstrainedExistence.{u} := by
  intro X _ μ _ M a b hab
  constructor
  · rintro ⟨h, hh, hM⟩ v
    exact (lower_le_density a b h hh v).trans_eq (hM v)
  · intro htest
    obtain ⟨L, hLM, hL⟩ := (dominated_dual μ M a b hab).mpr htest
    obtain ⟨h, hrep, _⟩ := ExpandedFA.FunctionSpaces.lp_one_infinity_duality_sigmaFinite μ L
    refine ⟨h, ?_, ?_⟩
    · apply finite_measure_tests μ a b h
      intro s hs hμs
      let v : Lp ℝ 1 μ := indicatorConstLp 1 hs hμs.ne (1 : ℝ)
      have ht := hL v
      rw [(hrep.1 v).2, lower_indicator a b s hs hμs,
        upper_indicator a b hab s hs hμs, product_indicator h s hs hμs] at ht
      exact ht
    · intro v
      rw [show (fun x => h x * (v : Lp ℝ 1 μ) x) =
        (fun x => (v : Lp ℝ 1 μ) x * h x) from funext (fun x => mul_comm _ _)]
      exact ((hrep.1 v).2).symm.trans (hLM v)

end ExpandedFA.PartIV.ConstrainedL1

