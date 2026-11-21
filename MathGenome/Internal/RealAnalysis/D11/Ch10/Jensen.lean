import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.Jensen
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral

/-! Jensen's inequality (paper.tex:3558–3575). Continuity is a conclusion
of finite convexity on all ℝ. The extended case splits according to finiteness
of the nonnegative integral, and uses scalar Jensen only in the finite case.
Normalized Lebesgue measure and both average formulas are made explicit. -/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch10.Jensen
open D11.Ch06.ScalarIntegral
open D11.Ch05.NonnegativeIntegral

theorem convex_continuous : Specs.D11.Ch10.Jensen.convex_continuous := by
  intro Φ hΦ
  exact continuousOn_univ.mp (hΦ.continuousOn isOpen_univ)

theorem convex_measurable : Specs.D11.Ch10.Jensen.convex_measurable := by
  intro Φ hΦ
  exact (convex_continuous Φ hΦ).measurable

theorem composition_measurable : Specs.D11.Ch10.Jensen.composition_measurable := by
  intro X _ f Φ hΦ hf
  exact (convex_measurable Φ hΦ).comp hf

private theorem jensen_native {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (Φ : ℝ → ℝ)
    (hΦ : ConvexOn ℝ univ Φ) (hf : Integrable f μ) (hΦf : Integrable (Φ ∘ f) μ) :
    Φ (∫ x, f x ∂μ) ≤ ∫ x, Φ (f x) ∂μ := by
  exact hΦ.map_integral_le (convex_continuous Φ hΦ).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hf hΦf

theorem jensen_integrable : Specs.D11.Ch10.Jensen.jensen_integrable := by
  intro X _ μ f Φ hμ hΦ hf hΦf
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  exact jensen_native μ f Φ hΦ ((scalarIntegrable_iff μ f).mp hf).2
    ((scalarIntegrable_iff μ (Φ ∘ f)).mp hΦf).2

private theorem jensen_nonnegative_native {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (Φ : ℝ → ℝ)
    (hΦ : ConvexOn ℝ univ Φ) (hpos : ∀ t, 0 ≤ Φ t) (hf : Integrable f μ) :
    ENNReal.ofReal (Φ (∫ x, f x ∂μ)) ≤ ∫⁻ x, ENNReal.ofReal (Φ (f x)) ∂μ := by
  by_cases hfin : (∫⁻ x, ENNReal.ofReal (Φ (f x)) ∂μ) = ∞
  · rw [hfin]
    exact le_top
  · have hmeas : AEStronglyMeasurable (Φ ∘ f) μ :=
      (convex_continuous Φ hΦ).comp_aestronglyMeasurable hf.aestronglyMeasurable
    have hnorm : (fun x => ENNReal.ofReal ‖Φ (f x)‖) =
        (fun x => ENNReal.ofReal (Φ (f x))) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos _)]
    have hΦf : Integrable (Φ ∘ f) μ := by
      refine ⟨hmeas, ?_⟩
      apply (hasFiniteIntegral_iff_norm _).mpr
      simpa only [Function.comp_apply, hnorm] using lt_top_iff_ne_top.mpr hfin
    have hJ := ENNReal.ofReal_le_ofReal (jensen_native μ f Φ hΦ hf hΦf)
    exact hJ.trans_eq (ofReal_integral_eq_lintegral_ofReal
      (f := fun x => Φ (f x)) hΦf (Filter.Eventually.of_forall (fun x => hpos (f x))))

theorem jensen_nonnegative : Specs.D11.Ch10.Jensen.jensen_nonnegative := by
  intro X _ μ f Φ hμ hΦ hpos hf
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  change ENNReal.ofReal (Φ (∫ x, f x ∂μ)) ≤
    nonnegativeIntegral μ (fun x => ENNReal.ofReal (Φ (f x)))
  rw [integral_eq_lintegral]
  exact jensen_nonnegative_native μ f Φ hΦ hpos ((scalarIntegrable_iff μ f).mp hf).2

local notation "LReal" => NullMeasurableSpace ℝ (volume : Measure ℝ)
local notation "lebesgue" => Measure.completion (volume : Measure ℝ)

def intervalProbability (a b : ℝ) : Measure LReal :=
  (ENNReal.ofReal (b - a))⁻¹ • Measure.restrict lebesgue (Icc a b : Set ℝ)

theorem intervalProbability_mass : Specs.D11.Ch10.Jensen.intervalProbability_mass := by
  intro a b hab
  change intervalProbability a b univ = 1
  have hmass : (Measure.restrict lebesgue (Icc a b : Set ℝ)) univ =
      ENNReal.ofReal (b - a) :=
    (Measure.restrict_apply_univ (μ := lebesgue) (s := (Icc a b : Set ℝ))).trans
      (Real.volume_Icc (a := a) (b := b))
  change (ENNReal.ofReal (b - a))⁻¹ *
    (Measure.restrict lebesgue (Icc a b : Set ℝ)) univ = 1
  rw [hmass]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
    ENNReal.ofReal_ne_top

theorem interval_integral_normalization :
    Specs.D11.Ch10.Jensen.interval_integral_normalization := by
  intro a b hab f hf
  change Integrable f (intervalProbability a b) ∧ _
  constructor
  · exact hf.smul_measure (by finiteness)
  · rw [Specs.D11.Ch10.Jensen.intervalProbability_value, integral_smul_measure]
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]

theorem interval_nonnegative_normalization :
    Specs.D11.Ch10.Jensen.interval_nonnegative_normalization := by
  intro a b _hab g
  change nonnegativeIntegral (intervalProbability a b) g =
    (ENNReal.ofReal (b - a))⁻¹ * nonnegativeIntegral (Measure.restrict lebesgue (Icc a b : Set ℝ)) g
  simp only [integral_eq_lintegral, intervalProbability, lintegral_smul_measure, smul_eq_mul]

theorem interval_jensen_integrable : Specs.D11.Ch10.Jensen.interval_jensen_integrable := by
  intro a b hab f Φ hΦ hf hΦf
  let : IsProbabilityMeasure (intervalProbability a b) := ⟨intervalProbability_mass a b hab⟩
  have hfn := interval_integral_normalization a b hab f hf
  have hΦfn := interval_integral_normalization a b hab (Φ ∘ f) hΦf
  change Integrable f (intervalProbability a b) ∧
    (∫ x, f x ∂intervalProbability a b) = (b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), f x ∂lebesgue at hfn
  change Integrable (Φ ∘ f) (intervalProbability a b) ∧
    (∫ x, Φ (f x) ∂intervalProbability a b) =
      (b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), Φ (f x) ∂lebesgue at hΦfn
  have h := jensen_native (intervalProbability a b) f Φ hΦ hfn.1 hΦfn.1
  simpa only [hfn.2, hΦfn.2, Function.comp_apply] using h

theorem interval_jensen_nonnegative : Specs.D11.Ch10.Jensen.interval_jensen_nonnegative := by
  intro a b hab f Φ hΦ hpos hf
  let : IsProbabilityMeasure (intervalProbability a b) := ⟨intervalProbability_mass a b hab⟩
  have hfn := interval_integral_normalization a b hab f hf
  change Integrable f (intervalProbability a b) ∧
    (∫ x, f x ∂intervalProbability a b) = (b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), f x ∂lebesgue at hfn
  have h := jensen_nonnegative_native (intervalProbability a b) f Φ hΦ hpos hfn.1
  rw [hfn.2] at h
  change ENNReal.ofReal (Φ ((b - a)⁻¹ * ∫ x in (Icc a b : Set ℝ), f x ∂lebesgue)) ≤
    (ENNReal.ofReal (b - a))⁻¹ *
      nonnegativeIntegral (Measure.restrict lebesgue (Icc a b : Set ℝ)) (fun x => ENNReal.ofReal (Φ (f x)))
  simpa only [integral_eq_lintegral, intervalProbability, lintegral_smul_measure,
    smul_eq_mul] using h

end D11.Ch10.Jensen
