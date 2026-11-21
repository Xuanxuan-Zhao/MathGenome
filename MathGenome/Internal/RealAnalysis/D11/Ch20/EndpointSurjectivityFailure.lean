import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.EndpointSurjectivityFailure
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Real.Cardinality

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D11.Ch20.EndpointSurjectivityFailure
open Specs.D11.Ch20.EndpointSurjectivityFailure
attribute [local instance] Classical.propDecidable

instance : MeasurableSingletonClass Point where
  measurableSet_singleton x := Or.inl (countable_singleton x)

theorem measurable_sets : Specs.D11.Ch20.EndpointSurjectivityFailure.measurable_sets :=
  fun _ => Iff.rfl

theorem restricted_counting : Specs.D11.Ch20.EndpointSurjectivityFailure.restricted_counting := by
  constructor
  · intro s hs
    exact Measure.count_apply_finite s hs
  · intro s hs
    exact Measure.count_apply_infinite hs

theorem only_empty_null : Specs.D11.Ch20.EndpointSurjectivityFailure.only_empty_null := by
  intro s
  exact Measure.count_eq_zero_iff

theorem positive_nonmeasurable :
    Specs.D11.Ch20.EndpointSurjectivityFailure.positive_nonmeasurable := by
  intro h
  rcases h with h | h
  · have hc : (Ioo (0 : ℝ) 1).Countable := h.mono (fun x hx => hx.1)
    have hc' := Cardinal.le_aleph0_iff_set_countable.mpr hc
    rw [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1)] at hc'
    exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hc'
  · have hc : (Ioo (-1 : ℝ) 0).Countable := h.mono (fun x hx => not_lt.mpr hx.2.le)
    have hc' := Cardinal.le_aleph0_iff_set_countable.mpr hc
    rw [Cardinal.mk_Ioo_real (by norm_num : (-1 : ℝ) < 0)] at hc'
    exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hc'

theorem integrable_norm_summable {𝕜 : Type} [RCLike 𝕜]
    {f : Point → 𝕜} (hf : Integrable f μ) : Summable (fun x => ‖f x‖) := by
  have h := hf.summable_integral (μ := fun x : Point => Measure.dirac x)
  simpa using h

theorem integral_eq_tsum {𝕜 : Type} [RCLike 𝕜]
    {f : Point → 𝕜} (hf : Integrable f μ) : (∫ x, f x ∂μ) = ∑' x, f x := by
  simpa only [μ, Measure.count, integral_dirac] using
    (integral_sum_measure (μ := fun x : Point => Measure.dirac x) hf)

theorem integrable_series : Specs.D11.Ch20.EndpointSurjectivityFailure.integrable_series := by
  intro 𝕜 _ f hf
  have hs := integrable_norm_summable hf
  refine ⟨?_, hs, integral_eq_tsum hf⟩
  simpa only [Function.support, ne_eq, norm_eq_zero] using hs.countable_support

theorem not_sigmaFinite : Specs.D11.Ch20.EndpointSurjectivityFailure.not_sigmaFinite := by
  intro h
  let : SigmaFinite μ := h
  have hc : (univ : Set Point).Countable := by
    rw [← iUnion_spanningSets μ]
    exact countable_iUnion fun n =>
      ((Measure.count_apply_lt_top.mp (measure_spanningSets_lt_top μ n))).countable
  have hi : (Ioo (0 : ℝ) 1).Countable := hc.mono (subset_univ _)
  have hi' := Cardinal.le_aleph0_iff_set_countable.mpr hi
  rw [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1)] at hi'
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hi'

theorem semifinite : Specs.D11.Ch20.EndpointSurjectivityFailure.semifinite := by
  intro E hE
  apply le_antisymm
  · by_cases hf : E.Finite
    · exact le_iSup_of_le E (le_iSup_of_le hE (le_iSup_of_le Subset.rfl
        (le_iSup_of_le (Measure.count_apply_lt_top.mpr hf) le_rfl)))
    · have hi : E.Infinite := hf
      rw [show μ E = ∞ from Measure.count_apply_infinite hi]
      have ht : (⨆ (A : Set Point) (_ : MeasurableSet A) (_ : A ⊆ E)
          (_ : μ A < ∞), μ A) = ∞ := by
        apply top_unique
        apply le_of_tendsto' ENNReal.tendsto_nat_nhds_top
        intro n
        obtain ⟨t, ht, hc⟩ := hi.exists_subset_card_eq n
        have hcard : μ (t : Set Point) = n := by
          simp only [μ, Measure.count_apply_finset, hc]
        rw [← hcard]
        exact le_iSup_of_le (t : Set Point) (le_iSup_of_le t.measurableSet
          (le_iSup_of_le ht (le_iSup_of_le (by simp [μ]) le_rfl)))
      exact ht.ge
  · exact iSup_le fun A => iSup_le fun _ => iSup_le fun hAE =>
      iSup_le fun _ => measure_mono hAE

section Functional
variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
theorem positive_norm_summable (f : Lp 𝕜 1 μ) :
    Summable (fun x : positive => ‖f x‖) :=
  (integrable_norm_summable (L1.integrable_coeFn f)).subtype _

def positiveSumLinear : Lp 𝕜 1 μ →ₗ[𝕜] 𝕜 where
  toFun f := ∑' x : positive, f x
  map_add' f g := by
    have h := Measure.ae_count_iff.mp (Lp.coeFn_add f g)
    simp only [Pi.add_apply] at h
    simp_rw [h]
    exact Summable.tsum_add (positive_norm_summable f).of_norm
      (positive_norm_summable g).of_norm
  map_smul' c f := by
    have h := Measure.ae_count_iff.mp (Lp.coeFn_smul c f)
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp_rw [h]
    exact tsum_mul_left

theorem positiveSum_bound (f : Lp 𝕜 1 μ) : ‖positiveSumLinear f‖ ≤ ‖f‖ := by
  change ‖∑' x : positive, f x‖ ≤ ‖f‖
  calc
    _ ≤ ∑' x : positive, ‖f x‖ := norm_tsum_le_tsum_norm (positive_norm_summable f)
    _ ≤ ∑' x : Point, ‖f x‖ := Summable.tsum_subtype_le _ _ (fun _ => norm_nonneg _)
      (integrable_norm_summable (L1.integrable_coeFn f))
    _ = ∫ x, ‖f x‖ ∂μ := (integral_eq_tsum (L1.integrable_coeFn f).norm).symm
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

def positiveSum : Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  positiveSumLinear.mkContinuous 1 (by simpa using positiveSum_bound (𝕜 := 𝕜))

def pointIndicator (x : Point) : Point → 𝕜 :=
  ({x} : Set Point).indicator (fun _ => 1)

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
theorem pointIndicator_integrable (x : Point) : Integrable (pointIndicator (𝕜 := 𝕜) x) μ := by
  exact (integrableOn_singleton (f := fun _ : Point => (1 : 𝕜))
    (by simp) (by simp [μ])).integrable_indicator (measurableSet_singleton x)

def pointClass (x : Point) : Lp 𝕜 1 μ :=
  (pointIndicator_integrable (𝕜 := 𝕜) x).toL1 (pointIndicator x)

theorem pointClass_apply (x y : Point) :
    pointClass (𝕜 := 𝕜) x y = pointIndicator x y := by
  exact Measure.ae_count_iff.mp (pointIndicator_integrable (𝕜 := 𝕜) x).coeFn_toL1 y

theorem positiveSum_pointClass (x : Point) :
    positiveSum (pointClass (𝕜 := 𝕜) x) = if x ∈ positive then 1 else 0 := by
  classical
  change (∑' y : positive, pointClass x y) = _
  simp_rw [pointClass_apply]
  split_ifs with hx
  · rw [tsum_eq_single (⟨x, hx⟩ : positive)]
    · simp [pointIndicator]
    · intro y hy
      have hne : (y : Point) ≠ x := by
        intro heq
        exact hy (Subtype.ext heq)
      simp [pointIndicator, hne]
  · have hz : ∀ y : positive, pointIndicator (𝕜 := 𝕜) x y = 0 := by
      intro y
      have hne : (y : Point) ≠ x := by
        intro heq
        exact hx (heq ▸ y.property)
      simp [pointIndicator, hne]
    simp only [hz, tsum_zero]

/-- Singleton tests evaluate the bilinear pairing pointwise. The product is
integrable even without any bound or measurability assumption on `g`. -/
theorem pointClass_pairing (x : Point) (g : Point → 𝕜) :
    (∫ y, pointClass (𝕜 := 𝕜) x y * g y ∂μ) = g x := by
  classical
  simp_rw [pointClass_apply]
  have heq : (fun y => pointIndicator (𝕜 := 𝕜) x y * g y) =
      ({x} : Set Point).indicator g := by
    funext y
    by_cases hy : y = x <;> simp [pointIndicator, hy]
  rw [heq, integral_indicator (measurableSet_singleton x), integral_singleton]
  simp [μ]

theorem pointClass_product_integrable (x : Point) (g : Point → 𝕜) :
    Integrable (fun y => pointClass (𝕜 := 𝕜) x y * g y) μ := by
  classical
  have heq : (fun y => pointClass (𝕜 := 𝕜) x y * g y) =
      ({x} : Set Point).indicator g := by
    funext y
    by_cases hy : y = x <;> simp [pointClass_apply, pointIndicator, hy]
  rw [heq]
  exact (integrableOn_singleton (f := g) (by simp) (by simp [μ])).integrable_indicator
    (measurableSet_singleton x)

theorem no_measurable_density : ¬ ∃ g : Point → 𝕜, Measurable g ∧
    ∀ f : Lp 𝕜 1 μ, positiveSum f = ∫ x, f x * g x ∂μ := by
  rintro ⟨g, hg, hrep⟩
  have hpoint : ∀ x, g x = if x ∈ positive then 1 else 0 := by
    intro x
    have h := hrep (pointClass x)
    rw [positiveSum_pointClass, pointClass_pairing] at h
    exact h.symm
  apply positive_nonmeasurable
  have hm : MeasurableSet {x | g x = 1} := measurableSet_eq_fun hg measurable_const
  have heq : {x | g x = 1} = positive := by
    ext x
    simp only [mem_ofPred_eq, hpoint]
    by_cases hx : x ∈ positive <;> simp [hx]
  exact heq ▸ hm

end Functional

theorem endpoint_surjectivity_failure :
    Specs.D11.Ch20.EndpointSurjectivityFailure.endpoint_surjectivity_failure := by
  intro 𝕜 _ _ _
  refine ⟨positiveSum, fun _ => rfl, positive_norm_summable, positiveSum_bound, ?_⟩
  rintro ⟨g, hg, _hbounded, hrep⟩
  exact no_measurable_density ⟨g, hg, fun f => (hrep f).2⟩

end D11.Ch20.EndpointSurjectivityFailure
