import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorMeasureVariation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
Variation and the measure associated to a Bochner L¹ density.
Source: paper.tex:20814–20827, 20910–20923 and 20930–20935.

The native variation is identified with the exact finite-partition supremum.
The density construction has variation equal to the integral of the norm.
For compactness, finite-valued approximants have bounded integral ranges in
finite-dimensional spans, and the L¹ approximation error is uniform in the
integration set. Completeness makes the resulting totally bounded range
relatively compact. No reflexivity is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.PartIV
open VectorMeasureVariationSpec
open ExpandedFA.FunctionSpaces

def vectorMeasureVariation : VariationType.{u,v} := VariationValue

theorem variation_partition : VariationPartition.{u,v} := by
  intro X E _ _ m A hA
  simp only [VariationValue, VectorMeasure.variation, preVariation_apply,
    VectorMeasure.ennrealToMeasure_apply hA, ennrealPreVariation_apply,
    preVariationFun_apply _ hA]

theorem variation_finite : VariationFinite.{u,v} := by
  intro X E _ _ m hm
  exact ⟨hm⟩

theorem variation_countable : VariationCountable.{u,v} := by
  intro X E _ _ m A hA hdisj
  exact measure_iUnion hdisj hA

theorem variation_absolutelyContinuous : VariationAbsolutelyContinuous.{u,v} := by
  intro X E _ _ m μ hm
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hμA
  apply (VectorMeasure.variation_apply_eq_zero hA).mpr
  intro B hBA hB
  exact hm B hB (measure_mono_null hBA hμA)

def densityMeasure : DensityMeasureType.{u,v} := DensityMeasureValue

theorem densityMeasure_apply : DensityMeasureApply.{u,v} := by
  intro X E _ _ _ _ μ f hf A hA
  exact withDensityᵥ_apply ((bochnerIntegrable_identification μ f).mp hf) hA

theorem densityMeasure_countable : DensityMeasureCountable.{u,v} := by
  intro X E _ _ _ _ μ f A _ hA hd
  exact (DensityMeasureValue μ f).m_iUnion hA hd

theorem densityMeasure_absolutelyContinuous : DensityMeasureAbsolutelyContinuous.{u,v} := by
  intro X E _ _ _ _ μ f hf A hA hμA
  rw [densityMeasure_apply μ f hf A hA]
  change (∫ x in A, f x ∂μ) = 0
  rw [Measure.restrict_eq_zero.mpr hμA, integral_zero_measure]

theorem densityMeasure_variation : DensityVariation.{u,v} := by
  intro X E _ _ _ _ μ f hf
  exact Measure.variation_withDensityᵥ ((bochnerIntegrable_identification μ f).mp hf)

theorem densityMeasure_variation_apply : DensityVariationApply.{u,v} := by
  intro X E _ _ _ _ μ f hf A hA
  rw [densityMeasure_variation μ f hf]
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  refine ⟨withDensity_apply _ hA, ?_⟩
  rw [measureReal_def, withDensity_apply _ hA]
  exact (integral_norm_eq_lintegral_enorm hfi.aestronglyMeasurable.restrict).symm

theorem densityMeasure_variation_finite : DensityVariationFinite.{u,v} := by
  intro X E _ _ _ _ μ f hf
  rw [densityMeasure_variation μ f hf]
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  exact ⟨by simpa using (hasFiniteIntegral_iff_enorm.mp hfi.2)⟩

theorem densityMeasure_unique : DensityUnique.{u,v} := by
  intro X E _ _ _ _ μ f g hf hg hfg
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  have hgi := (bochnerIntegrable_identification μ g).mp hg
  apply hfi.ae_eq_of_withDensityᵥ_eq hgi
  ext A hA
  rw [withDensityᵥ_apply hfi hA, withDensityᵥ_apply hgi hA]
  exact hfg A hA

/-- The integrals of a finite-valued integrable function form a totally
bounded set, even when the ambient Banach space is infinite dimensional. -/
theorem simple_integrals_totallyBounded {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (s : SimpleFunc X E) (hs : Integrable s μ) :
    TotallyBounded (range (fun A : Set X => ∫ x in A, s x ∂μ)) := by
  classical
  let V := Submodule.span ℝ (range s)
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ s.finite_range
  have hmem (A : Set X) : (∫ x in A, s x ∂μ) ∈ V := by
    rw [s.integral_eq_sum hs.restrict]
    apply Submodule.sum_mem
    intro y hy
    exact Submodule.smul_mem V _ (Submodule.subset_span (by simpa using hy))
  let F : Set X → V := fun A => ⟨∫ x in A, s x ∂μ, hmem A⟩
  have hb : Bornology.IsBounded (range F) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨∫ x, ‖s x‖ ∂μ, ?_⟩
    rintro _ ⟨A, rfl⟩
    exact (norm_integral_le_integral_norm _).trans
      (setIntegral_le_integral hs.norm (Eventually.of_forall (fun _ => norm_nonneg _)))
  have hc := hb.isCompact_closure.image (continuous_subtype_val : Continuous (Subtype.val : V → E))
  apply hc.totallyBounded.subset
  rintro _ ⟨A, rfl⟩
  exact ⟨F A, subset_closure (mem_range_self A), rfl⟩

/-- Uniform L¹ approximation transfers the finite-dimensional total
boundedness of simple integral ranges to an arbitrary Bochner density. -/
theorem integrals_totallyBounded {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (f : X → E) (hf : Integrable f μ) :
    TotallyBounded (range (fun A : Set X => ∫ x in A, f x ∂μ)) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨s, herr, hs⟩ := (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (show ENNReal.ofReal (ε / 2) ≠ 0 by positivity)
  have hsi := memLp_one_iff_integrable.mp hs
  have hnear (A : Set X) : dist (∫ x in A, f x ∂μ) (∫ x in A, s x ∂μ) < ε / 2 := by
    apply edist_lt_ofReal.mp
    apply lt_of_le_of_lt (edist_integral_le_lintegral_edist hf.restrict hsi.restrict)
    calc
      ∫⁻ x in A, edist (f x) (s x) ∂μ = ∫⁻ x in A, ‖(f - ⇑s) x‖ₑ ∂μ := by
        simp only [edist_eq_enorm_sub, Pi.sub_apply]
      _ ≤ ∫⁻ x, ‖(f - ⇑s) x‖ₑ ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = eLpNorm (f - ⇑s) 1 μ :=
        (eLpNorm_one_eq_lintegral_enorm (hf.sub hsi).aestronglyMeasurable).symm
      _ < ENNReal.ofReal (ε / 2) := herr
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (simple_integrals_totallyBounded μ s hsi) (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨A, rfl⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (hcover (mem_range_self A))
  apply Set.mem_iUnion₂.mpr
  refine ⟨y, hyt, ?_⟩
  apply Metric.mem_ball.mpr
  calc
    dist (∫ x in A, f x ∂μ) y ≤
        dist (∫ x in A, f x ∂μ) (∫ x in A, s x ∂μ) + dist (∫ x in A, s x ∂μ) y :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hnear A) (Metric.mem_ball.mp hy)
    _ = ε := add_halves ε

theorem densityMeasure_compactRange : DensityCompactRange.{u,v} := by
  intro X E _ _ _ _ μ f hf
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  have hb := integrals_totallyBounded μ f hfi
  have hd : TotallyBounded (range (DensityMeasureValue μ f)) := by
    apply hb.subset
    rintro _ ⟨A, rfl⟩
    by_cases hA : MeasurableSet A
    · exact ⟨A, (withDensityᵥ_apply hfi hA).symm⟩
    · refine ⟨∅, ?_⟩
      simp [DensityMeasureValue, VectorMeasure.not_measurable _ hA]
  exact hd.closure.isCompact_of_isClosed isClosed_closure

end ExpandedFA.PartIV
