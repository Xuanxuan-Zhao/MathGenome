import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Tightness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuousMapping
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ProkhorovForward

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped NNReal ENNReal

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section

/-- The manuscript's strict real-epsilon tightness implies Mathlib tightness. -/
theorem UniformlyTight.isTightMeasureSet {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] {A : Set (ProbabilityMeasure S)}
    (hA : UniformlyTight A) :
    IsTightMeasureSet { (μ : Measure S) | μ ∈ A } := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨K, hK, hb⟩ := (uniformlyTight_iff A).mp hA δ (by exact_mod_cast hδ)
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  exact (hb μ hμ).le.trans (by simpa using hδε.le)

/-- Forward Prokhorov: compact weak closure on an arbitrary metric space. -/
theorem prokhorov_compact_closure {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S))
    (hA : UniformlyTight A) : IsCompact (closure A) :=
  isCompact_closure_of_isTightMeasureSet hA.isTightMeasureSet

/-- A uniformly tight family is carried by a common closed separable subspace.
This is the extra step needed for sequential compactness in a possibly
nonseparable ambient space. -/
theorem UniformlyTight.exists_closed_separable_support {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] {A : Set (ProbabilityMeasure S)}
    (hA : UniformlyTight A) :
    ∃ F : Set S, IsClosed F ∧ IsSeparable F ∧ ∀ μ ∈ A, (μ : Measure S) Fᶜ = 0 := by
  obtain ⟨u, -, hu_pos, hu⟩ : ∃ u : ℕ → ℝ≥0, StrictAnti u ∧
      (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto 0
  have bounds (n : ℕ) : ∃ K : Set S, IsCompact K ∧
      ∀ μ ∈ A, (μ : Measure S) Kᶜ ≤ (u n : ℝ≥0∞) := by
    obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      hA.isTightMeasureSet (u n) (by exact_mod_cast hu_pos n)
    exact ⟨K, hK, fun μ hμ => hb _ ⟨μ, hμ, rfl⟩⟩
  choose K hK hb using bounds
  let F := closure (⋃ n, K n)
  refine ⟨F, isClosed_closure, (IsSeparable.iUnion (fun n => (hK n).isSeparable)).closure,
    fun μ hμ => ?_⟩
  apply le_antisymm _ bot_le
  have hlim : Tendsto (fun n => (u n : ℝ≥0∞)) atTop (𝓝 0) := by
    exact_mod_cast (ENNReal.continuous_coe.tendsto 0).comp hu
  apply ge_of_tendsto' hlim
  intro n
  exact (measure_mono (compl_subset_compl.mpr
    ((subset_iUnion K n).trans subset_closure))).trans (hb n μ hμ)

/-- Forward Prokhorov: every sequence in a uniformly tight family has a
weakly convergent subsequence, even when the ambient metric space is
nonseparable. Compactness is applied only after reduction to a common
separable support. -/
theorem prokhorov_subsequence {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S))
    (hA : UniformlyTight A) (μ : ℕ → ProbabilityMeasure S) (hμ : ∀ n, μ n ∈ A) :
    ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
      WeaklyConverges atTop (μ ∘ φ) ν := by
  obtain ⟨F, hF, hsep, hnull⟩ := hA.exists_closed_separable_support
  have : SeparableSpace F := hsep.separableSpace
  have he : MeasurableEmbedding (Subtype.val : F → S) :=
    MeasurableEmbedding.subtype_coe hF.measurableSet
  have hfull (n : ℕ) : ∀ᵐ x ∂(μ n : Measure S), x ∈ F := by
    rw [ae_iff]
    exact hnull _ (hμ n)
  let ν : ℕ → ProbabilityMeasure F := fun n =>
    ⟨(μ n : Measure S).comap Subtype.val,
      he.isProbabilityMeasure_comap (by simpa only [Subtype.range_val] using hfull n)⟩
  have htight : IsTightMeasureSet { (ρ : Measure F) | ρ ∈ range ν } := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      hA.isTightMeasureSet ε hε
    refine ⟨(Subtype.val : F → S) ⁻¹' K,
      hF.isClosedEmbedding_subtypeVal.isCompact_preimage hK, ?_⟩
    rintro _ ⟨ρ, ⟨n, rfl⟩, rfl⟩
    change ((μ n : Measure S).comap Subtype.val) ((Subtype.val : F → S) ⁻¹' K)ᶜ ≤ ε
    rw [he.comap_apply]
    apply (measure_mono ?_).trans (hb _ ⟨μ n, hμ n, rfl⟩)
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have hcompact : IsCompact (closure (range ν)) :=
    isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨ρ, _, φ, hφ, hconv⟩ := hcompact.isSeqCompact
    (fun n => subset_closure (mem_range_self n))
  have hrecover (n : ℕ) : (ν n).map (Subtype.val : F → S) = μ n := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Subtype.val ((μ n : Measure S).comap Subtype.val) = (μ n : Measure S)
    rw [he.map_comap, Subtype.range_val, Measure.restrict_eq_self_of_ae_mem (hfull n)]
  refine ⟨ρ.map (Subtype.val : F → S), φ, hφ, ?_⟩
  have h := weaklyConverges_map atTop (ν ∘ φ) ρ
    (Subtype.val : F → S) continuous_subtype_val hconv
  simpa only [Function.comp_def, hrecover] using h

end
end ProbabilityFoundations.Ch06


