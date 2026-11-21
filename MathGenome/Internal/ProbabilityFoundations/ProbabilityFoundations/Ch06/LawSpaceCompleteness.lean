import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.SeparableWeakMetrization
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.LawSpaceSeparability
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.LawSpaceCompleteness
import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal
namespace ProbabilityFoundations.Ch06
universe u
noncomputable section
variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [SeparableSpace S] [CompleteSpace S]

/-- A Cauchy family puts uniformly little mass outside a small neighborhood
of a compact set. The compact set may depend on the radius and mass tolerance. -/
private lemma cauchy_compact_neighborhood (μ : ℕ → ProbabilityMeasure S)
    (hμ : @CauchySeq _ _ (prokhorovMetricSpace (S := S)).toUniformSpace _ μ)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∃ K : Set S, IsCompact K ∧ ∀ n,
      (μ n : Measure S) (cthickening r K)ᶜ ≤ ENNReal.ofReal ε := by
  let a := min r (ε / 2)
  have ha : 0 < a := lt_min hr (half_pos hε)
  have haε : a ≤ ε / 2 := min_le_right _ _
  have har : a ≤ r := min_le_left _ _
  have hc : ∃ N : ℕ, ∀ n ≥ N, prokhorovDist (μ n) (μ N) < a := by
    letI := prokhorovMetricSpace (S := S)
    simpa only [prokhorovMetricSpace_dist] using (Metric.cauchySeq_iff'.mp hμ) a ha
  obtain ⟨N, hN⟩ := hc
  have ht : IsTightMeasureSet {((ν : ProbabilityMeasure S) : Measure S) |
      ν ∈ μ '' Iic N} :=
    isTightMeasureSet_of_isCompact_closure (by
      rw [(finite_Iic N).image μ |>.isClosed.closure_eq]
      exact ((finite_Iic N).image μ).isCompact)
  obtain ⟨K, hK, hbound⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
      (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  have hinit (n : ℕ) (hn : n ≤ N) : (μ n : Measure S).real Kᶜ ≤ ε / 2 := by
    have h := hbound (μ n) ⟨μ n, ⟨n, hn, rfl⟩, rfl⟩
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa [Measure.real, ENNReal.toReal_ofReal (half_pos hε).le] using this
  refine ⟨K, hK, fun n => ?_⟩
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  by_cases hn : n ≤ N
  · exact (measureReal_mono (compl_subset_compl.mpr
        (self_subset_cthickening K))).trans ((hinit n hn).trans (by linarith))
  · have had := prokhorovAdmissible_of_levyProkhorovDist_lt (μ N) (μ n) a (by
      rw [← prokhorovDist_eq_levyProkhorovDist, prokhorovDist_comm]
      exact hN n (Nat.le_of_lt (Nat.lt_of_not_ge hn)))
    have hmass := (had.2 K hK.measurableSet).1
    have hsub : enlargement a K ⊆ cthickening r K := by
      rw [enlargement_eq_thickening]
      exact (thickening_subset_cthickening a K).trans (cthickening_mono har K)
    have hmono := measureReal_mono (μ := (μ n : Measure S)) hsub
    have hcomp := measureReal_compl (μ := (μ n : Measure S))
      (isClosed_cthickening (δ := r) (E := K)).measurableSet
    have hcompN := measureReal_compl (μ := (μ N : Measure S)) hK.measurableSet
    have hb := hinit N le_rfl
    simp only [probReal_univ] at hcomp hcompN
    linarith

/-- Uniform tightness follows by intersecting closed compact neighborhoods
at radii tending to zero, with summable bounds on the omitted mass. -/
private lemma cauchy_laws_tight (μ : ℕ → ProbabilityMeasure S)
    (hμ : @CauchySeq _ _ (prokhorovMetricSpace (S := S)).toUniformSpace _ μ) :
    IsTightMeasureSet (range (fun n => (μ n : Measure S))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ => htop ▸ le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨r, -, hr, hrlim⟩ : ∃ r : ℕ → ℝ,
      StrictAnti r ∧ (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have heps (n : ℕ) : 0 < ε.toReal / 2 / 2 ^ n := by positivity
  choose K hK hb using fun n =>
    cauchy_compact_neighborhood μ hμ (r n) (ε.toReal / 2 / 2 ^ n) (hr n) (heps n)
  let L := ⋂ n, cthickening (r n) (K n)
  have hLclosed : IsClosed L := isClosed_iInter fun _ => isClosed_cthickening
  have hLcompact : IsCompact L := by
    apply TotallyBounded.isCompact_of_isClosed _ hLclosed
    apply Metric.totallyBounded_iff.mpr
    intro δ hδ
    obtain ⟨n, hn⟩ := (hrlim.eventually (gt_mem_nhds (half_pos hδ))).exists
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp (hK n).totallyBounded
      (δ / 2) (half_pos hδ)
    refine ⟨t, ht, ?_⟩
    intro x hx
    have hx' : x ∈ thickening (δ / 2) (K n) :=
      cthickening_subset_thickening' (half_pos hδ) hn (K n) (mem_iInter.mp hx n)
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx'
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
    apply mem_iUnion₂.mpr
    refine ⟨z, hz, ?_⟩
    have hyz' : dist y z < δ / 2 := hyz
    have := dist_triangle x y z
    change dist x z < δ
    linarith
  refine ⟨L, hLcompact, ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    (μ n : Measure S) Lᶜ =
        (μ n : Measure S) (⋃ k, (cthickening (r k) (K k))ᶜ) := by simp [L]
    _ ≤ ∑' k, (μ n : Measure S) (cthickening (r k) (K k))ᶜ := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal (ε.toReal / 2 / 2 ^ k) := ENNReal.tsum_le_tsum fun k => hb k n
    _ = ε := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (heps k).le)
        (summable_geometric_two' ε.toReal), tsum_geometric_two', ENNReal.ofReal_toReal htop]

/-- Every Cauchy sequence converges for the original Prokhorov uniformity. -/
private lemma cauchy_laws_converge (μ : ℕ → ProbabilityMeasure S)
    (hμ : @CauchySeq _ _ (prokhorovMetricSpace (S := S)).toUniformSpace _ μ) :
    ∃ ν, Tendsto μ atTop
      (@nhds _ (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace ν) := by
  have ht := cauchy_laws_tight μ hμ
  have ht' : IsTightMeasureSet {((ν : ProbabilityMeasure S) : Measure S) | ν ∈ range μ} := by
    convert ht using 1
    ext ν
    simp
  have hc := isCompact_closure_of_isTightMeasureSet ht'
  obtain ⟨ν, -, f, hf, hconv⟩ := hc.isSeqCompact
    (fun n => subset_closure (mem_range_self n))
  have heq : (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (ProbabilityMeasure S)) := by
    rw [prokhorovMetricSpace_topology_eq_weak, weakTopology_eq]
  letI := prokhorovMetricSpace (S := S)
  refine ⟨ν, tendsto_nhds_of_cauchySeq_of_subseq hμ hf.tendsto_atTop ?_⟩
  rw [heq]
  exact hconv

/-- The particular metric π is complete, including when the law space is empty. -/
theorem lawSpace_complete :
    @CompleteSpace (ProbabilityMeasure S) (prokhorovMetricSpace (S := S)).toUniformSpace := by
  letI := prokhorovMetricSpace (S := S)
  exact Metric.complete_of_cauchySeq_tendsto cauchy_laws_converge

/-- Explicit sequential formulation in terms of the source's infimum distance. -/
theorem prokhorov_cauchy_sequence_converges (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      prokhorovDist (μ m) (μ n) < ε) :
    ∃ ν : ProbabilityMeasure S,
      Tendsto (fun n => prokhorovDist (μ n) ν) atTop (𝓝 0) := by
  letI := prokhorovMetricSpace (S := S)
  have hc : CauchySeq μ := Metric.cauchySeq_iff.mpr (by
    simpa only [prokhorovMetricSpace_dist] using hμ)
  obtain ⟨ν, hν⟩ := cauchy_laws_converge μ hc
  refine ⟨ν, ?_⟩
  simpa only [prokhorovMetricSpace_dist] using tendsto_iff_dist_tendsto_zero.mp hν

/-- With the previously established separability and metrization, the weak law
space is Polish. Completeness above was proved for π itself. -/
theorem lawSpace_polish :
    @PolishSpace (ProbabilityMeasure S) (weakTopology (S := S)) := by
  have heq := prokhorovMetricSpace_topology_eq_weak (S := S)
  rw [← heq]
  letI := prokhorovMetricSpace (S := S)
  letI : CompleteSpace (ProbabilityMeasure S) := lawSpace_complete
  letI : @SeparableSpace (ProbabilityMeasure S)
    (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace :=
      lawSpace_separable (S := S)
  infer_instance

end
end ProbabilityFoundations.Ch06
