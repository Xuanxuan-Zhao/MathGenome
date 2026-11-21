import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ProkhorovForward
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ProkhorovReverse

/-! Reverse Prokhorov and its singleton consequence (paper.tex 1859–1903).
Mathlib's reverse Prokhorov theorem gives tightness from compact weak closure.
The sequential formulation follows by metrizability of the weak topology on
laws on a separable metric space. -/

open MeasureTheory Filter Topology TopologicalSpace Set
open scoped ENNReal

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section

/-- Mathlib tightness implies the manuscript's strict, real-epsilon version.
Shrinking epsilon also handles the possible failure of a strict supremum
bound from pointwise strict bounds. -/
theorem uniformlyTight_of_isTightMeasureSet {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] {A : Set (ProbabilityMeasure S)}
    (hA : IsTightMeasureSet { (μ : Measure S) | μ ∈ A }) : UniformlyTight A := by
  rw [uniformlyTight_iff]
  intro ε hε
  obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    hA (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  refine ⟨K, hK, fun μ hμ => (hb _ ⟨μ, hμ, rfl⟩).trans_lt ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)

/-- Approximation by points of the original set transfers the subsequence
property to its closure in a metrizable space. -/
private theorem compact_closure_of_subsequences {X : Type u} [TopologicalSpace X]
    [MetrizableSpace X] (A : Set X)
    (hA : ∀ x : ℕ → X, (∀ n, x n ∈ A) →
      ∃ (a : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)) :
    IsCompact (closure A) := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  apply IsSeqCompact.isCompact
  intro x hx
  obtain ⟨u, -, hu_pos, hu⟩ : ∃ u : ℕ → ℝ, StrictAnti u ∧
      (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto 0
  have happ (n : ℕ) : ∃ y ∈ A, dist (x n) y < u n :=
    Metric.mem_closure_iff.mp (hx n) _ (hu_pos n)
  choose y hy hd using happ
  obtain ⟨a, φ, hφ, ha⟩ := hA y hy
  have hdist : Tendsto (fun n => dist (y (φ n)) (x (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => dist_nonneg (x := y (φ n)) (y := x (φ n)))
      ?_ (hu.comp hφ.tendsto_atTop)
    intro n
    rw [dist_comm]
    exact (hd (φ n)).le
  have hxlim : Tendsto (x ∘ φ) atTop (𝓝 a) := ha.congr_dist hdist
  exact ⟨a, isClosed_closure.mem_of_tendsto hxlim (Eventually.of_forall (fun n => hx (φ n))),
    φ, hφ, hxlim⟩

/-- Reverse Prokhorov for compact weak closure. -/
theorem prokhorov_reverse_compact_closure {S : Type u} [MetricSpace S]
    [CompleteSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)) (hA : IsCompact (closure A)) :
    UniformlyTight A :=
  uniformlyTight_of_isTightMeasureSet (isTightMeasureSet_of_isCompact_closure hA)

/-- Reverse Prokhorov for subsequences, whose limits need not be in A. -/
theorem prokhorov_reverse_subsequence {S : Type u} [MetricSpace S]
    [CompleteSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S))
    (hA : ∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
      ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
        WeaklyConverges atTop (μ ∘ φ) ν) : UniformlyTight A := by
  exact prokhorov_reverse_compact_closure A (compact_closure_of_subsequences A hA)

/-- The subsequence characterization of uniform tightness. -/
theorem uniformlyTight_iff_subsequence {S : Type u} [MetricSpace S]
    [CompleteSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)) :
    UniformlyTight A ↔ ∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
      ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
        WeaklyConverges atTop (μ ∘ φ) ν :=
  ⟨prokhorov_subsequence A, prokhorov_reverse_subsequence A⟩

/-- The compact weak closure characterization of uniform tightness. -/
theorem uniformlyTight_iff_compact_closure {S : Type u} [MetricSpace S]
    [CompleteSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)) : UniformlyTight A ↔ IsCompact (closure A) :=
  ⟨prokhorov_compact_closure A, prokhorov_reverse_compact_closure A⟩

/-- Equivalence of the two compactness conditions in reverse Prokhorov. -/
theorem compact_closure_iff_subsequence {S : Type u} [MetricSpace S]
    [CompleteSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)) :
    IsCompact (closure A) ↔ ∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
      ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
        WeaklyConverges atTop (μ ∘ φ) ν :=
  (uniformlyTight_iff_compact_closure A).symm.trans (uniformlyTight_iff_subsequence A)

/-- Every Borel probability law on a complete separable metric space is tight. -/
theorem probabilityMeasure_tight {S : Type u} [MetricSpace S] [CompleteSpace S]
    [SeparableSpace S] [MeasurableSpace S] [BorelSpace S] (μ : ProbabilityMeasure S) :
    Tight μ := by
  apply prokhorov_reverse_compact_closure {μ}
  simpa only [isClosed_singleton.closure_eq] using
    (isCompact_singleton : IsCompact ({μ} : Set (ProbabilityMeasure S)))

end
end ProbabilityFoundations.Ch06
