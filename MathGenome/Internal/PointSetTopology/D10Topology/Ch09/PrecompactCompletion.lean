import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.PrecompactCompletion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricCompletion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CompactEquivalences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.TotalBoundedPermanence

/-! Corollary d10:09:precompact-completion.
Total boundedness of the dense isometric image passes to the completion by
closure. Completeness then gives compactness. For subsets of a complete space,
the same argument uses completeness of the closed closure. The final assertion
transfers finite nets using both uniformly continuous identity maps. -/

open Set
universe u

namespace D10Topology.Ch09

theorem totallyBounded_iff_completion_compact {X : Type u} (d : MetricSpace X) :
    TotallyBounded d.toPseudoMetricSpace ↔
      @Ch05.CoverCompact (MetricCompletion d)
        (metricTopology (completionMetric d).toPseudoMetricSpace) := by
  let := d
  have hι : _root_.Isometry (completionEmbedding d) :=
    (isometry_iff_mathlib _ _ _).mp (completion_isometry d)
  have hImage : _root_.TotallyBounded (range (completionEmbedding d)) ↔
      _root_.TotallyBounded (univ : Set X) := by
    simpa only [image_univ] using
      (totallyBounded_image_iff hι.isUniformInducing (s := (univ : Set X)))
  have hTB : TotallyBounded d.toPseudoMetricSpace ↔
      TotallyBounded (completionMetric d).toPseudoMetricSpace := by
    rw [totallyBounded_iff_mathlib, totallyBounded_iff_mathlib]
    constructor
    · intro h
      have hclosure := (hImage.mpr h).closure
      simpa only [(completion_dense d).closure_range] using hclosure
    · intro h
      exact hImage.mp (h.subset (subset_univ _))
  constructor
  · intro h
    exact (coverCompact_iff_complete_totallyBounded (completionMetric d)).mpr
      ⟨completion_complete d, hTB.mp h⟩
  · intro h
    exact hTB.mpr
      ((coverCompact_iff_complete_totallyBounded (completionMetric d)).mp h).2

theorem closure_compact_iff_totallyBounded {X : Type u} [d : MetricSpace X]
    (A : Set X) (hc : SequentiallyComplete d.toPseudoMetricSpace) :
    Ch05.SubspaceCompact (closure A) ↔
      TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace := by
  let := (sequentiallyComplete_iff_mathlib _).mp hc
  rw [Ch05.subspaceCompact_iff_isCompact, totallyBounded_subspace_iff]
  constructor
  · intro h
    exact h.totallyBounded.subset subset_closure
  · intro h
    exact h.closure.isCompact_of_isClosed isClosed_closure

private theorem uniformlyContinuous_id_totallyBounded_subspace {X : Type u}
    (d e : MetricSpace X)
    (h : UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace id)
    (A : Set X)
    (hA : TotallyBounded
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace) :
    TotallyBounded
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective e).toPseudoMetricSpace := by
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := h ε hε
  obtain ⟨F, hF, hcover⟩ := hA δ hδ
  refine ⟨F, hF, eq_univ_of_forall fun a => ?_⟩
  obtain ⟨b, hb, hba⟩ := mem_iUnion₂.mp (hcover.symm ▸ mem_univ a)
  exact mem_iUnion₂.mpr ⟨b, hb, hδε b.val a.val hba⟩

theorem uniformlyEquivalent_totallyBounded_subsets {X : Type u} (d e : MetricSpace X)
    (h : UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace) (A : Set X) :
    TotallyBounded
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace ↔
    TotallyBounded
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective e).toPseudoMetricSpace :=
  ⟨uniformlyContinuous_id_totallyBounded_subspace d e h.1 A,
    uniformlyContinuous_id_totallyBounded_subspace e d h.2 A⟩

end D10Topology.Ch09
