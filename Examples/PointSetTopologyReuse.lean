import Examples.PointSetTopologyReuseSpecs

open Set
universe u v

namespace GenomeTopologyProbe

theorem arbitrary_products : Specs.GenomeTopologyProbe.arbitrary_products.{u,v} := by
  intro I X tX hX
  have hCover : ∀ i, @D10Topology.Ch05.CoverCompact (X i) (tX i) :=
    fun i => (@D10Topology.Ch05.coverCompact_iff_compactSpace (X i) (tX i)).mpr (hX i)
  have hProduct := D10Topology.Ch05.tychonoff_product tX hCover
  rw [D10Topology.Ch03.productTopology_eq_pi] at hProduct
  exact (@D10Topology.Ch05.coverCompact_iff_compactSpace (∀ i, X i)
    (@Pi.topologicalSpace I X tX)).mp hProduct

theorem closed_set_separation : Specs.GenomeTopologyProbe.closed_set_separation.{u} := by
  intro X _ hN A B hA hB hAB
  exact (D10Topology.Ch07.normal_iff_urysohn X).mp hN A B hA hB hAB

theorem interval_extension : Specs.GenomeTopologyProbe.interval_extension.{u} := by
  intro X _ hN A hA a b hab f hf
  exact D10Topology.Ch07.tietze_bounded hN A hA a b hab f hf

theorem compact_neighborhood : Specs.GenomeTopologyProbe.compact_neighborhood.{u} := by
  intro X _ hLC hT2 C U hC hU hCU
  have hX : D10Topology.Ch11.LCH X :=
    (D10Topology.Ch11.lch_iff_locallyCompactSpace_and_t2 X).mpr ⟨hLC, hT2⟩
  exact D10Topology.Ch11.compact_set_shrinking hX C U hC hU hCU

theorem canonical_metric_completion : Specs.GenomeTopologyProbe.canonical_metric_completion.{u} := by
  intro X d
  refine ⟨?_, ?_, ?_⟩
  · exact (D10Topology.Ch09.sequentiallyComplete_iff_mathlib _).mp
      (D10Topology.Ch09.completion_complete d)
  · exact (D10Topology.Ch09.isometry_iff_mathlib _ _ _).mp
      (D10Topology.Ch09.completion_isometry d)
  · exact D10Topology.Ch09.completion_dense d

theorem euclidean_compact_bridge : Specs.GenomeTopologyProbe.euclidean_compact_bridge := by
  intro n K hClosed hBounded
  have hOld : D04.Compact K := (D04.compact_iff_closed_bounded K).mpr
    ⟨(D04.closed_iff_isClosed K).mpr hClosed, hBounded⟩
  exact (D10Topology.Ch05.subspaceCompact_iff_isCompact K).mpr
    ((D04.compact_iff_isCompact K).mp hOld)

end GenomeTopologyProbe
