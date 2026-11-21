import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.FilteredContinua
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CompactImagesAndSeparation

/-!
The filtered intersection has the finite intersection property. For
connectedness, two disjoint relatively closed pieces of the intersection
are compact, so chapter 5 separates them by disjoint open neighborhoods.
Compactness and filteredness put some A i inside their union, contradicting
the connectedness of A i. No normality theorem or instance is assumed.
-/

open Set Topology
universe u v

namespace D10Topology.Ch06

/-- An arbitrary nonempty downward filtered family of nonempty closed
connected subsets of a compact Hausdorff space has nonempty connected
intersection. -/
theorem filtered_continua {K : Type u} [TopologicalSpace K] [T2Space K]
    {ι : Type v} [Nonempty ι] (A : ι → Set K)
    (hK : Ch05.CoverCompact K) (hne : ∀ i, (A i).Nonempty)
    (hclosed : ∀ i, IsClosed (A i)) (hconn : ∀ i, ConnectedSubset (A i))
    (hfilter : ∀ i j, ∃ k, A k ⊆ A i ∩ A j) :
    (⋂ i, A i).Nonempty ∧ ConnectedSubset (⋂ i, A i) := by
  classical
  letI : CompactSpace K := (Ch05.coverCompact_iff_compactSpace K).mp hK
  have hd : Directed (· ⊇ ·) A := by
    intro i j
    obtain ⟨k, hk⟩ := hfilter i j
    exact ⟨k, fun x hx => (hk hx).1, fun x hx => (hk hx).2⟩
  refine ⟨IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    A hd hne (fun i => (hclosed i).isCompact) hclosed, ?_⟩
  apply (connectedSubset_iff_isPreconnected _).mpr
  apply isPreconnected_closed_iff.mpr
  intro B C hB hC hcover hLB hLC
  by_contra hdis
  have hL : IsClosed (⋂ i, A i) := isClosed_iInter hclosed
  have hBC : Disjoint ((⋂ i, A i) ∩ B) ((⋂ i, A i) ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxC
    exact hdis ⟨x, hxB.1, hxB.2, hxC.2⟩
  obtain ⟨U, V, hU, hV, hBU, hCV, hUV⟩ :=
    Ch05.disjoint_compact_separation _ _
      ((Ch05.subspaceCompact_iff_isCompact _).mpr (hL.inter hB).isCompact)
      ((Ch05.subspaceCompact_iff_isCompact _).mpr (hL.inter hC).isCompact) hBC
  have hLUV : (⋂ i, A i) ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxB | hxC
    · exact Or.inl (hBU ⟨hx, hxB⟩)
    · exact Or.inr (hCV ⟨hx, hxC⟩)
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_compactSpace hd hclosed
    (mem_nhdsSet_iff_exists.mpr ⟨U ∪ V, hU.union hV, hLUV, Subset.rfl⟩)
  obtain ⟨b, hbL, hbB⟩ := hLB
  obtain ⟨c, hcL, hcC⟩ := hLC
  obtain ⟨x, _, hxU, hxV⟩ :=
    ((connectedSubset_iff_isPreconnected _).mp (hconn i)) U V hU hV hi
      ⟨b, mem_iInter.mp hbL i, hBU ⟨hbL, hbB⟩⟩
      ⟨c, mem_iInter.mp hcL i, hCV ⟨hcL, hcC⟩⟩
  exact Set.disjoint_left.mp hUV hxU hxV

end D10Topology.Ch06
