import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CompactConvergence
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Ultranets
import Mathlib.Order.ULift

/-! The six compactness/convergence criteria of paper.tex d10:05:compact-convergence.
The filters, nets, neighborhoods and Moore–Smith subnets are the accepted
canonical objects. Ultrafilter extension is the choice-dependent implication.
No step assumes that a cluster point or a limit is unique.
-/

open Set Filter
universe u v
namespace D10Topology.Ch05
open D10Topology.Ch04

/-- Open-cover compactness is equivalent to clustering of all proper filters. -/
theorem compact_iff_filter_cluster_points (X : Type u) [TopologicalSpace X] :
    CoverCompact X ↔ ∀ F : Filter X, F.NeBot → ∃ x : X, FilterClusters F x := by
  constructor
  · intro h F hF
    let := hF
    let : CompactSpace X := (coverCompact_iff_compactSpace X).mp h
    obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace F
    exact ⟨x, (clusters_iff_clusterPt F x).mpr hx⟩
  · intro h
    apply (coverCompact_iff_isCompact_univ X).mpr
    intro F hF _
    obtain ⟨x, hx⟩ := h F hF
    exact ⟨x, mem_univ x, (clusters_iff_clusterPt F x).mp hx⟩

/-- This direction permits an index preorder in any universe. -/
theorem compact_net_cluster {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] [t : TopologicalSpace X]
    (h : CoverCompact X) (a : D → X) : ∃ x : X, Clusters t a x := by
  obtain ⟨x, hx⟩ := (compact_iff_filter_cluster_points X).mp h
    (TailFilter a) (tailFilter_proper a)
  exact ⟨x, (tailFilter_clusters a x).mp hx⟩

theorem compact_net_convergent_subnet {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] [t : TopologicalSpace X]
    (h : CoverCompact X) (a : D → X) : ∃ x : X, HasConvergentSubnet t a x := by
  obtain ⟨x, hx⟩ := compact_net_cluster h a
  exact ⟨x, (cluster_iff_convergent_subnet t a x).mp hx⟩

theorem compact_iff_net_cluster_points (X : Type u) [t : TopologicalSpace X] :
    CoverCompact X ↔ ∀ (D : Type (max u v)) [Preorder D] [Nonempty D]
      [IsDirectedOrder D] (a : D → X), ∃ x : X, Clusters t a x := by
  constructor
  · intro h D _ _ _ a
    exact compact_net_cluster h a
  · intro h
    apply (compact_iff_filter_cluster_points X).mpr
    intro F hF
    let := hF
    -- Lifting changes only the universe of the canonical filter-net index.
    let E := ULift.{v} (FilterNetIndex F)
    let : IsDirectedOrder E := ⟨fun p q => by
      obtain ⟨r, hpr, hqr⟩ := exists_ge_ge p.down q.down
      exact ⟨⟨r⟩, hpr, hqr⟩⟩
    obtain ⟨x, hx⟩ := h E (fun q => filterNet F q.down)
    have hc : Clusters t (filterNet F) x := by
      intro N hN d
      obtain ⟨e, hde, he⟩ := hx N hN (ULift.up d)
      exact ⟨e.down, hde, he⟩
    have hf := (tailFilter_clusters (filterNet F) x).mpr hc
    rw [filterNet_tailFilter F] at hf
    exact ⟨x, hf⟩

theorem compact_iff_convergent_subnets (X : Type u) [t : TopologicalSpace X] :
    CoverCompact X ↔ ∀ (D : Type (max u v)) [Preorder D] [Nonempty D]
      [IsDirectedOrder D] (a : D → X), ∃ x : X, HasConvergentSubnet t a x := by
  constructor
  · intro h D _ _ _ a
    exact compact_net_convergent_subnet h a
  · intro h
    apply (compact_iff_net_cluster_points.{u, v} X).mpr
    intro D _ _ _ a
    obtain ⟨x, hx⟩ := h D a
    exact ⟨x, (cluster_iff_convergent_subnet t a x).mpr hx⟩

/-- The reverse direction explicitly uses extension of a proper filter to an
ultrafilter. A limit of that extension clusters for the original filter. -/
theorem compact_iff_ultrafilter_convergence (X : Type u) [TopologicalSpace X] :
    CoverCompact X ↔ ∀ F : Filter X, IsUltrafilter F →
      ∃ x : X, FilterConverges F x := by
  constructor
  · intro h F hF
    obtain ⟨x, hx⟩ := (compact_iff_filter_cluster_points X).mp h F hF.1
    exact ⟨x, ultrafilter_converges_at_cluster F hF x hx⟩
  · intro h
    apply (compact_iff_filter_cluster_points X).mpr
    intro F hF
    obtain ⟨U, hU, hUF⟩ := proper_filter_extension F hF
    obtain ⟨x, hx⟩ := h U hU
    refine ⟨x, ?_⟩
    intro A hA N hN
    exact hU.1.nonempty_of_mem (inter_mem (hUF hA) (hx N hN))

theorem compact_ultranet_converges {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] [t : TopologicalSpace X]
    (h : CoverCompact X) (a : D → X) (ha : IsUltranet a) :
    ∃ x : X, Converges t a x := by
  have hU := (ultranet_iff_tailFilter_ultrafilter a).mp ha
  obtain ⟨x, hx⟩ := (compact_iff_ultrafilter_convergence X).mp h (TailFilter a) hU
  exact ⟨x, (tailFilter_converges a x).mp hx⟩

theorem compact_iff_ultranet_convergence (X : Type u) [t : TopologicalSpace X] :
    CoverCompact X ↔ ∀ (D : Type (max u v)) [Preorder D] [Nonempty D]
      [IsDirectedOrder D] (a : D → X), IsUltranet a → ∃ x : X, Converges t a x := by
  constructor
  · intro h D _ _ _ a ha
    exact compact_ultranet_converges h a ha
  · intro h
    apply (compact_iff_ultrafilter_convergence X).mpr
    intro F hF
    let := hF.1
    have hu : IsUltranet (filterNet F) := by
      apply (ultranet_iff_tailFilter_ultrafilter _).mpr
      rwa [filterNet_tailFilter F]
    let E := ULift.{v} (FilterNetIndex F)
    let : IsDirectedOrder E := ⟨fun p q => by
      obtain ⟨r, hpr, hqr⟩ := exists_ge_ge p.down q.down
      exact ⟨⟨r⟩, hpr, hqr⟩⟩
    have huE : IsUltranet (fun q : E => filterNet F q.down) := by
      intro A
      rcases hu A with ⟨d, hd⟩ | ⟨d, hd⟩
      · exact Or.inl ⟨⟨d⟩, fun e he => hd e.down he⟩
      · exact Or.inr ⟨⟨d⟩, fun e he => hd e.down he⟩
    obtain ⟨x, hx⟩ := h E (fun q => filterNet F q.down) huE
    have hc : Converges t (filterNet F) x := by
      intro N hN
      obtain ⟨d, hd⟩ := hx N hN
      exact ⟨d.down, fun e he => hd (ULift.up e) he⟩
    have hf := (tailFilter_converges (filterNet F) x).mpr hc
    rw [filterNet_tailFilter F] at hf
    exact ⟨x, hf⟩

/-- All six statements, in the source order. Each existential is plain existence;
there is no assertion that its point is the only possible cluster point or limit. -/
theorem compactness_convergence_equivalences (X : Type u) [t : TopologicalSpace X] :
    List.TFAE [
      CoverCompact X,
      (∀ F : Filter X, F.NeBot → ∃ x : X, FilterClusters F x),
      (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : D → X), ∃ x : X, Clusters t a x),
      (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : D → X), ∃ x : X, HasConvergentSubnet t a x),
      (∀ F : Filter X, IsUltrafilter F → ∃ x : X, FilterConverges F x),
      (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : D → X), IsUltranet a → ∃ x : X, Converges t a x)] := by
  apply List.tfae_of_forall (b := CoverCompact X)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact (compact_iff_filter_cluster_points X).symm
  · exact (compact_iff_net_cluster_points.{u, v} X).symm
  · exact (compact_iff_convergent_subnets.{u, v} X).symm
  · exact (compact_iff_ultrafilter_convergence X).symm
  · exact (compact_iff_ultranet_convergence.{u, v} X).symm

end D10Topology.Ch05
