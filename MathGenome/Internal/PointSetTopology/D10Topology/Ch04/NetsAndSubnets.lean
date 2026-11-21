import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetsAndSubnets
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods

open Set
open scoped Topology
universe u v w z
namespace D10Topology.Ch04

abbrev Net (D : Type v) (X : Type u) := D → X
abbrev EventuallyIn {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.EventuallyIn D X _
abbrev FrequentlyIn {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.FrequentlyIn D X _
abbrev Converges {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.Converges D X _
abbrev Clusters {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.Clusters D X _
abbrev SubnetMap {E : Type w} {D : Type v} [Preorder E] [Preorder D] :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.SubnetMap E D _ _
abbrev subnet {E : Type w} {D : Type v} {X : Type u} :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.subnet E D X
abbrev HasConvergentSubnet {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetsAndSubnets.HasConvergentSubnet D X _

theorem subnetMap_eventually_above {D : Type v} {E : Type w} [Preorder D] [Preorder E]
    (φ : E → D) (h : SubnetMap φ) (d : D) : ∃ e₀, ∀ e, e₀ ≤ e → d ≤ φ e := by
  obtain ⟨e₀, he₀⟩ := h.2 d
  exact ⟨e₀, fun e he => he₀.trans (h.1 he)⟩

theorem eventuallyIn_subnet {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Preorder E] (a : Net D X) (φ : E → D) (A : Set X)
    (hφ : SubnetMap φ) (ha : EventuallyIn a A) : EventuallyIn (subnet a φ) A := by
  obtain ⟨d₀, hd₀⟩ := ha
  obtain ⟨e₀, he₀⟩ := subnetMap_eventually_above φ hφ d₀
  exact ⟨e₀, fun e he => hd₀ _ (he₀ e he)⟩

theorem converges_subnet {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Preorder E] (t : TopologicalSpace X)
    (a : Net D X) (φ : E → D) (x : X) (hφ : SubnetMap φ)
    (ha : Converges t a x) : Converges t (subnet a φ) x := by
  intro N hN
  exact eventuallyIn_subnet a φ N hφ (ha N hN)

theorem subnetMap_comp {D : Type v} {E : Type w} {F : Type z}
    [Preorder D] [Preorder E] [Preorder F] (φ : E → D) (ψ : F → E)
    (hφ : SubnetMap φ) (hψ : SubnetMap ψ) : SubnetMap (φ ∘ ψ) := by
  refine ⟨hφ.1.comp hψ.1, ?_⟩
  intro d
  obtain ⟨e, he⟩ := hφ.2 d
  obtain ⟨f, hf⟩ := hψ.2 e
  exact ⟨f, he.trans (hφ.1 hf)⟩

theorem subnet_comp {D : Type v} {E : Type w} {F : Type z} {X : Type u}
    (a : Net D X) (φ : E → D) (ψ : F → E) :
    subnet (subnet a φ) ψ = subnet a (φ ∘ ψ) := rfl

theorem frequentlyIn_of_subnet {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Preorder E] (a : Net D X) (φ : E → D) (A : Set X)
    (hφ : SubnetMap φ) (ha : FrequentlyIn (subnet a φ) A) : FrequentlyIn a A := by
  intro d₀
  obtain ⟨e₀, he₀⟩ := hφ.2 d₀
  obtain ⟨e, he, hae⟩ := ha e₀
  exact ⟨φ e, he₀.trans (hφ.1 he), hae⟩

theorem clusters_of_subnet {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Preorder E] (t : TopologicalSpace X)
    (a : Net D X) (φ : E → D) (x : X) (hφ : SubnetMap φ)
    (ha : Clusters t (subnet a φ) x) : Clusters t a x := by
  intro N hN
  exact frequentlyIn_of_subnet a φ N hφ (ha N hN)

theorem converges_clusters {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (t : TopologicalSpace X)
    (a : Net D X) (x : X) (ha : Converges t a x) : Clusters t a x := by
  intro N hN d
  obtain ⟨d₀, hd₀⟩ := ha N hN
  obtain ⟨e, hde, hd₀e⟩ := exists_ge_ge d d₀
  exact ⟨e, hde, hd₀ e hd₀e⟩

/-- The index set in the paper's constructive cluster-subnet proof. -/
def ClusterIndex {D : Type v} {X : Type u} (t : TopologicalSpace X)
    (a : Net D X) (x : X) :=
  {q : D × Set X // IsOpen[t] q.2 ∧ x ∈ q.2 ∧ a q.1 ∈ q.2}

instance clusterIndexPreorder {D : Type v} {X : Type u} [Preorder D]
    (t : TopologicalSpace X) (a : Net D X) (x : X) : Preorder (ClusterIndex t a x) where
  le q r := q.val.1 ≤ r.val.1 ∧ r.val.2 ⊆ q.val.2
  le_refl q := ⟨le_rfl, Subset.rfl⟩
  le_trans q r s hqr hrs := ⟨hqr.1.trans hrs.1, hrs.2.trans hqr.2⟩

instance clusterIndexNonempty {D : Type v} {X : Type u} [Nonempty D]
    (t : TopologicalSpace X) (a : Net D X) (x : X) : Nonempty (ClusterIndex t a x) := by
  let := t
  obtain ⟨d⟩ := ‹Nonempty D›
  exact ⟨⟨(d, univ), isOpen_univ, mem_univ x, mem_univ (a d)⟩⟩

/-- Clustering makes the pair order directed: refine both open witnesses and
pass the upper bound of both original stages. Antisymmetry is never needed. -/
theorem clusterIndex_directed {D : Type v} {X : Type u}
    [Preorder D] [IsDirectedOrder D] (t : TopologicalSpace X)
    (a : Net D X) (x : X) (ha : Clusters t a x) :
    IsDirectedOrder (ClusterIndex t a x) := by
  let := t
  constructor
  intro q r
  obtain ⟨d₀, hqd₀, hrd₀⟩ := exists_ge_ge q.val.1 r.val.1
  have hU : Ch01.Neighborhood t x (q.val.2 ∩ r.val.2) :=
    ⟨q.val.2 ∩ r.val.2, q.property.1.inter r.property.1,
      ⟨q.property.2.1, r.property.2.1⟩, Subset.rfl⟩
  obtain ⟨d, hd, had⟩ := ha _ hU d₀
  refine ⟨⟨(d, q.val.2 ∩ r.val.2),
    q.property.1.inter r.property.1, ⟨q.property.2.1, r.property.2.1⟩, had⟩,
    ⟨hqd₀.trans hd, inter_subset_left⟩, ⟨hrd₀.trans hd, inter_subset_right⟩⟩

theorem clusterIndex_projection_subnetMap {D : Type v} {X : Type u}
    [Preorder D] (t : TopologicalSpace X) (a : Net D X) (x : X) :
    SubnetMap (fun q : ClusterIndex t a x => q.val.1) := by
  let := t
  refine ⟨fun _ _ h => h.1, ?_⟩
  intro d
  exact ⟨⟨(d, univ), isOpen_univ, mem_univ x, mem_univ (a d)⟩, le_rfl⟩

theorem clusterIndex_subnet_converges {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] (t : TopologicalSpace X)
    (a : Net D X) (x : X) (ha : Clusters t a x) :
    Converges t (subnet a (fun q : ClusterIndex t a x => q.val.1)) x := by
  intro N hN
  obtain ⟨U, hU, hxU, hUN⟩ := hN
  have hnU : Ch01.Neighborhood t x U := ⟨U, hU, hxU, Subset.rfl⟩
  obtain ⟨d₀⟩ := ‹Nonempty D›
  obtain ⟨d, _, had⟩ := ha U hnU d₀
  refine ⟨⟨(d, U), hU, hxU, had⟩, ?_⟩
  intro q hq
  exact hUN (hq.2 q.property.2.2)

/-- A genuine Moore–Smith subnet, with all directed-index data supplied. -/
theorem cluster_iff_convergent_subnet {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (t : TopologicalSpace X)
    (a : Net D X) (x : X) : Clusters t a x ↔ HasConvergentSubnet t a x := by
  constructor
  · intro ha
    exact ⟨ClusterIndex t a x, clusterIndexPreorder t a x,
      clusterIndexNonempty t a x, clusterIndex_directed t a x ha,
      (fun q => q.val.1), clusterIndex_projection_subnetMap t a x,
      clusterIndex_subnet_converges t a x ha⟩
  · rintro ⟨E, p, hn, hd, φ, hφ, hconv⟩
    let := p
    let := hn
    let := hd
    exact clusters_of_subnet t a φ x hφ (converges_clusters t _ x hconv)

end D10Topology.Ch04
