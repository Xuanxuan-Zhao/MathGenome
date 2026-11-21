import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetFilterBridge
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetsAndSubnets
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.ProperFilters

open Set Filter
universe u v w
namespace D10Topology.Ch04

abbrev Tail {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetFilterBridge.Tail D X _
abbrev TailFilter {D : Type v} {X : Type u} [Preorder D] :=
  @Specs.D10Topology.Ch04.NetFilterBridge.TailFilter D X _
abbrev FilterNetIndex {X : Type u} :=
  @Specs.D10Topology.Ch04.NetFilterBridge.FilterNetIndex X
abbrev filterNet {X : Type u} :=
  @Specs.D10Topology.Ch04.NetFilterBridge.filterNet X

theorem tails_filterBase {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X) :
    FilterBase (range (Tail a)) := by
  refine ⟨Set.range_nonempty _, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact ⟨a d, d, le_rfl, rfl⟩
  · rintro _ ⟨d, rfl⟩ _ ⟨e, rfl⟩
    obtain ⟨f, hdf, hef⟩ := exists_ge_ge d e
    refine ⟨Tail a f, mem_range_self f, ?_⟩
    rintro _ ⟨g, hfg, rfl⟩
    exact ⟨⟨g, hdf.trans hfg, rfl⟩, ⟨g, hef.trans hfg, rfl⟩⟩

theorem tailFilter_mem {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X) (A : Set X) :
    A ∈ TailFilter a ↔ EventuallyIn a A := by
  rw [show TailFilter a = GeneratedFilter (range (Tail a)) from rfl,
    base_generated_mem _ (tails_filterBase a)]
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, hd⟩
    exact ⟨d, fun e he => hd ⟨e, he, rfl⟩⟩
  · rintro ⟨d, hd⟩
    refine ⟨Tail a d, mem_range_self d, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact hd e he

theorem tailFilter_proper {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X) :
    (TailFilter a).NeBot := base_generates_proper _ (tails_filterBase a)

theorem tailFilter_converges {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [t : TopologicalSpace X] (a : D → X) (x : X) :
    FilterConverges (TailFilter a) x ↔ Converges t a x := by
  constructor
  · intro h N hN
    exact (tailFilter_mem a N).mp (h N hN)
  · intro h N hN
    exact (tailFilter_mem a N).mpr (h N hN)

theorem tail_mem_tailFilter {D : Type v} {X : Type u}
    [Preorder D] (a : D → X) (d : D) : Tail a d ∈ TailFilter a :=
  mem_generate_of_mem (mem_range_self d)

theorem tailFilter_clusters {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [t : TopologicalSpace X] (a : D → X) (x : X) :
    FilterClusters (TailFilter a) x ↔ Clusters t a x := by
  constructor
  · intro h N hN d
    obtain ⟨y, ⟨e, hde, hay⟩, hyN⟩ := h _ (tail_mem_tailFilter a d) N hN
    exact ⟨e, hde, hay ▸ hyN⟩
  · intro h U hU N hN
    obtain ⟨d, hd⟩ := (tailFilter_mem a U).mp hU
    obtain ⟨e, he, hae⟩ := h N hN d
    exact ⟨a e, hd e he, hae⟩

theorem filterNetIndex_le_iff {X : Type u} (F : Filter X)
    (p q : FilterNetIndex F) : p ≤ q ↔ q.val.1 ⊆ p.val.1 := Iff.rfl

instance filterNetIndex_nonempty {X : Type u} (F : Filter X) [F.NeBot] :
    Nonempty (FilterNetIndex F) := by
  obtain ⟨a, ha⟩ := Filter.nonempty_of_mem (univ_mem : (univ : Set X) ∈ F)
  exact ⟨⟨(univ, a), univ_mem, ha⟩⟩

instance filterNetIndex_directed {X : Type u} (F : Filter X) [F.NeBot] :
    IsDirectedOrder (FilterNetIndex F) := by
  constructor
  intro p q
  have hi := inter_mem p.property.1 q.property.1
  obtain ⟨a, ha⟩ := Filter.nonempty_of_mem hi
  exact ⟨⟨(p.val.1 ∩ q.val.1, a), hi, ha⟩, inter_subset_left, inter_subset_right⟩

theorem filterNet_tail {X : Type u} (F : Filter X) (p : FilterNetIndex F) :
    Tail (filterNet F) p = p.val.1 := by
  ext b
  constructor
  · rintro ⟨q, hpq, hqb⟩
    exact hqb ▸ hpq q.property.2
  · intro hb
    exact ⟨⟨(p.val.1, b), p.property.1, hb⟩, Subset.rfl, rfl⟩

theorem filterNet_tailFilter {X : Type u} (F : Filter X) [F.NeBot] :
    TailFilter (filterNet F) = F := by
  apply Filter.ext
  intro A
  rw [tailFilter_mem]
  constructor
  · rintro ⟨p, hp⟩
    apply mem_of_superset p.property.1
    intro b hb
    exact hp ⟨(p.val.1, b), p.property.1, hb⟩ Subset.rfl
  · intro hA
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem hA
    exact ⟨⟨(A, a), hA, ha⟩, fun q hq => hq q.property.2⟩

theorem subnet_tailFilter_finer {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (a : D → X) (φ : E → D) (hφ : SubnetMap φ) :
    FilterFiner (TailFilter (subnet a φ)) (TailFilter a) ∧
      TailFilter (subnet a φ) ≤ TailFilter a := by
  have hle : TailFilter (subnet a φ) ≤ TailFilter a := by
    intro A hA
    exact (tailFilter_mem _ _).mpr
      (eventuallyIn_subnet a φ A hφ ((tailFilter_mem a A).mp hA))
  exact ⟨(finer_iff_le _ _).mpr hle, hle⟩

end D10Topology.Ch04
