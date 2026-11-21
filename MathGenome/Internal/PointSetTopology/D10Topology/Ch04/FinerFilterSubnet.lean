import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.FinerFilterSubnet
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetFilterBridge

/-! Refining a tail filter by an actual Moore–Smith subnet.
This implements the triple construction in paper.tex, d10:04:finer-subnet.
Both original-index coordinates increase and the filter member decreases. -/

open Set Filter
universe u v
namespace D10Topology.Ch04

/-- The paper's triples `(d, U, e)` with `d ≤ e` and `a e ∈ U ∈ G`. -/
structure TailRefinementIndex {D : Type v} {X : Type u} [Preorder D]
    (a : D → X) (G : Filter X) where
  stage : D
  region : Set X
  index : D
  region_mem : region ∈ G
  stage_le_index : stage ≤ index
  term_mem : a index ∈ region

instance tailRefinementIndexPreorder {D : Type v} {X : Type u} [Preorder D]
    (a : D → X) (G : Filter X) : Preorder (TailRefinementIndex a G) where
  le q r := q.stage ≤ r.stage ∧ q.index ≤ r.index ∧ r.region ⊆ q.region
  le_refl _ := ⟨le_rfl, le_rfl, Subset.rfl⟩
  le_trans _ _ _ hqr hrs :=
    ⟨hqr.1.trans hrs.1, hqr.2.1.trans hrs.2.1, hrs.2.2.trans hqr.2.2⟩

instance tailRefinementIndexNonempty {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] (a : D → X) (G : Filter X) :
    Nonempty (TailRefinementIndex a G) := by
  obtain ⟨d⟩ := ‹Nonempty D›
  exact ⟨⟨d, univ, d, univ_mem, le_rfl, mem_univ _⟩⟩

/-- Every member of the finer proper filter meets every original tail. -/
theorem exists_tail_term_mem {D : Type v} {X : Type u}
    [Preorder D] (a : D → X) (G : Filter X) [G.NeBot]
    (hG : FilterFiner G (TailFilter a)) (d : D) (U : Set X) (hU : U ∈ G) :
    ∃ e, d ≤ e ∧ a e ∈ U := by
  obtain ⟨z, hzU, e, hde, hez⟩ :=
    Filter.nonempty_of_mem (inter_mem hU (hG (tail_mem_tailFilter a d)))
  exact ⟨e, hde, hez.symm ▸ hzU⟩

theorem tailRefinementIndex_directed {D : Type v} {X : Type u}
    [Preorder D] [IsDirectedOrder D] (a : D → X) (G : Filter X) [G.NeBot]
    (hG : FilterFiner G (TailFilter a)) :
    IsDirectedOrder (TailRefinementIndex a G) := by
  constructor
  intro q r
  obtain ⟨b, hqb, hrb⟩ := exists_ge_ge q.index r.index
  obtain ⟨e, hbe, he⟩ := exists_tail_term_mem a G hG b
    (q.region ∩ r.region) (inter_mem q.region_mem r.region_mem)
  refine ⟨⟨b, q.region ∩ r.region, e,
    inter_mem q.region_mem r.region_mem, hbe, he⟩, ?_, ?_⟩
  · exact ⟨q.stage_le_index.trans hqb, hqb.trans hbe, inter_subset_left⟩
  · exact ⟨r.stage_le_index.trans hrb, hrb.trans hbe, inter_subset_right⟩

theorem tailRefinementIndex_projection_subnetMap {D : Type v} {X : Type u}
    [Preorder D] (a : D → X) (G : Filter X) :
    SubnetMap (fun q : TailRefinementIndex a G => q.index) := by
  refine ⟨fun _ _ h => h.2.1, ?_⟩
  intro d
  exact ⟨⟨d, univ, d, univ_mem, le_rfl, mem_univ _⟩, le_rfl⟩

theorem tailRefinementIndex_eventually_mem {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] (a : D → X) (G : Filter X) [G.NeBot]
    (hG : FilterFiner G (TailFilter a)) (U : Set X) (hU : U ∈ G) :
    EventuallyIn (subnet a (fun q : TailRefinementIndex a G => q.index)) U := by
  obtain ⟨d⟩ := ‹Nonempty D›
  obtain ⟨e, hde, he⟩ := exists_tail_term_mem a G hG d U hU
  refine ⟨⟨d, U, e, hU, hde, he⟩, ?_⟩
  intro q hq
  exact hq.2.2 q.term_mem

/-- A single subnet refines `G` and therefore preserves every limit of `G`. -/
theorem finer_filter_subnet {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (a : D → X) (G : Filter X) [G.NeBot]
    (hG : FilterFiner G (TailFilter a)) :
    ∃ (E : Type (max u v)) (p : Preorder E),
      Nonempty E ∧ @IsDirectedOrder E p.toLE ∧
      ∃ φ : E → D, @SubnetMap E D p _ φ ∧
        (@TailFilter E X p (subnet a φ)).NeBot ∧
        FilterFiner (@TailFilter E X p (subnet a φ)) G ∧
        ∀ (t : TopologicalSpace X) (x₀ : X),
          @FilterConverges X t G x₀ → @Converges E X p t (subnet a φ) x₀ := by
  let E := TailRefinementIndex a G
  letI : IsDirectedOrder E := tailRefinementIndex_directed a G hG
  let φ : E → D := fun q => q.index
  have hfine : FilterFiner (TailFilter (subnet a φ)) G := by
    intro U hU
    exact (tailFilter_mem _ U).mpr (tailRefinementIndex_eventually_mem a G hG U hU)
  refine ⟨E, inferInstance, inferInstance, inferInstance, φ,
    tailRefinementIndex_projection_subnetMap a G, tailFilter_proper _, hfine, ?_⟩
  intro t x₀ hconv
  letI := t
  exact (tailFilter_converges _ x₀).mp (fun N hN => hfine (hconv N hN))

end D10Topology.Ch04
