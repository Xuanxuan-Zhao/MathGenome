import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.SubnetConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetsAndSubnets

/-!
The interface between eventual-cofinal and Moore–Smith subnet conventions
(paper.tex, Proposition `d10:04:subnet-interface`). The pair construction
retains increasing images as part of its order; φ itself need not be monotone.
-/

universe u v w
namespace D10Topology.Ch04

abbrev EventuallyCofinal {E : Type w} {D : Type v} [Preorder E] [Preorder D] :=
  @Specs.D10Topology.Ch04.SubnetConventions.EventuallyCofinal E D _ _

theorem subnetMap_eventuallyCofinal {D : Type v} {E : Type w}
    [Preorder D] [Preorder E] (φ : E → D) (hφ : SubnetMap φ) :
    EventuallyCofinal φ :=
  subnetMap_eventually_above φ hφ

/-- The paper's pairs (d,e) with d ≤ φ(e). -/
def CommonRefinementIndex {D : Type v} {E : Type w} [Preorder D] (φ : E → D) :=
  {q : D × E // q.1 ≤ φ q.2}

instance commonRefinementIndexPreorder {D : Type v} {E : Type w}
    [Preorder D] [Preorder E] (φ : E → D) : Preorder (CommonRefinementIndex φ) where
  le q r := q.val.1 ≤ r.val.1 ∧ q.val.2 ≤ r.val.2 ∧ φ q.val.2 ≤ φ r.val.2
  le_refl q := ⟨le_rfl, le_rfl, le_rfl⟩
  le_trans q r s hqr hrs :=
    ⟨hqr.1.trans hrs.1, hqr.2.1.trans hrs.2.1, hqr.2.2.trans hrs.2.2⟩

instance commonRefinementIndexNonempty {D : Type v} {E : Type w}
    [Preorder D] [Nonempty E] (φ : E → D) : Nonempty (CommonRefinementIndex φ) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  exact ⟨⟨(φ e, e), le_rfl⟩⟩

/-- Choose a bound for both images, and then pass both indices and the
eventual-cofinality threshold. This supplies the extra image inequalities. -/
theorem commonRefinementIndex_directed {D : Type v} {E : Type w}
    [Preorder D] [IsDirectedOrder D] [Preorder E] [IsDirectedOrder E]
    (φ : E → D) (hφ : EventuallyCofinal φ) :
    IsDirectedOrder (CommonRefinementIndex φ) := by
  constructor
  intro q r
  obtain ⟨d, hqd, hrd⟩ := exists_ge_ge (φ q.val.2) (φ r.val.2)
  obtain ⟨e₀, he₀⟩ := hφ d
  obtain ⟨e₁, hqe₁, hre₁⟩ := exists_ge_ge q.val.2 r.val.2
  obtain ⟨e, he₁e, he₀e⟩ := exists_ge_ge e₁ e₀
  have hde : d ≤ φ e := he₀ e he₀e
  refine ⟨⟨(d, e), hde⟩, ?_, ?_⟩
  · exact ⟨q.property.trans hqd, hqe₁.trans he₁e, hqd.trans hde⟩
  · exact ⟨r.property.trans hrd, hre₁.trans he₁e, hrd.trans hde⟩

theorem commonRefinementIndex_alpha_subnetMap {D : Type v} {E : Type w}
    [Preorder D] [Preorder E] (φ : E → D) :
    SubnetMap (fun q : CommonRefinementIndex φ => q.val.2) := by
  refine ⟨fun _ _ h => h.2.1, ?_⟩
  intro e
  exact ⟨⟨(φ e, e), le_rfl⟩, le_rfl⟩

theorem commonRefinementIndex_beta_subnetMap {D : Type v} {E : Type w}
    [Preorder D] [Preorder E] (φ : E → D) (hφ : EventuallyCofinal φ) :
    SubnetMap (fun q : CommonRefinementIndex φ => φ q.val.2) := by
  refine ⟨fun _ _ h => h.2.2, ?_⟩
  intro d
  obtain ⟨e₀, he₀⟩ := hφ d
  exact ⟨⟨(d, e₀), he₀ e₀ le_rfl⟩, he₀ e₀ le_rfl⟩

/-- Both maps are monotone and cofinal, despite the weaker hypothesis on φ. -/
theorem common_mooreSmith_refinement {D : Type v} {E : Type w}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (φ : E → D) (hφ : EventuallyCofinal φ) :
    ∃ (H : Type (max v w)) (p : Preorder H),
      Nonempty H ∧ @IsDirectedOrder H p.toLE ∧
      ∃ (α : H → E) (β : H → D),
        @SubnetMap H E p _ α ∧ @SubnetMap H D p _ β ∧ β = φ ∘ α := by
  exact ⟨CommonRefinementIndex φ, commonRefinementIndexPreorder φ,
    commonRefinementIndexNonempty φ, commonRefinementIndex_directed φ hφ,
    (fun q => q.val.2), (fun q => φ q.val.2),
    commonRefinementIndex_alpha_subnetMap φ, commonRefinementIndex_beta_subnetMap φ hφ,
    rfl⟩

theorem net_common_mooreSmith_refinement {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (a : Net D X) (φ : E → D) (hφ : EventuallyCofinal φ) :
    ∃ (H : Type (max v w)) (p : Preorder H),
      Nonempty H ∧ @IsDirectedOrder H p.toLE ∧
      ∃ (α : H → E) (β : H → D),
        @SubnetMap H E p _ α ∧ @SubnetMap H D p _ β ∧
        β = φ ∘ α ∧ subnet (subnet a φ) α = subnet a β := by
  obtain ⟨H, p, hn, hd, α, β, hα, hβ, heq⟩ := common_mooreSmith_refinement φ hφ
  exact ⟨H, p, hn, hd, α, β, hα, hβ, heq, heq ▸ subnet_comp a φ α⟩

theorem clusters_of_eventual_subnet {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (t : TopologicalSpace X) (a : Net D X) (φ : E → D) (x : X)
    (hφ : EventuallyCofinal φ) (ha : Converges t (subnet a φ) x) : Clusters t a x := by
  obtain ⟨H, p, hn, hd, α, β, hα, hβ, _, heq⟩ :=
    net_common_mooreSmith_refinement a φ hφ
  let := p
  let := hn
  let := hd
  have hconv := converges_subnet t (subnet a φ) α x hα ha
  rw [heq] at hconv
  exact clusters_of_subnet t a β x hβ (converges_clusters t _ x hconv)

end D10Topology.Ch04
