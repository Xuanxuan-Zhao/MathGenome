import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetsAndSubnets

/-!
Independent specifications for paper.tex, `d10:04:subnet-interface`.
Eventual cofinality does not impose monotonicity. The common refinement
has an actual nonempty directed preorder and two Moore–Smith index maps.
All spaces and both index universes are arbitrary.
-/

universe u v w
namespace Specs.D10Topology.Ch04.SubnetConventions

open NetsAndSubnets

/-- The weaker index-map convention: every original stage is eventually passed. -/
def EventuallyCofinal {E : Type w} {D : Type v} [Preorder E] [Preorder D]
    (φ : E → D) : Prop :=
  ∀ d, ∃ e₀, ∀ e, e₀ ≤ e → d ≤ φ e

def eventuallyCofinalType :=
  {E : Type w} → {D : Type v} → [Preorder E] → [Preorder D] → (E → D) → Prop

def eventuallyCofinalValue : eventuallyCofinalType :=
  fun {E} {D} [Preorder E] [Preorder D] => @EventuallyCofinal E D _ _

/-- The monotone convention implies the eventual convention. -/
def subnetMap_eventuallyCofinal : Prop :=
  ∀ {D : Type v} {E : Type w} [Preorder D] [Preorder E] (φ : E → D),
    SubnetMap φ → EventuallyCofinal φ

/-- A common Moore–Smith refinement at the level of index maps. -/
def common_mooreSmith_refinement : Prop :=
  ∀ {D : Type v} {E : Type w}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (φ : E → D), EventuallyCofinal φ →
    ∃ (H : Type (max v w)) (p : Preorder H),
      Nonempty H ∧ @IsDirectedOrder H p.toLE ∧
      ∃ (α : H → E) (β : H → D),
        @SubnetMap H E p _ α ∧ @SubnetMap H D p _ β ∧ β = φ ∘ α

/-- The same net, indexed by H, is a Moore–Smith subnet of both nets. -/
def net_common_mooreSmith_refinement : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (a : Net D X) (φ : E → D), EventuallyCofinal φ →
    ∃ (H : Type (max v w)) (p : Preorder H),
      Nonempty H ∧ @IsDirectedOrder H p.toLE ∧
      ∃ (α : H → E) (β : H → D),
        @SubnetMap H E p _ α ∧ @SubnetMap H D p _ β ∧
        β = φ ∘ α ∧ subnet (subnet a φ) α = subnet a β

/-- Convergence of an eventually cofinal reindexing forces clustering
of the original net, with no separation assumption on the space. -/
def clusters_of_eventual_subnet : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (t : TopologicalSpace X) (a : Net D X) (φ : E → D) (x : X),
    EventuallyCofinal φ → Converges t (subnet a φ) x → Clusters t a x

end Specs.D10Topology.Ch04.SubnetConventions
