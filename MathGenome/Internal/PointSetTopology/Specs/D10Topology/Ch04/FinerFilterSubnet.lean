import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetFilterBridge

/-! Independent statement of paper.tex, d10:04:finer-subnet.
The witness is a Moore–Smith subnet on a nonempty directed preorder.
Filter inclusion uses the paper's family-inclusion convention. The same
subnet works for every topology and every limit of the finer filter. -/

universe u v
namespace Specs.D10Topology.Ch04.FinerFilterSubnet

def finer_filter_subnet : Prop :=
  ∀ {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (a : D → X) (G : Filter X) [G.NeBot],
    ProperFilters.FilterFiner G (NetFilterBridge.TailFilter a) →
    ∃ (E : Type (max u v)) (p : Preorder E),
      Nonempty E ∧ @IsDirectedOrder E p.toLE ∧
      ∃ φ : E → D, @NetsAndSubnets.SubnetMap E D p _ φ ∧
        (@NetFilterBridge.TailFilter E X p (NetsAndSubnets.subnet a φ)).NeBot ∧
        ProperFilters.FilterFiner
          (@NetFilterBridge.TailFilter E X p (NetsAndSubnets.subnet a φ)) G ∧
        ∀ (t : TopologicalSpace X) (x₀ : X),
          @ProperFilters.FilterConverges X t G x₀ →
          @NetsAndSubnets.Converges E X p t (NetsAndSubnets.subnet a φ) x₀

end Specs.D10Topology.Ch04.FinerFilterSubnet
