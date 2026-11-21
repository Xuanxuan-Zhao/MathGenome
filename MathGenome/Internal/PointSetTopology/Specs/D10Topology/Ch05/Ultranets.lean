import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Ultrafilters
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.FinerFilterSubnet

/-! Independent statements for the ultranet definition in d10:05:ultrafilter
and the two ultranet assertions of d10:05:ultranet. Nonempty directed
preorders are explicit in both the original and the subnet index data.
No topology or separation hypothesis is needed. -/

open Set Filter
universe u v
namespace Specs.D10Topology.Ch05.Ultranets
open Ch04.NetsAndSubnets Ch04.NetFilterBridge

/-- The eventual-membership alternative. As for the upstream net predicates,
the predicate only needs a preorder; all net theorems require a nonempty
directed index preorder. -/
def IsUltranet {D : Type v} {X : Type u} [Preorder D] (a : D → X) : Prop :=
  ∀ A : Set X, EventuallyIn a A ∨ EventuallyIn a Aᶜ

def isUltranetType :=
  {D : Type v} → {X : Type u} → [Preorder D] → (D → X) → Prop

def isUltranetValue : isUltranetType.{u, v} :=
  fun {D} {X} [Preorder D] => @IsUltranet D X _

/-- The tail filter is proper under precisely the standing net hypotheses. -/
def ultranet_iff_tailFilter_ultrafilter : Prop :=
  ∀ {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X),
    IsUltranet a ↔ Ultrafilters.IsUltrafilter (TailFilter a)

/-- An actual Moore–Smith reindexing: the new index preorder is nonempty
and directed, and the map is monotone with cofinal range. -/
def exists_ultranet_subnet : Prop :=
  ∀ {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X),
    ∃ (E : Type (max u v)) (p : Preorder E),
      Nonempty E ∧ @IsDirectedOrder E p.toLE ∧
      ∃ φ : E → D, @SubnetMap E D p _ φ ∧ @IsUltranet E X p (subnet a φ)

end Specs.D10Topology.Ch05.Ultranets
