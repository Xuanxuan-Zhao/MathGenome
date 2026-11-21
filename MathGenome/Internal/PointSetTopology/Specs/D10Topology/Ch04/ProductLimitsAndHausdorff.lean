import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetsAndSubnets
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProperFilters
import Mathlib.Topology.Separation.Hausdorff

/-! Independent statements of paper.tex, d10:04:product-convergence.
The product topology is the upstream initial topology, neighborhoods may be
nonopen, nets have nonempty directed preorders, and filters are proper.
No inhabitation of the spaces or factors is assumed. -/

open Set Filter
open scoped Topology
universe u v w
namespace Specs.D10Topology.Ch04.ProductLimitsAndHausdorff

/-- The paper's open-neighborhood separation convention. -/
def Hausdorff {X : Type u} (t : TopologicalSpace X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ U V : Set X,
    IsOpen[t] U ∧ IsOpen[t] V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V

def hausdorffType := {X : Type u} → TopologicalSpace X → Prop
def hausdorffValue : hausdorffType := @Hausdorff

def hausdorff_iff_t2 : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X), Hausdorff t ↔ @T2Space X t

def net_product_converges_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} {D : Type w}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (tX : ∀ i, TopologicalSpace (X i)) (a : D → ∀ i, X i) (x : ∀ i, X i),
    NetsAndSubnets.Converges (Ch03.Products.productTopologyValue tX) a x ↔
      ∀ i, NetsAndSubnets.Converges (tX i) (fun d => a d i) (x i)

def filter_product_converges_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (F : Filter (∀ i, X i)) [F.NeBot]
    (x : ∀ i, X i),
    @ProperFilters.FilterConverges _ (Ch03.Products.productTopologyValue tX) F x ↔
      ∀ i, @ProperFilters.FilterConverges _ (tX i)
        (ProperFilters.ImageFilter (Ch03.Products.projectionValue i) F) (x i)

def hausdorff_iff_unique_filter_limits : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X), Hausdorff t ↔
    ∀ (F : Filter X) [F.NeBot] (x y : X),
      @ProperFilters.FilterConverges X t F x →
      @ProperFilters.FilterConverges X t F y → x = y

/-- The free universe v allows arbitrarily large index types. Taking max u v
also includes the canonical pair-index net of every filter on X. -/
def hausdorff_iff_unique_net_limits : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X), Hausdorff t ↔
    ∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X) (x y : X),
      NetsAndSubnets.Converges t a x → NetsAndSubnets.Converges t a y → x = y

/-- Explicit uniqueness for nets with independently chosen space/index universes. -/
def net_limits_unique : Prop :=
  ∀ {X : Type u} {D : Type v} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (t : TopologicalSpace X), Hausdorff t → ∀ (a : D → X) (x y : X),
      NetsAndSubnets.Converges t a x → NetsAndSubnets.Converges t a y → x = y

end Specs.D10Topology.Ch04.ProductLimitsAndHausdorff
