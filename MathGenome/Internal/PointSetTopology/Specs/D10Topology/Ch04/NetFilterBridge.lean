import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetsAndSubnets
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProperFilters

/-! Independent statements for paper.tex, d10:04:filter-net.
The pair index has exactly the paper's reverse-inclusion preorder; its
point coordinate has no effect on the order. -/

open Set Filter
universe u v w
namespace Specs.D10Topology.Ch04.NetFilterBridge

def Tail {D : Type v} {X : Type u} [Preorder D] (a : D → X) (d : D) : Set X :=
  a '' Ici d

def TailFilter {D : Type v} {X : Type u} [Preorder D] (a : D → X) : Filter X :=
  Filter.generate (range (Tail a))

def FilterNetIndex {X : Type u} (F : Filter X) :=
  {p : Set X × X // p.1 ∈ F ∧ p.2 ∈ p.1}

instance filterNetIndexPreorder {X : Type u} (F : Filter X) :
    Preorder (FilterNetIndex F) where
  le p q := q.val.1 ⊆ p.val.1
  le_refl _ := Subset.rfl
  le_trans _ _ _ hpq hqr := hqr.trans hpq

def filterNet {X : Type u} (F : Filter X) : FilterNetIndex F → X :=
  fun p => p.val.2

def tailType := {D : Type v} → {X : Type u} → [Preorder D] →
  (D → X) → D → Set X
def tailValue : tailType.{u, v} := fun {D} {X} [Preorder D] => @Tail D X _
def tailFilterType := {D : Type v} → {X : Type u} → [Preorder D] →
  (D → X) → Filter X
def tailFilterValue : tailFilterType.{u, v} := fun {D} {X} [Preorder D] => @TailFilter D X _
def filterNetIndexType := {X : Type u} → Filter X → Type u
def filterNetIndexValue : filterNetIndexType := @FilterNetIndex
def filterNetType := {X : Type u} → (F : Filter X) → FilterNetIndex F → X
def filterNetValue : filterNetType := @filterNet

def tails_filterBase : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (a : D → X), ProperFilters.FilterBase (range (Tail a))

def tailFilter_mem : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (a : D → X) (A : Set X),
    A ∈ TailFilter a ↔ NetsAndSubnets.EventuallyIn a A

def tailFilter_proper : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (a : D → X), (TailFilter a).NeBot

def tailFilter_converges : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [t : TopologicalSpace X] (a : D → X) (x : X),
    ProperFilters.FilterConverges (TailFilter a) x ↔ NetsAndSubnets.Converges t a x

def tailFilter_clusters : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [t : TopologicalSpace X] (a : D → X) (x : X),
    ProperFilters.FilterClusters (TailFilter a) x ↔ NetsAndSubnets.Clusters t a x

def filterNetIndex_le_iff : Prop :=
  ∀ {X : Type u} (F : Filter X) (p q : FilterNetIndex F),
    p ≤ q ↔ q.val.1 ⊆ p.val.1

def filterNetIndex_nonempty : Prop :=
  ∀ {X : Type u} (F : Filter X) [F.NeBot], Nonempty (FilterNetIndex F)

def filterNetIndex_directed : Prop :=
  ∀ {X : Type u} (F : Filter X) [F.NeBot], IsDirectedOrder (FilterNetIndex F)

def filterNet_tail : Prop :=
  ∀ {X : Type u} (F : Filter X) (p : FilterNetIndex F),
    Tail (filterNet F) p = p.val.1

def filterNet_tailFilter : Prop :=
  ∀ {X : Type u} (F : Filter X) [F.NeBot], TailFilter (filterNet F) = F

def subnet_tailFilter_finer : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    [Preorder E] [Nonempty E] [IsDirectedOrder E]
    (a : D → X) (φ : E → D), NetsAndSubnets.SubnetMap φ →
    ProperFilters.FilterFiner (TailFilter (NetsAndSubnets.subnet a φ)) (TailFilter a)
      ∧ TailFilter (NetsAndSubnets.subnet a φ) ≤ TailFilter a

end Specs.D10Topology.Ch04.NetFilterBridge
