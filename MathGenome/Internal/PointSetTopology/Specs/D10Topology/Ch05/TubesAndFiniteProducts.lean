import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-!
Independent statements for `paper.tex` d10:05:tube and d10:05:finite-product.
Compactness is the upstream open-cover property. Binary products use the
canonical product topology; dependent products use the upstream initial
topology of the coordinate projections. No separation or nonemptiness
assumption is imposed. The last two statements make the empty cases explicit.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch05.TubesAndFiniteProducts

open Specs.D10Topology.Ch05.Compactness

def tube_lemma : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    CoverCompact K → ∀ (x : X) (W : Set (X × K)),
      IsOpen W → ({x} : Set X) ×ˢ (univ : Set K) ⊆ W →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ (univ : Set K) ⊆ W

def projection_closed : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    CoverCompact K → IsClosedMap (Prod.fst : X × K → X)

def compact_binary_product : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    CoverCompact X → CoverCompact K → CoverCompact (X × K)

def compact_finite_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} [Finite I]
    (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @CoverCompact (X i) (tX i)) →
      @CoverCompact (Ch03.Products.productValue X) (Ch03.Products.productTopologyValue tX)

def empty_product_compact : Prop :=
  ∀ {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)),
    (∃! _x : Ch03.Products.productValue X, True) ∧
      @CoverCompact (Ch03.Products.productValue X) (Ch03.Products.productTopologyValue tX)

def empty_factor_product_compact : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) [IsEmpty (X i)],
    IsEmpty (Ch03.Products.productValue X) ∧
      @CoverCompact (Ch03.Products.productValue X) (Ch03.Products.productTopologyValue tX)

end Specs.D10Topology.Ch05.TubesAndFiniteProducts
