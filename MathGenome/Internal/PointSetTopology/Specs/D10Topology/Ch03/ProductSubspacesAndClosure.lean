import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.NhdsWithin

/-! Independent full statements for `d10:03:product-subspaces` and
`d10:03:product-closure`. The product topology is the initial topology
specified upstream, not the box topology. Subsets use canonical subtypes.
No inhabitedness, finiteness or separation assumptions are imposed. -/

open Set Topology
universe u v w z

namespace Specs.D10Topology.Ch03.ProductSubspacesAndClosure
open Products

/-- Equality with the topology pulled back by the natural inclusion. -/
def product_subspace_topology : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (A : ∀ i, Set (X i)),
    productTopologyValue (fun i => (tX i).induced (Subtype.val : A i → X i)) =
      (productTopologyValue tX).induced (fun a i => (a i).val)

/-- The natural inclusion really has the rectangle as its image. -/
def product_subspace_range : Prop :=
  ∀ {I : Type u} {X : I → Type v} (A : ∀ i, Set (X i)),
    range (fun (a : ∀ i, A i) i => (a i).val) = univ.pi A

def product_embeddings : Prop :=
  ∀ {I : Type u} {A : I → Type v} {X : I → Type w}
    (tA : ∀ i, TopologicalSpace (A i)) (tX : ∀ i, TopologicalSpace (X i))
    (e : ∀ i, A i → X i),
    (∀ i, @IsEmbedding _ _ (tA i) (tX i) (e i)) →
      @IsEmbedding _ _ (productTopologyValue tA) (productTopologyValue tX)
        (fun a i => e i (a i))

/-- Any bijection of coordinate indices gives the canonical homeomorphism. -/
def product_reindex : Prop :=
  ∀ {I : Type u} {J : Type v} {X : J → Type w}
    (tX : ∀ j, TopologicalSpace (X j)) (e : I ≃ J),
    ∃ h : @Homeomorph (∀ i, X (e i)) (∀ j, X j)
      (productTopologyValue (fun i => tX (e i))) (productTopologyValue tX),
      (@Homeomorph.toEquiv _ _ (productTopologyValue (fun i => tX (e i))) (productTopologyValue tX) h) = Equiv.piCongrLeft X e

/-- Flattening/regrouping an arbitrary dependent family, including empty blocks. -/
def product_regroup : Prop :=
  ∀ {I : Type u} {J : I → Type v} {X : ∀ i, J i → Type w}
    (tX : ∀ i j, TopologicalSpace (X i j)),
    ∃ h : @Homeomorph (∀ p : Sigma J, X p.1 p.2) (∀ i j, X i j)
      (productTopologyValue (fun p : Sigma J => tX p.1 p.2))
      (productTopologyValue (fun i => productTopologyValue (tX i))),
      (@Homeomorph.toEquiv _ _ (productTopologyValue (fun p : Sigma J => tX p.1 p.2))
        (productTopologyValue (fun i => productTopologyValue (tX i))) h) = Equiv.piCurry X

/-- Grouping the coordinates along the fibers of any map of index sets.
This explicitly includes arbitrary partitions of an existing family. -/
def product_group_fibers : Prop :=
  ∀ {I : Type u} {J : Type v} {X : I → Type w}
    (tX : ∀ i, TopologicalSpace (X i)) (q : I → J),
    ∃ h : @Homeomorph (∀ i, X i) (∀ j, ∀ i : {i // q i = j}, X i.val)
      (productTopologyValue tX)
      (productTopologyValue (fun j => productTopologyValue
        (fun i : {i // q i = j} => tX i.val))),
      (@Homeomorph.toEquiv _ _ (productTopologyValue tX)
        (productTopologyValue (fun j => productTopologyValue (fun i : {i // q i = j} => tX i.val))) h) = @Equiv.piCongrFiberwise I J X
        (fun j => ∀ i : {i // q i = j}, X i.val) q (fun _ => Equiv.refl _)

def closure_product_rectangle : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (A : ∀ i, Set (X i)),
    @closure _ (productTopologyValue tX) (univ.pi A) =
      univ.pi (fun i => @closure _ (tX i) (A i))

def dense_product_rectangle : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (A : ∀ i, Set (X i)), (∀ i, @Dense _ (tX i) (A i)) →
      @Dense _ (productTopologyValue tX) (univ.pi A)

/-- Direct closedness by the intersection of coordinate inverse images. -/
def closed_product_rectangle : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (A : ∀ i, Set (X i)), (∀ i, IsClosed[tX i] (A i)) →
      IsClosed[productTopologyValue tX] (univ.pi A)

end Specs.D10Topology.Ch03.ProductSubspacesAndClosure
