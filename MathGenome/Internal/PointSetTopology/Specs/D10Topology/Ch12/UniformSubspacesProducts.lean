import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformTopology
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import Mathlib.Topology.UniformSpace.Pi

/-! Independent statements for paper.tex, `d10:12:subspace-product`.
Subsets and dependent products carry their canonical uniform structures. A
relative relation is expressed by inverse image under the subtype inclusion;
the image formula below identifies it with the literal ambient intersection.
No nonemptiness or separation is imposed on either base construction.
-/

open Set Filter
open scoped Uniformity Topology
universe u v w

namespace Specs.D10Topology.Ch12.UniformSubspacesProducts

open UniformConventions

def restrictedEntourage {X : Type u} (A : Set X) (U : Set (X × X)) : Set (A × A) :=
  (Prod.map Subtype.val Subtype.val) ⁻¹' U

def restrictedEntourageType := {X : Type u} → (A : Set X) → Set (X × X) → Set (A × A)
def restrictedEntourageValue : restrictedEntourageType := @restrictedEntourage

/-- The same finite coordinate tests as in the manuscript; only finite F are
used in the base, and the empty F gives the universal relation. -/
def productEntourage {I : Type u} {X : I → Type v}
    (F : Set I) (U : ∀ i, Set (X i × X i)) : Set ((∀ i, X i) × (∀ i, X i)) :=
  ⋂ i ∈ F, (fun p => (p.1 i, p.2 i)) ⁻¹' U i

def productEntourageType := {I : Type u} → {X : I → Type v} →
  Set I → (∀ i, Set (X i × X i)) → Set ((∀ i, X i) × (∀ i, X i))
def productEntourageValue : productEntourageType := @productEntourage

def restrictedEntourage_image : Prop :=
  ∀ {X : Type u} (A : Set X) (U : Set (X × X)),
    (Prod.map Subtype.val Subtype.val) '' restrictedEntourage A U = U ∩ (A ×ˢ A)

def subspace_uniformity_basis : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X),
    (𝓤 A).HasBasis (fun U : Set (X × X) => U ∈ 𝓤 X) (restrictedEntourage A)

def subspace_uniformity_mem : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X) (W : Set (A × A)),
    W ∈ 𝓤 A ↔ ∃ U ∈ 𝓤 X, restrictedEntourage A U ⊆ W

def subspace_uniform_topology : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X),
    (UniformTopology.uniformTopology (X := A)) =
      TopologicalSpace.induced (Subtype.val : A → X) UniformTopology.uniformTopology

def restrictedEntourage_ball : Prop :=
  ∀ {X : Type u} (A : Set X) (U : Set (X × X)) (a : A),
    entourageBall (restrictedEntourage A U) a =
      (Subtype.val : A → X) ⁻¹' entourageBall U a.val

def product_uniformity_basis : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)],
    (𝓤 (∀ i, X i)).HasBasis
      (fun b : Set I × (∀ i, Set (X i × X i)) =>
        b.1.Finite ∧ ∀ i ∈ b.1, b.2 i ∈ 𝓤 (X i))
      (fun b => productEntourage b.1 b.2)

def product_uniformity_mem : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)]
    (W : Set ((∀ i, X i) × (∀ i, X i))),
    W ∈ 𝓤 (∀ i, X i) ↔
      ∃ (F : Set I) (U : ∀ i, Set (X i × X i)),
        F.Finite ∧ (∀ i ∈ F, U i ∈ 𝓤 (X i)) ∧ productEntourage F U ⊆ W

def productEntourage_empty : Prop :=
  ∀ {I : Type u} {X : I → Type v} (U : ∀ i, Set (X i × X i)),
    productEntourage ∅ U = univ

def productEntourage_ball : Prop :=
  ∀ {I : Type u} {X : I → Type v} (F : Set I)
    (U : ∀ i, Set (X i × X i)) (x : ∀ i, X i),
    entourageBall (productEntourage F U) x = F.pi (fun i => entourageBall (U i) (x i))

def product_uniform_topology : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)],
    UniformTopology.uniformTopology (X := ∀ i, X i) =
      Specs.D10Topology.Ch03.Products.productTopologyValue
        (fun i => UniformTopology.uniformTopology (X := X i))

def entourageContinuous_product_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} {Z : Type w}
    [∀ i, UniformSpace (X i)] [UniformSpace Z] (f : Z → ∀ i, X i),
    EntourageContinuous f ↔ ∀ i, EntourageContinuous (fun z => f z i)

def separated_subspace : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X),
    Separated (X := X) → Separated (X := A)

def separated_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)],
    (∀ i, Separated (X := X i)) → Separated (X := ∀ i, X i)

def empty_subspace_uniformity : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X) [IsEmpty A],
    (𝓤 A).sets = {∅} ∧ ∀ uA vA : UniformSpace A, uA = vA

def empty_factor_product_uniformity : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)]
    (i : I) [IsEmpty (X i)],
    IsEmpty (∀ i, X i) ∧ (𝓤 (∀ i, X i)).sets = {∅} ∧
      ∀ uP vP : UniformSpace (∀ i, X i), uP = vP

def zero_factor_product_uniformity : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)] [IsEmpty I],
    (∃! _x : (∀ i, X i), True) ∧
      ∀ uP vP : UniformSpace (∀ i, X i), uP = vP

end Specs.D10Topology.Ch12.UniformSubspacesProducts
