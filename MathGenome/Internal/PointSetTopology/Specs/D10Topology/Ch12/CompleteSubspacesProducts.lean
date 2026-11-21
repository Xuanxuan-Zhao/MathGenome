import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformSubspacesProducts

/-! Independent statements of paper.tex, `d10:12:complete-subspace-product`.
`Complete` quantifies over proper Cauchy filters, and `Separated` is the
diagonal-intersection condition from the canonical Chapter 12 conventions.
Subtypes and dependent products carry their induced uniform structures; their
topologies agree with the paper's constructions by the upstream interfaces.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch12.CompleteSubspacesProducts

open UniformConventions

/-- No separatedness is required for a closed subspace to inherit completeness. -/
def closed_subspace_complete : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X),
    Complete X → IsClosed A → Complete A

/-- Completeness of a subspace forces closedness in a separated ambient space. -/
def complete_subspace_closed : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X),
    Separated (X := X) → Complete A → IsClosed A

/-- Arbitrary products, including empty products and products with empty factors. -/
def complete_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)],
    (∀ i, Complete (X i)) → Complete (∀ i, X i)

/-- Nonemptiness belongs to the product, with no separation assumption. -/
def complete_factors_of_nonempty_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)],
    Nonempty (∀ i, X i) → Complete (∀ i, X i) → ∀ i, Complete (X i)

/-- Explicit empty-factor boundary; no completeness of the other factors. -/
def empty_factor_product_complete : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)]
    (i : I) [IsEmpty (X i)], Complete (∀ i, X i)

end Specs.D10Topology.Ch12.CompleteSubspacesProducts
