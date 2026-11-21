import Mathlib.Topology.Bases
import Mathlib.Logic.Relation

/-! The countable plaque-chain cover used in M08.03 (paper.tex, 1660).
The ambient space and transverse index type need not be second countable or
countable. All topology assumptions refer to the original plaque subtypes. -/
set_option autoImplicit false

namespace Specs.SmoothManifolds.Ch08.PlaqueChainCountability
open Set
universe u v w

/-- Even an empty initial plaque contributes its own index by reflexivity. -/
def reachable_countableType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {I : Type v} [Countable I]
    {Z : Type w} (P : I × Z → Set X),
    (∀ a, SecondCountableTopology (P a)) →
    (∀ i, Pairwise (fun z z' => Disjoint (P (i, z)) (P (i, z')))) →
    (∀ a b, IsOpen (Subtype.val ⁻¹' P b : Set (P a))) →
    ∀ a, {b | Relation.ReflTransGen (fun c d => (P c ∩ P d).Nonempty) a b}.Countable

/-- A countable set of original plaques covers exactly the point-chain class;
each chosen plaque is entirely contained in that class. -/
def point_class_coverType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {I : Type v} [Countable I]
    {Z : Type w} (P : I × Z → Set X),
    (∀ a, SecondCountableTopology (P a)) →
    (∀ i, Pairwise (fun z z' => Disjoint (P (i, z)) (P (i, z')))) →
    (∀ a b, IsOpen (Subtype.val ⁻¹' P b : Set (P a))) →
    (∀ x, ∃ a, x ∈ P a) → ∀ p,
    ∃ S : Set (I × Z), S.Countable ∧
      (∀ a ∈ S, P a ⊆ {q | Relation.EqvGen (fun x y => ∃ b, x ∈ P b ∧ y ∈ P b) p q}) ∧
      {q | Relation.EqvGen (fun x y => ∃ b, x ∈ P b ∧ y ∈ P b) p q} = ⋃ a ∈ S, P a

end Specs.SmoothManifolds.Ch08.PlaqueChainCountability
