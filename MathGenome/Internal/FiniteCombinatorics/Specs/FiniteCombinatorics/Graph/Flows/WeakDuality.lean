import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations

/-! Independent propositions for W45. Values are signed; original arc identities,
loops, and arbitrary incidences at the source and sink are retained. -/

open scoped BigOperators
universe u v
namespace FiniteCombinatorics.Graph.Flows.Spec

/-- Conservation summed over an s–t cut gives its signed net outgoing load. -/
def value_eq_cut_net : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (S : Set V),
    feasible N f → isCut N S →
    value N f = (∑ a ∈ outgoing N S, f a) - ∑ a ∈ incoming N S, f a

/-- Every feasible signed flow value is bounded above by every cut capacity. -/
def weak_duality : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (S : Set V),
    feasible N f → isCut N S → value N f ≤ cutCapacity N S

/-- Equality holds precisely at saturated outgoing and zero incoming cut arcs. -/
def value_eq_cutCapacity_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (S : Set V),
    feasible N f → isCut N S →
    (value N f = cutCapacity N S ↔
      (∀ a ∈ outgoing N S, f a = N.capacity a) ∧
      (∀ a ∈ incoming N S, f a = 0))

end FiniteCombinatorics.Graph.Flows.Spec
