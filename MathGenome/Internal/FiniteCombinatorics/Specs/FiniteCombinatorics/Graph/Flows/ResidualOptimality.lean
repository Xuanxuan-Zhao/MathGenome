import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Augmentation

/-! Independent specification for the reachable-cut assertion of
`p204:residual-path` and the residual-optimality assertion of `p204:W47`.
All capacities and loads are real, and original tagged arc identities are retained.
No attainment or termination hypothesis is used. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows.ResidualOptimalitySpec
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Exactly the vertices reachable by a finite positive-residual walk from s. -/
def reachableSet (N : Network V A) (f : A → ℝ) : Set V :=
  {x | Directed.Spec.reachable (ResidualSpec.graph N f) N.source x}

set_option linter.checkUnivs false in
def reachableSetType :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
    Network V A → (A → ℝ) → Set V

/-- The exact reachable set is a cut, with all crossing loads characterized,
and its capacity is the signed flow value. -/
def reachable_cut : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    ¬ Nonempty (Walk (ResidualSpec.graph N f) N.source N.sink) →
    Spec.isCut N (reachableSet N f) ∧
    (∀ a ∈ Spec.outgoing N (reachableSet N f), f a = N.capacity a) ∧
    (∀ a ∈ Spec.incoming N (reachableSet N f), f a = 0) ∧
    Spec.cutCapacity N (reachableSet N f) = Spec.value N f

/-- The same certificate under the source's no vertex-simple path formulation. -/
def reachable_cut_of_no_path : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    ¬ Nonempty (Directed.Spec.path (ResidualSpec.graph N f) N.source N.sink) →
    Spec.isCut N (reachableSet N f) ∧
    (∀ a ∈ Spec.outgoing N (reachableSet N f), f a = N.capacity a) ∧
    (∀ a ∈ Spec.incoming N (reachableSet N f), f a = 0) ∧
    Spec.cutCapacity N (reachableSet N f) = Spec.value N f

/-- Maximum among every real feasible flow iff there is no residual walk. -/
def maximum_iff_no_walk : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    (Spec.isMaximum N f ↔
      ¬ Nonempty (Walk (ResidualSpec.graph N f) N.source N.sink))

/-- Maximum among every real feasible flow iff there is no simple residual path. -/
def maximum_iff_no_path : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    (Spec.isMaximum N f ↔
      ¬ Nonempty (Directed.Spec.path (ResidualSpec.graph N f) N.source N.sink))

end FiniteCombinatorics.Graph.Flows.ResidualOptimalitySpec
