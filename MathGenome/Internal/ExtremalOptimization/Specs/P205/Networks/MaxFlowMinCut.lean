import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualFoundation

/-! Independent statements for paper.tex, Theorem p205:W36 (8.1).
`Network` retains arbitrary labelled arcs, finite real nonnegative capacities,
and distinct source and sink. Its feasibility is bounds plus conservation away
from those vertices; its value is signed net outflow at the source.
The residual certificate uses precisely the upstream bounded residual graph.
No loop deletion, nonempty arc type, or restriction on terminal incidences is used. -/

open scoped BigOperators Classical
universe u v
namespace P205.Networks.FlowCutSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows

/-- All vertices reachable from the source in the zero-lower-bound residual graph. -/
def reachableSet {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) : Set V :=
  {x | Nonempty (Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) N.source x)}

set_option linter.checkUnivs false in
def reachableSetType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Network V A → (A → ℝ) → Set V

/-- The signed flow across every source–sink cut equals the flow value. -/
def flow_cut_identity : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (S : Set V), N.Feasible f → N.IsCut S →
    N.value f = BoundedSpec.arcSum f (BoundedSpec.outgoing N.graph S) -
      BoundedSpec.arcSum f (BoundedSpec.incoming N.graph S)

/-- Weak duality is for every feasible flow, including those with negative value. -/
def flow_cut_bound : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (S : Set V), N.Feasible f → N.IsCut S →
    N.value f ≤ BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S)

/-- Equality certifies maximum flow and minimum cut among all real flows and cuts. -/
def flow_cut_optimality : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (S : Set V), N.Feasible f → N.IsCut S →
    N.value f = BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) →
    N.IsMaximum f ∧ ∀ T : Set V, N.IsCut T →
      BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) ≤
      BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph T)

/-- Existence for arbitrary finite real nonnegative capacities. -/
def max_flow_min_cut : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A] (N : Network V A),
    ∃ (f : A → ℝ) (S : Set V), N.Feasible f ∧ N.IsCut S ∧
      (∀ g : A → ℝ, N.Feasible g → N.value g ≤ N.value f) ∧
      (∀ T : Set V, N.IsCut T →
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) ≤
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph T)) ∧
      N.value f = BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S)

/-- Integer capacities give an integral maximizer among all feasible real flows.
Integer witnesses, rather than natural-capacity hypotheses, express the source. -/
def integral_max_flow_min_cut : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A] (N : Network V A),
    (∀ a, ∃ z : ℤ, N.capacity a = (z : ℝ)) →
    ∃ (f : A → ℝ) (S : Set V), N.Feasible f ∧ N.IsCut S ∧
      (∀ g : A → ℝ, N.Feasible g → N.value g ≤ N.value f) ∧
      (∀ T : Set V, N.IsCut T →
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) ≤
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph T)) ∧
      N.value f = BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) ∧
      ∀ a, ∃ z : ℤ, f a = (z : ℝ)

/-- No residual walk gives the actual reachable cut, saturated outgoing arcs,
zero incoming loads, equal value, and both optimality assertions. -/
def residual_reachable_cut : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), N.Feasible f →
    ¬ Nonempty (Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f)
      N.source N.sink) →
    N.IsCut (reachableSet N f) ∧
      (∀ a ∈ BoundedSpec.outgoing N.graph (reachableSet N f), f a = N.capacity a) ∧
      (∀ a ∈ BoundedSpec.incoming N.graph (reachableSet N f), f a = 0) ∧
      N.value f = BoundedSpec.arcSum N.capacity
        (BoundedSpec.outgoing N.graph (reachableSet N f)) ∧
      N.IsMaximum f ∧ ∀ T : Set V, N.IsCut T →
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph (reachableSet N f)) ≤
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph T)

/-- The algorithm may use absence of a vertex-simple path instead of a walk. -/
def residual_reachable_cut_of_no_path : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), N.Feasible f →
    ¬ Nonempty (Path (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f)
      N.source N.sink) →
    N.IsCut (reachableSet N f) ∧
      (∀ a ∈ BoundedSpec.outgoing N.graph (reachableSet N f), f a = N.capacity a) ∧
      (∀ a ∈ BoundedSpec.incoming N.graph (reachableSet N f), f a = 0) ∧
      N.value f = BoundedSpec.arcSum N.capacity
        (BoundedSpec.outgoing N.graph (reachableSet N f)) ∧
      N.IsMaximum f ∧ ∀ T : Set V, N.IsCut T →
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph (reachableSet N f)) ≤
        BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph T)

end P205.Networks.FlowCutSpec
