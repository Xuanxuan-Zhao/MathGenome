import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.Foundations
import Mathlib.Data.Set.Basic

/-!
Independent specification for W44 and the following divergence/loop paragraph.
Capacities are finite real numbers; values are signed. All walks, paths, cycles,
and divergences use the shared original-arc directed graph interface.
No exclusion of arcs entering the source or leaving the sink is imposed.
-/

open scoped BigOperators
universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed

/-- A network retains the original finite arc identities, including loops. -/
structure Network (V : Type u) (A : Type v) [Fintype V] [Fintype A] where
  graph : Digraph V A
  capacity : A → ℝ
  capacity_nonneg : ∀ a, 0 ≤ capacity a
  source : V
  sink : V
  source_ne_sink : source ≠ sink

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Original arcs retained by actual deletion of all loops. -/
def Network.NonloopArc (N : Network V A) :=
  {a : A // N.graph.tail a ≠ N.graph.head a}

noncomputable instance (N : Network V A) : Fintype N.NonloopArc := by
  classical
  unfold Network.NonloopArc
  infer_instance

namespace Spec

def feasible (N : Network V A) (f : A → ℝ) : Prop :=
  (∀ a, 0 ≤ f a ∧ f a ≤ N.capacity a) ∧
    ∀ x, x ≠ N.source → x ≠ N.sink → Directed.Spec.divergence N.graph f x = 0

def flow (N : Network V A) : Type v :=
  {f : A → ℝ // feasible N f}

noncomputable def value (N : Network V A) (f : A → ℝ) : ℝ :=
  Directed.Spec.divergence N.graph f N.source

def isCut (N : Network V A) (S : Set V) : Prop :=
  N.source ∈ S ∧ N.sink ∉ S

def cut (N : Network V A) : Type u :=
  {S : Set V // isCut N S}

noncomputable def outgoing (N : Network V A) (S : Set V) : Finset A :=
  by
  classical
  exact Finset.univ.filter (fun a => N.graph.tail a ∈ S ∧ N.graph.head a ∉ S)

noncomputable def incoming (N : Network V A) (S : Set V) : Finset A :=
  by
  classical
  exact Finset.univ.filter (fun a => N.graph.tail a ∉ S ∧ N.graph.head a ∈ S)

noncomputable def cutCapacity (N : Network V A) (S : Set V) : ℝ :=
  ∑ a ∈ outgoing N S, N.capacity a

def withoutLoops (N : Network V A) : Network V N.NonloopArc :=
  { graph := { tail := fun a => N.graph.tail a.val, head := fun a => N.graph.head a.val }
    capacity := fun a => N.capacity a.val
    capacity_nonneg := fun a => N.capacity_nonneg a.val
    source := N.source
    sink := N.sink
    source_ne_sink := N.source_ne_sink }

def restrictLoad (N : Network V A) (f : A → ℝ) : N.NonloopArc → ℝ :=
  fun a => f a.val

noncomputable def extendLoad (N : Network V A) (g : N.NonloopArc → ℝ) : A → ℝ :=
  by
  classical
  exact fun a => if h : N.graph.tail a ≠ N.graph.head a then g ⟨a, h⟩ else 0

def attainableValues (N : Network V A) : Set ℝ :=
  {r | ∃ f : A → ℝ, feasible N f ∧ value N f = r}

def isMaximum (N : Network V A) (f : A → ℝ) : Prop :=
  feasible N f ∧ ∀ g : A → ℝ, feasible N g → value N g ≤ value N f

section ExpectedTypes
set_option linter.unusedVariables false
set_option linter.checkUnivs false
def feasibleType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → (A → ℝ) → Prop
def flowType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Type v
def valueType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → (A → ℝ) → ℝ
def isCutType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Set V → Prop
def cutType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Type u
def outgoingType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Set V → Finset A
def incomingType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Set V → Finset A
def cutCapacityType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Set V → ℝ
def withoutLoopsType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (N : Network V A) → Network V N.NonloopArc
def restrictLoadType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (N : Network V A) → (A → ℝ) → N.NonloopArc → ℝ
def extendLoadType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (N : Network V A) → (N.NonloopArc → ℝ) → A → ℝ
def attainableValuesType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → Set ℝ
def isMaximumType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Network V A → (A → ℝ) → Prop
end ExpectedTypes

-- Full independently stated propositions for the foundation laws.
section ExpectedLaws
set_option linter.unusedVariables false

open scoped Classical in
def feasible_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ),
    feasible N f ↔
    (∀ a, 0 ≤ f a ∧ f a ≤ N.capacity a) ∧
    ∀ x, x ≠ N.source → x ≠ N.sink → Directed.Spec.divergence N.graph f x = 0

open scoped Classical in
def isCut_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (S : Set V),
    isCut N S ↔ N.source ∈ S ∧ N.sink ∉ S

open scoped Classical in
def value_eq : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ),
    value N f = Directed.Spec.divergence N.graph f N.source

open scoped Classical in
def mem_outgoing : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (S : Set V) (a : A),
    a ∈ outgoing N S ↔ N.graph.tail a ∈ S ∧ N.graph.head a ∉ S

open scoped Classical in
def mem_incoming : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (S : Set V) (a : A),
    a ∈ incoming N S ↔ N.graph.tail a ∉ S ∧ N.graph.head a ∈ S

open scoped Classical in
def cutCapacity_eq : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (S : Set V),
    cutCapacity N S = ∑ a ∈ outgoing N S, N.capacity a

open scoped Classical in
def sum_divergence : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ),
    ∑ x : V, Directed.Spec.divergence N.graph f x = 0

open scoped Classical in
def sink_divergence : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (hf : feasible N f),
    Directed.Spec.divergence N.graph f N.sink = -value N f

open scoped Classical in
def zero_feasible : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A),
    feasible N (fun _ => 0)

open scoped Classical in
def value_zero : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A),
    value N (fun _ => 0) = 0

open scoped Classical in
def loop_not_outgoing : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (a : A) (ha : N.graph.tail a = N.graph.head a) (S : Set V),
    a ∉ outgoing N S

open scoped Classical in
def loop_not_incoming : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (a : A) (ha : N.graph.tail a = N.graph.head a) (S : Set V),
    a ∉ incoming N S

open scoped Classical in
def divergence_eq_sum : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (x : V),
    Directed.Spec.divergence N.graph f x = ∑ a : A,
      ((if N.graph.tail a = x then f a else 0) -
       (if N.graph.head a = x then f a else 0))

open scoped Classical in
def withoutLoops_no_loop : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (a : N.NonloopArc),
    (withoutLoops N).graph.tail a ≠ (withoutLoops N).graph.head a

open scoped Classical in
def divergence_restrict : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (x : V),
    Directed.Spec.divergence (withoutLoops N).graph (restrictLoad N f) x = Directed.Spec.divergence N.graph f x

open scoped Classical in
def divergence_congr_nonloops : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f g : A → ℝ)
    (h : ∀ a, N.graph.tail a ≠ N.graph.head a → f a = g a) (x : V),
    Directed.Spec.divergence N.graph f x = Directed.Spec.divergence N.graph g x

open scoped Classical in
def restrict_extend : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (g : N.NonloopArc → ℝ),
    restrictLoad N (extendLoad N g) = g

open scoped Classical in
def extend_eq_zero_of_loop : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (g : N.NonloopArc → ℝ) (a : A)
    (ha : N.graph.tail a = N.graph.head a),
    extendLoad N g a = 0

open scoped Classical in
def divergence_extend : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (g : N.NonloopArc → ℝ) (x : V),
    Directed.Spec.divergence N.graph (extendLoad N g) x = Directed.Spec.divergence (withoutLoops N).graph g x

open scoped Classical in
def feasible_restrict : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (hf : feasible N f),
    feasible (withoutLoops N) (restrictLoad N f)

open scoped Classical in
def feasible_extend_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (g : N.NonloopArc → ℝ),
    feasible N (extendLoad N g) ↔ feasible (withoutLoops N) g

open scoped Classical in
def value_restrict : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ),
    value (withoutLoops N) (restrictLoad N f) = value N f

open scoped Classical in
def value_extend : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (g : N.NonloopArc → ℝ),
    value N (extendLoad N g) = value (withoutLoops N) g

open scoped Classical in
def cutCapacity_eq_sum : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (S : Set V),
    cutCapacity N S = ∑ a : A,
      if N.graph.tail a ∈ S ∧ N.graph.head a ∉ S then N.capacity a else 0

open scoped Classical in
def cutCapacity_withoutLoops : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (S : Set V),
    cutCapacity (withoutLoops N) S = cutCapacity N S

open scoped Classical in
def attainableValues_withoutLoops : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A),
    attainableValues (withoutLoops N) = attainableValues N

open scoped Classical in
def maximum_restrict_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (hf : feasible N f),
    isMaximum (withoutLoops N) (restrictLoad N f) ↔ isMaximum N f

open scoped Classical in
def maximum_extend_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (g : N.NonloopArc → ℝ),
    isMaximum N (extendLoad N g) ↔ isMaximum (withoutLoops N) g

end ExpectedLaws
end Spec
end FiniteCombinatorics.Graph.Flows
