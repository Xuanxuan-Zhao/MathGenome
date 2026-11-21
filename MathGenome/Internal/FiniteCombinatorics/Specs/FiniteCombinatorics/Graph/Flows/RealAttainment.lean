import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact

/-! Independent propositions for the real-flow attainment part of W46.
The topology on arc loads is the usual product topology on `A → ℝ`.
All networks use finite original arc identities and finite nonnegative real
capacities; no nonemptiness assumption on the arc type is imposed. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows.Spec

def feasible_nonempty : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A), Set.Nonempty {f : A → ℝ | feasible N f}

def isClosed_conservation : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A),
    IsClosed {f : A → ℝ | ∀ x, x ≠ N.source → x ≠ N.sink →
      FiniteCombinatorics.Directed.Spec.divergence N.graph f x = 0}

def isClosed_feasible : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A), IsClosed {f : A → ℝ | feasible N f}

def isCompact_feasible : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A), IsCompact {f : A → ℝ | feasible N f}

def continuous_value : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A), Continuous (value N)

def exists_maximum : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A), ∃ f : A → ℝ, isMaximum N f

end FiniteCombinatorics.Graph.Flows.Spec
