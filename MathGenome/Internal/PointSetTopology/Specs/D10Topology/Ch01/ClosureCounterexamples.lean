import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ClosureCalculus
import Mathlib.Topology.Algebra.Ring.Real

/-! Independent proposition types for paper.tex, d10:01:closure-cautions.
The real topology is the usual one. In the two-point example the topology
is explicitly indiscrete. Neighborhoods use the upstream open-witness
definition and are not required to be open. -/

open Set
open scoped Topology
universe u

namespace Specs.D10Topology.Ch01.ClosureCounterexamples
open _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods

def reciprocal_singletons_counterexample : Prop :=
  (⋃ (n : ℕ) (_ : 1 ≤ n), closure ({1 / (n : ℝ)} : Set ℝ)) =
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = 1 / (n : ℝ)} ∧
    (0 : ℝ) ∈ closure (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) ∧
    (0 : ℝ) ∉ (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) ∧
    closure (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) ≠
      (⋃ (n : ℕ) (_ : 1 ≤ n), closure ({1 / (n : ℝ)} : Set ℝ))

def interval_intersection_counterexample : Prop :=
  Ioo (-1 : ℝ) 0 ∩ Ioo 0 1 = ∅ ∧
    (0 : ℝ) ∈ closure (Ioo (-1 : ℝ) 0) ∩ closure (Ioo (0 : ℝ) 1) ∧
    closure (Ioo (-1 : ℝ) 0 ∩ Ioo 0 1) ≠
      closure (Ioo (-1 : ℝ) 0) ∩ closure (Ioo (0 : ℝ) 1)

/-- Bool is the two-point set; top is Mathlib's indiscrete topology. -/
def indiscrete_accumulation_counterexample : Prop :=
  ∀ a b : Bool, a ≠ b →
    a ∈ @derivedSet Bool ⊤ {b} ∧
      (∀ N : Set Bool, Neighborhood ⊤ a N → (N ∩ ({b} \ {a})).Finite) ∧
      ¬ (∀ N : Set Bool, Neighborhood ⊤ a N → (N ∩ {b}).Infinite)

/-- The reverse implication has no separation hypothesis. -/
def accumulation_of_infinite_punctured_neighborhoods : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X),
    (∀ N : Set X, Neighborhood t x N → (N ∩ (A \ {x})).Infinite) →
      x ∈ derivedSet A

/-- This also needs no separation hypothesis: removing one point preserves infinitude. -/
def accumulation_of_infinite_neighborhoods : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X),
    (∀ N : Set X, Neighborhood t x N → (N ∩ A).Infinite) →
      x ∈ derivedSet A

def accumulation_iff_infinite_punctured_neighborhoods : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] [T1Space X] (A : Set X) (x : X),
    x ∈ derivedSet A ↔
      ∀ N : Set X, Neighborhood t x N → (N ∩ (A \ {x})).Infinite

def accumulation_iff_infinite_neighborhoods : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] [T1Space X] (A : Set X) (x : X),
    x ∈ derivedSet A ↔
      ∀ N : Set X, Neighborhood t x N → (N ∩ A).Infinite

end Specs.D10Topology.Ch01.ClosureCounterexamples
