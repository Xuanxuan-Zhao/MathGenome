import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements for the permanence, boundedness, separability and
counterexample parts of paper.tex, d10:09:total-bounded-basics.
Subsets carry their restricted metric, so finite ball centers must belong to
the subset. No nonemptiness assumption is imposed on these results.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch09.TotalBoundedPermanence
open Specs.D10Topology.Ch09.MetricConventions

/-- Bridge between total boundedness of the restricted metric and of an
ambient subset. The left-hand side requires centers in the subtype. -/
def totallyBounded_subspace_iff : Prop :=
  ∀ {X : Type u} [d : MetricSpace X] (A : Set X),
    TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace ↔
      _root_.TotallyBounded A

def totallyBounded_subspace : Prop :=
  ∀ {X : Type u} [d : MetricSpace X] (A : Set X),
    TotallyBounded d.toPseudoMetricSpace →
      TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace

def totallyBounded_closure : Prop :=
  ∀ {X : Type u} [d : MetricSpace X] (A : Set X),
    TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace →
      TotallyBounded (inferInstance : MetricSpace (closure A)).toPseudoMetricSpace

def totallyBounded_image : Prop :=
  ∀ {X : Type u} {Y : Type v} [d : MetricSpace X] [e : MetricSpace Y]
    (f : X → Y) (A : Set X),
    UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f →
    TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace →
      TotallyBounded (inferInstance : MetricSpace (f '' A)).toPseudoMetricSpace

def totallyBounded_bounded : Prop :=
  ∀ {X : Type u} [d : MetricSpace X], TotallyBounded d.toPseudoMetricSpace →
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x y : X, distance d.toPseudoMetricSpace x y ≤ R

def totallyBounded_separable : Prop :=
  ∀ {X : Type u} [d : MetricSpace X], TotallyBounded d.toPseudoMetricSpace →
    Specs.D10Topology.Ch08.CountabilityConventions.separableValue
      (metricTopology d.toPseudoMetricSpace)

def totallyBounded_countable_dense : Prop :=
  ∀ {X : Type u} [d : MetricSpace X], TotallyBounded d.toPseudoMetricSpace →
    ∃ D : Set X, D.Countable ∧ closure D = univ

/-- The metric exists on every underlying set, without decidable equality
or a preselected topology as an additional hypothesis. -/
def unit_discrete_metric_exists : Prop :=
  ∀ (X : Type u), ∃ d : MetricSpace X,
    ∀ x y : X, x ≠ y → distance d.toPseudoMetricSpace x y = 1

/-- This applies to every metric having exactly the indicated distances. -/
def infinite_unit_discrete_not_totallyBounded : Prop :=
  ∀ {X : Type u} [Infinite X] [d : MetricSpace X],
    (∀ x y : X, x ≠ y → distance d.toPseudoMetricSpace x y = 1) →
    (∀ x y : X, distance d.toPseudoMetricSpace x y ≤ 1) ∧
      ¬ TotallyBounded d.toPseudoMetricSpace

def infinite_unit_discrete_counterexample : Prop :=
  ∀ (X : Type u) [Infinite X], ∃ d : MetricSpace X,
    (∀ x y : X, x ≠ y → distance d.toPseudoMetricSpace x y = 1) ∧
    (∀ x y : X, distance d.toPseudoMetricSpace x y ≤ 1) ∧
      ¬ TotallyBounded d.toPseudoMetricSpace

end Specs.D10Topology.Ch09.TotalBoundedPermanence
