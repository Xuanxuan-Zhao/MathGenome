import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Constructions
import Mathlib.Data.PNat.Equiv

/-! Independent statements for `d10:10:urysohn-metrization`.
Regularity has no T₁ condition. The cube has the product of the usual
subspace topologies on [0,1], indexed by the positive natural numbers.
There is no nonemptiness or infinitude assumption on the space or its basis.
-/

open Topology
universe u

namespace Specs.D10Topology.Ch10.UrysohnMetrization

def urysohn_metrization : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    RegularSpace X → SecondCountableTopology X → T1Space X →
      (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ∧
        Specs.D10Topology.Ch09.MetricConventions.Metrizable t

def urysohn_metrization_t0 : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    RegularSpace X → SecondCountableTopology X → T0Space X →
      (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ∧
        Specs.D10Topology.Ch09.MetricConventions.Metrizable t

def regular_separation_equivalence : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], RegularSpace X → (T0Space X ↔ T1Space X)

/-- The topology ⊤ is indiscrete in Lean's reverse topology order. -/
def indiscrete_two_point_counterexample : Prop :=
  @RegularSpace Bool ⊤ ∧ @SecondCountableTopology Bool ⊤ ∧
    ¬ Specs.D10Topology.Ch09.MetricConventions.Metrizable (⊤ : TopologicalSpace Bool)

end Specs.D10Topology.Ch10.UrysohnMetrization
