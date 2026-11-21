import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-! Independent statements for paper.tex, d10:15:smirnov.
Each local metric induces the inherited subspace topology. No common metric,
countability, nonemptiness or separation condition is built into local metrizability
or paracompactness. Hausdorffness is a separate hypothesis of the theorem. -/

universe u
namespace Specs.D10Topology.Ch15.Smirnov

open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch15.LocallyFiniteConventions

abbrev LocallyMetrizable (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    Metrizable (inferInstance : TopologicalSpace U)

def locallyMetrizableType := (X : Type u) → [TopologicalSpace X] → Prop

def locallyMetrizableValue : locallyMetrizableType := fun X _ =>
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    Metrizable (inferInstance : TopologicalSpace U)

def smirnov : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    T2Space X →
      (Metrizable t ↔ Paracompact X ∧ LocallyMetrizable X)

end Specs.D10Topology.Ch15.Smirnov
