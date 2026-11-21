import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-! Independent statements for paper.tex, d10:15:nagata-smirnov.
Regularity excludes no additional points: T1 is a separate hypothesis.
The basis and its layers may be uncountable or empty. The converse requires
an actual finite-valued metric inducing the given topology.
-/

open Set TopologicalSpace
universe u

namespace Specs.D10Topology.Ch15.NagataSmirnov

open Specs.D10Topology.Ch15.LocallyFiniteConventions
open Specs.D10Topology.Ch09.MetricConventions

def metric_sigmaLocallyFinite_basis : Prop :=
  ∀ (X : Type u) [MetricSpace X],
    ∃ B : Set (Set X), IsTopologicalBasis B ∧
      SigmaLocallyFinite (fun b : B => (b : Set X))

def exists_compatibleMetric_of_sigmaLocallyFinite_basis : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)), IsTopologicalBasis B →
    SigmaLocallyFinite (fun b : B => (b : Set X)) →
    ∃ d : MetricSpace X, metricTopology d.toPseudoMetricSpace = t

def nagata_smirnov : Prop :=
  ∀ (X : Type u) (t : TopologicalSpace X),
    Metrizable t ↔ @RegularSpace X t ∧ @T1Space X t ∧
      ∃ B : Set (Set X), @IsTopologicalBasis X t B ∧
        @SigmaLocallyFinite X B t (fun b => (b : Set X))

end Specs.D10Topology.Ch15.NagataSmirnov
