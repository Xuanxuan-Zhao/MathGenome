import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Basic

/-! Independent statements for paper.tex, d10:18:sierpinski and d10:18:discrete,
also covering the uncountable discrete metric example in d10:08:implication-scope.
Bool is the already shared two-point set, with false = 0 and true = 1.
The metric statements quantify over every metric with distinct-point distance
exactly 1. In particular they concern its actual uniformity, not merely a
compatible discrete topology. Local compactness means a compact neighborhood.
-/

open Set Filter TopologicalSpace
open scoped Topology
universe u

namespace Specs.D10Topology.Ch18.FiniteDiscreteExamples

def sierpinski_properties : Prop :=
  letI := _root_.D10Topology.Ch02.CharacteristicMaps.topology
  T0Space Bool ∧ CompactSpace Bool ∧ PreconnectedSpace Bool ∧
    ¬ T1Space Bool ∧ ¬ T2Space Bool

def sierpinski_constant_sequence : Prop :=
  ∀ x : Bool, Tendsto (fun _ : ℕ => true) atTop
    (@nhds Bool _root_.D10Topology.Ch02.CharacteristicMaps.topology x)

def infinite_unit_discrete_properties : Prop :=
  ∀ {X : Type u} [Infinite X] [d : MetricSpace X],
    (∀ x y : X, x ≠ y → dist x y = 1) →
    (∀ x y : X, dist x y ≤ 1) ∧ CompleteSpace X ∧
      ¬ CompactSpace X ∧ ¬ TotallyBounded (univ : Set X)

def uncountable_unit_discrete_properties : Prop :=
  ∀ {X : Type u} [Uncountable X] [d : MetricSpace X],
    (∀ x y : X, x ≠ y → dist x y = 1) →
    (∀ x : X, ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x) ∧
      FirstCountableTopology X ∧ ¬ SeparableSpace X ∧
        ¬ SecondCountableTopology X ∧ ¬ LindelofSpace X

end Specs.D10Topology.Ch18.FiniteDiscreteExamples
