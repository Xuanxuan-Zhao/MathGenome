import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-! Independent statements for paper.tex, d10:13:evaluation-exponential.
All function-space continuity statements use the previously defined compact-open
subspace topology explicitly. LCH has the source meaning: one compact neighborhood
at each point, together with Hausdorffness. No condition is imposed on Y or Z.
-/

universe u v w

namespace Specs.D10Topology.Ch13.EvaluationParameter

open Specs.D10Topology.Ch13.FunctionTopologies
open Specs.D10Topology.Ch11.LocalCompactConventions

/-- The curried map formed from continuous slices. -/
def parameterMap {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Z × X → Y) (hs : ∀ z : Z, Continuous (fun x : X => h (z, x))) :
    Z → ContinuousMaps X Y :=
  fun z => ⟨fun x => h (z, x), hs z⟩

def parameterMapType :=
  {X : Type u} → {Y : Type v} → {Z : Type w} →
    [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace Z] →
    (h : Z × X → Y) → (∀ z : Z, Continuous (fun x : X => h (z, x))) →
    Z → ContinuousMaps X Y

def parameterMapValue : parameterMapType := @parameterMap

def joint_evaluation_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    LCH X →
    letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
    Continuous (fun p : ContinuousMaps X Y × X => p.1 p.2)

def continuous_slices : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Z × X → Y), Continuous h →
    ∀ z : Z, Continuous (fun x : X => h (z, x))

/-- Currying needs no local compactness or separation hypothesis. -/
def parameter_map_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Z × X → Y) (hs : ∀ z : Z, Continuous (fun x : X => h (z, x))),
    Continuous h →
    letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
    Continuous (parameterMap h hs)

/-- The converse applies to every family of continuous maps on an LCH domain. -/
def associated_map_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z],
    LCH X → ∀ F : Z → ContinuousMaps X Y,
    (letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
     Continuous F) →
    Continuous (fun p : Z × X => F p.1 p.2)

def parameter_criterion : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z],
    LCH X → ∀ (h : Z × X → Y)
      (hs : ∀ z : Z, Continuous (fun x : X => h (z, x))),
    Continuous h ↔
    (letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
     Continuous (parameterMap h hs))

end Specs.D10Topology.Ch13.EvaluationParameter
