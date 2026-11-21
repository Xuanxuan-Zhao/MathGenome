import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.NhdsSet

/-!
Independent specification of `paper.tex`, Definition `d13:18:attractor-definition`.

Stability refers to neighborhoods of the entire set. Attraction is pointwise
in the initial state and uses distance to the set, without selecting a limiting
point in it. Extended distance gives the empty set distance infinity; for the
nonempty sets in the source, `approachesSet_iff_distStatement` identifies this
with the usual real distance tending to zero. The ambient map's continuity is
included in `StableAttractor`; the auxiliary orbit predicates need no continuity.
The iterates and image-equality invariance are the canonical Chapter 15 objects.
-/

namespace Specs.D13Unified.Ch18.AttractorDefinition

universe u
open Filter Set
open scoped Topology
open Specs.D13Unified.Ch15.DiscreteDefinitions

def ApproachesSetType :=
  {X : Type u} → [MetricSpace X] → (X → X) → Set X → X → Prop

/-- The forward orbit approaches the set in distance. -/
def ApproachesSet : ApproachesSetType := fun F A x =>
  Tendsto (fun n : ℕ => Metric.infEDist (forwardOrbit F x n) A) atTop (𝓝 0)

def SetLyapunovStableType :=
  {X : Type u} → [MetricSpace X] → (X → X) → Set X → Prop

/-- Every neighborhood of the whole set contains all future iterates of
some neighborhood of that set, including the time-zero iterate. -/
def SetLyapunovStable : SetLyapunovStableType := fun F A =>
  ∀ V ∈ 𝓝ˢ A, ∃ U ∈ 𝓝ˢ A, ∀ x ∈ U, ∀ n : ℕ, forwardOrbit F x n ∈ V

def AttractsSetNeighborhoodType :=
  {X : Type u} → [MetricSpace X] → (X → X) → Set X → Prop

/-- One neighborhood of the whole set is attracted, pointwise in x. -/
def AttractsSetNeighborhood : AttractsSetNeighborhoodType := fun F A =>
  ∃ U ∈ 𝓝ˢ A, ∀ x ∈ U, ApproachesSet F A x

def basinType :=
  {X : Type u} → [MetricSpace X] → (X → X) → Set X → Set X

/-- All initial points whose forward iterates approach A. -/
def basin : basinType := fun F A => {x | ApproachesSet F A x}

def StableAttractorType :=
  {X : Type u} → [MetricSpace X] → (X → X) → Set X → Prop

/-- The source's full stable-attractor condition for a continuous metric map.
There is no transitivity or growth-exponent condition. -/
def StableAttractor : StableAttractorType := fun F A =>
  Continuous F ∧ A.Nonempty ∧ IsCompact A ∧ Invariant F A ∧
    SetLyapunovStable F A ∧ AttractsSetNeighborhood F A

def approachesSet_iff_distStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X) (hA : A.Nonempty) (x : X),
    ApproachesSet F A x ↔
      Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) A) atTop (𝓝 0)

def setLyapunovStable_iff_open_neighborhoodsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X),
    SetLyapunovStable F A ↔
      ∀ V : Set X, IsOpen V → A ⊆ V →
        ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ ∀ x ∈ U, ∀ n : ℕ, F^[n] x ∈ V

def attractsSetNeighborhood_iff_open_distStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X) (hA : A.Nonempty),
    AttractsSetNeighborhood F A ↔
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ ∀ x ∈ U,
        Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) A) atTop (𝓝 0)

def mem_basin_iff_distStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X) (hA : A.Nonempty) (x : X),
    x ∈ basin F A ↔
      Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) A) atTop (𝓝 0)

def stableAttractor_iffStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X),
    StableAttractor F A ↔
      Continuous F ∧ A.Nonempty ∧ IsCompact A ∧ F '' A = A ∧
        SetLyapunovStable F A ∧ AttractsSetNeighborhood F A

def basin_mem_nhdsSetStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X),
    StableAttractor F A → basin F A ∈ 𝓝ˢ A

end Specs.D13Unified.Ch18.AttractorDefinition
