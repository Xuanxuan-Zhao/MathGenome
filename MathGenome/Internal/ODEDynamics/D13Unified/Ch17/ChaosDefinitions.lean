import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions

/-!
The canonical Chapter 17 chaos predicates and their source formulations.
These are used for continuous maps in the manuscript. Continuity is a
hypothesis of that setting, not an additional property asserted by a predicate.
All iterates are the Chapter 15 natural-number iterates, including time zero.
-/

namespace D13Unified.Ch17.ChaosDefinitions

universe u
open Set
open scoped Topology

/-- Every pair of nonempty open sets is connected by some forward iterate. -/
abbrev TopologicallyTransitive :
    Specs.D13Unified.Ch17.ChaosDefinitions.TopologicallyTransitiveType.{u} :=
  Specs.D13Unified.Ch17.ChaosDefinitions.TopologicallyTransitive

/-- Points fixed by some positive iterate; not just points of one least period. -/
abbrev periodicPoints : Specs.D13Unified.Ch17.ChaosDefinitions.periodicPointsType.{u} :=
  Specs.D13Unified.Ch17.ChaosDefinitions.periodicPoints

/-- Density of all positive-period points. -/
abbrev DensePeriodicPoints :
    Specs.D13Unified.Ch17.ChaosDefinitions.DensePeriodicPointsType.{u} :=
  Specs.D13Unified.Ch17.ChaosDefinitions.DensePeriodicPoints

/-- Uniform positive separation in every neighborhood, with a strict inequality. -/
abbrev SensitiveDependence :
    Specs.D13Unified.Ch17.ChaosDefinitions.SensitiveDependenceType.{u} :=
  Specs.D13Unified.Ch17.ChaosDefinitions.SensitiveDependence

/-- Transitivity, dense periodic points, and sensitivity together. -/
abbrev Chaotic : Specs.D13Unified.Ch17.ChaosDefinitions.ChaoticType.{u} :=
  Specs.D13Unified.Ch17.ChaosDefinitions.Chaotic

theorem topologicallyTransitive_iff {X : Type u} [TopologicalSpace X] (F : X → X) :
    TopologicallyTransitive F ↔
      ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ n : ℕ, ((F^[n] '' U) ∩ V).Nonempty := Iff.rfl

theorem topologicallyTransitive_iff_exists_mem {X : Type u} [TopologicalSpace X]
    (F : X → X) :
    TopologicallyTransitive F ↔
      ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ x ∈ U, ∃ n : ℕ, F^[n] x ∈ V := by
  constructor
  · intro h U V hU hUne hV hVne
    rcases h U V hU hUne hV hVne with ⟨n, z, ⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, hx, n, hz⟩
  · intro h U V hU hUne hV hVne
    rcases h U V hU hUne hV hVne with ⟨x, hx, n, hn⟩
    exact ⟨n, F^[n] x, ⟨x, hx, rfl⟩, hn⟩

theorem mem_periodicPoints {X : Type u} (F : X → X) (x : X) :
    x ∈ periodicPoints F ↔ ∃ n : ℕ, 0 < n ∧ F^[n] x = x := Iff.rfl

theorem densePeriodicPoints_iff {X : Type u} [TopologicalSpace X] (F : X → X) :
    DensePeriodicPoints F ↔ Dense {x : X | ∃ n : ℕ, 0 < n ∧ F^[n] x = x} := Iff.rfl

theorem densePeriodicPoints_iff_open {X : Type u} [TopologicalSpace X] (F : X → X) :
    DensePeriodicPoints F ↔ ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ x ∈ U, ∃ n : ℕ, 0 < n ∧ F^[n] x = x := by
  change Dense (periodicPoints F) ↔ _
  rw [dense_iff_inter_open]
  rfl

theorem sensitiveDependence_iff_neighborhoods {X : Type u} [MetricSpace X] (F : X → X) :
    SensitiveDependence F ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ U ∈ 𝓝 x,
      ∃ y ∈ U, ∃ n : ℕ, δ < dist (F^[n] x) (F^[n] y) := Iff.rfl

theorem sensitiveDependence_iff_balls {X : Type u} [MetricSpace X] (F : X → X) :
    SensitiveDependence F ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ ε : ℝ, 0 < ε →
      ∃ y, dist y x < ε ∧ ∃ n : ℕ, δ < dist (F^[n] x) (F^[n] y) := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, ?_⟩
    intro x ε hε
    exact h x (Metric.ball x ε) (Metric.ball_mem_nhds x hε)
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, ?_⟩
    intro x U hU
    rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hball⟩
    rcases h x ε hε with ⟨y, hy, n, hn⟩
    exact ⟨y, hball hy, n, hn⟩

theorem chaotic_iff {X : Type u} [MetricSpace X] (F : X → X) :
    Chaotic F ↔ TopologicallyTransitive F ∧ DensePeriodicPoints F ∧ SensitiveDependence F :=
  Iff.rfl

end D13Unified.Ch17.ChaosDefinitions
