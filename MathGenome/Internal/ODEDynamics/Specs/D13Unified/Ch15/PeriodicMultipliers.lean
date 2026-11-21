import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LinearizedStability
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LinearizedInstability
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent specification of paper.tex, Proposition `d13:15:periodic-multipliers`.
The map is only assumed C¹ near its finite orbit. `ContDiffAt ℝ 1` at every
orbit point expresses exactly this local regularity; no regularity away from
those neighborhoods, injectivity, or invariance of an open domain is assumed.
The spectral condition is imposed at the one distinguished point `p`.
Distances and all quantitative estimates use the original norm. -/
noncomputable section
open Module Filter
open scoped Topology

namespace D13Unified.Ch15.PeriodicMultipliers

/-- The finite orbit, including phase zero and excluding phase `m`. -/
def finiteOrbit {X : Type*} (F : X → X) (p : X) (m : ℕ) : Set X :=
  Set.range (fun i : Fin m => F^[i.val] p)

/-- Stability as a set, with a single radius for all phases. -/
def SetLyapunovStable {X : Type*} [MetricSpace X] (F : X → X) (O : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x, Metric.infDist x O < δ → ∀ n : ℕ, Metric.infDist (F^[n] x) O < ε

/-- Exponential attraction with distance to the whole orbit on both sides. -/
def SetExponentiallyAttracting {X : Type*} [MetricSpace X]
    (F : X → X) (O : Set X) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, Metric.infDist x O < δ → ∀ n : ℕ,
      Metric.infDist (F^[n] x) O ≤ C * q ^ n * Metric.infDist x O

end D13Unified.Ch15.PeriodicMultipliers

namespace Specs.D13Unified.Ch15.PeriodicMultipliers
open _root_.D13Unified.Ch15.PeriodicMultipliers
open _root_.D13Unified.Ch08.MatrixPowerCriteria
open Specs.D13Unified.Ch15.DiscreteDefinitions

/-- The attracting alternative, including the quantitative bound, set stability,
and convergence from a neighborhood of every phase. -/
def periodicAttraction : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (b : Basis (Fin d) ℝ E) (F : E → E) (p : E) (m : ℕ),
    HasLeastPeriod F p m →
    (∀ z ∈ finiteOrbit F p m, ContDiffAt ℝ 1 F z) →
    spectralRadius ℂ (complexify (LinearMap.toMatrix b b
      (fderiv ℝ (F^[m]) p).toLinearMap)) < 1 →
    SetExponentiallyAttracting F (finiteOrbit F p m) ∧
    SetLyapunovStable F (finiteOrbit F p m) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, Metric.infDist x (finiteOrbit F p m) < δ →
      Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) (finiteOrbit F p m)) atTop (𝓝 0)

/-- The repelling alternative is instability of the entire finite orbit. -/
def periodicInstability : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (b : Basis (Fin d) ℝ E) (F : E → E) (p : E) (m : ℕ),
    HasLeastPeriod F p m →
    (∀ z ∈ finiteOrbit F p m, ContDiffAt ℝ 1 F z) →
    (∃ z : ℂ, Module.End.HasEigenvalue
      (complexify (LinearMap.toMatrix b b
        (fderiv ℝ (F^[m]) p).toLinearMap)).toLin' z ∧ 1 < ‖z‖) →
    ¬ SetLyapunovStable F (finiteOrbit F p m)

end Specs.D13Unified.Ch15.PeriodicMultipliers
