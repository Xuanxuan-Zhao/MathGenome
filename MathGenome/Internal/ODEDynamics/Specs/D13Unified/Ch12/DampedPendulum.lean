import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.Lyapunov
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.Lasalle
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.FirstIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Specs.D13Unified.Ch12.DampedPendulum
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch12.StabilityDefinitions Ch11.Invariant

abbrev Plane := ℝ × ℝ

def vectorField (c : ℝ) (z : Plane) : Plane := (z.2, -Real.sin z.1 - c * z.2)

def pendulum (c : ℝ) : AutonomousODE Plane where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun z => vectorField c z.val
  continuous_field := by unfold vectorField; fun_prop

def energy (z : Plane) : ℝ := z.2 ^ 2 / 2 + 1 - Real.cos z.1

/-- A sublevel restricted to one neighborhood of the selected equilibrium;
the full energy sublevel on the covering plane is not compact. -/
def sublevel (r a : ℝ) : Set Plane := closedBall 0 r ∩ energy ⁻¹' Iic a

def Dissipation : Prop := ∀ (c : ℝ) (z : Plane),
  (fderiv ℝ energy z) (vectorField c z) = -c * z.2 ^ 2

/-- Arbitrarily small compact sublevel neighborhoods, with forward invariance
and a singleton largest invariant subset of the zero-velocity set. -/
def Trapping : Prop := ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
  ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (sublevel r a) ∧ positiveInvariantValue (pendulum c) (sublevel r a) ∧
    ball 0 δ ⊆ sublevel r a ∧ sublevel r a ⊆ ball 0 (min ε (Real.pi / 2)) ∧
    Lasalle.completeCore (pendulum c) {z | z ∈ sublevel r a ∧ z.2 = 0} = {0}

/-- Directly expanded shared stability predicate, including forward existence. -/
def AsymptoticStability : Prop := ∀ c : ℝ, 0 < c →
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Plane, ‖z‖ < δ →
    (∀ t : ℝ, 0 ≤ t → (t,z) ∈ flowDomain (pendulum c)) ∧
    ∀ t : ℝ, 0 ≤ t → ‖flow (pendulum c) t z‖ < ε) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ z : Plane, ‖z‖ < δ →
    (∀ t : ℝ, 0 ≤ t → (t,z) ∈ flowDomain (pendulum c)) ∧
    Tendsto (fun t : ℝ => flow (pendulum c) t z) atTop (𝓝 (0 : Plane))

/-- Conservation for every classical solution on its actual open interval. -/
def UndampedConservation : Prop :=
  ∀ (I : OpenTimeInterval) (x : ℝ → Plane),
    Ch01.SolutionConcepts.classicalSolutionOnValue (autonomousToODEValue (pendulum 0)) I x →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, energy (x t) = energy (x s)

/-- Nearby undamped solutions exist for all forward times. Every one with
nonzero energy fails to converge to the selected equilibrium. -/
def UndampedNonconvergence : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ z : Plane, ‖z‖ < δ →
  (∀ t : ℝ, 0 ≤ t → (t,z) ∈ flowDomain (pendulum 0)) ∧
  (energy z ≠ 0 → ¬ Tendsto (fun t : ℝ => flow (pendulum 0) t z) atTop (𝓝 (0 : Plane)))

end Specs.D13Unified.Ch12.DampedPendulum
