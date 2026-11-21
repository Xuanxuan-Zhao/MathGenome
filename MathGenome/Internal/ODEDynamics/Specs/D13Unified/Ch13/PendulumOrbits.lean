import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.PendulumPortrait
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.OmegaTopology
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Invariant
import Mathlib.Topology.Connected.Clopen

/-! The whole-plane pendulum of paper.tex, d13:13:pendulum.
The strip selects a single well on the unwrapped plane. No compactness,
regularity, periodicity or separatrix certificate is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch13.PendulumOrbits
open PendulumPortrait Ch11.Orbits Ch06.StateDerivative

/-- The portion of the energy level in the closed well centered at 2kπ.
For 0 < e < 2 its endpoints on the strip boundary are absent. -/
def oval (k : ℤ) (e : ℝ) : Set Plane :=
  {z | energy z = e ∧ |z 0 - 2 * (k : ℝ) * Real.pi| ≤ Real.pi}

/-- A specified point of the selected component. -/
def ovalPoint (k : ℤ) (e : ℝ) : Plane :=
  ![2 * (k : ℝ) * Real.pi, Real.sqrt (2 * e)]

/-- The usual local center property, with stability and actual maximal periods. -/
def IsCenter (p : Plane) : Prop :=
  StableAt p ∧ ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧
    ∀ z ∈ U, z ≠ p → ¬ IsConstant pendulum z ∧ HasLeastPeriod pendulum z

end D13Unified.Ch13.PendulumOrbits

namespace Specs.D13Unified.Ch13.PendulumOrbits
open _root_.D13Unified.Ch13.PendulumPortrait _root_.D13Unified.Ch13.PendulumOrbits
open _root_.D13Unified.Ch11.Orbits _root_.D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch11.Invariant Specs.D13Unified.Ch11.OmegaTopology

/-- A compact regular invariant component, equal to one nonconstant complete
periodic orbit. The least period supplies a simple regular closed parametrization.
The explicit well and base point distinguish it from all other components. -/
def EnergyOvals : Prop := ∀ (k : ℤ) (e : ℝ), 0 < e → e < 2 →
  IsCompact (oval k e) ∧ IsConnected (oval k e) ∧
  oval k e = connectedComponentIn {z : Plane | energy z = e} (ovalPoint k e) ∧
  (∀ z ∈ oval k e, Function.Surjective (fderiv ℝ energy z) ∧ vectorField z ≠ 0) ∧
  invariantValue pendulum (oval k e) ∧
  ∃ p ∈ oval k e, ¬ IsConstant pendulum p ∧ HasLeastPeriod pendulum p ∧
    oval k e = orbit pendulum p

/-- The selected oval is the full boundary of a bounded open region containing
its designated center. This makes the word "surrounding" explicit. -/
def Surrounding : Prop := ∀ (k : ℤ) (e : ℝ), 0 < e → e < 2 →
  ∃ V : Set Plane, IsOpen V ∧ Bornology.IsBounded V ∧ center k ∈ V ∧ frontier V = oval k e

def Centers : Prop := ∀ k : ℤ, IsCenter (center k)

/-- A complete nonconstant energy-two trajectory tends to the adjacent right
saddle. Its omega set is that equilibrium, and cannot be a nonconstant periodic
orbit. Quantification over k retains the unwrapped plane. -/
def SaddleLimit : Prop := ∀ k : ℤ, ∃ z : Plane,
  energy z = 2 ∧ ¬ IsConstant pendulum z ∧ IsComplete pendulum z ∧
  Tendsto (fun t => flow pendulum t z) atTop (𝓝 (saddle k)) ∧
  omegaValue pendulum z = {saddle k} ∧
  ¬ ∃ p : Plane, ¬ IsConstant pendulum p ∧ HasLeastPeriod pendulum p ∧
    omegaValue pendulum z = orbit pendulum p

end Specs.D13Unified.Ch13.PendulumOrbits
