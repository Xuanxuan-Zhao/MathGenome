import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.FirstIntegral
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.StabilityDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The pendulum on the whole real plane. The coordinate model uses the
supremum norm on ℝ². Stability includes forward existence in the canonical
maximal interval. Periodic energy ovals belong to the next allocated goal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace D13Unified.Ch13.PendulumPortrait
abbrev Plane := Fin 2 → ℝ

def vectorField (z : Plane) : Plane := ![z 1, -Real.sin (z 0)]
def energy (z : Plane) : ℝ := (z 1)^2 / 2 + 1 - Real.cos (z 0)
def pendulum : AutonomousODE Plane where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun z => vectorField z.val
  continuous_field := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun z : (univ : Set Plane) => z.val 1)
      exact (continuous_apply 1).comp continuous_subtype_val
    · change Continuous (fun z : (univ : Set Plane) => -Real.sin (z.val 0))
      exact (Real.continuous_sin.comp ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val)).neg

def center (k : ℤ) : Plane := ![2 * (k : ℝ) * Real.pi, 0]
def saddle (k : ℤ) : Plane := ![(2 * (k : ℝ) + 1) * Real.pi, 0]

/-- Expanded shared Lyapunov stability at p for the full-domain pendulum.
Both clauses refer to its actual canonical maximal solution. -/
def StableAt (p : Plane) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Plane, dist z p < δ →
    (∀ t : ℝ, 0 ≤ t → t ∈ (Ch06.StateDerivative.flowInterval pendulum z).carrier) ∧
    ∀ t : ℝ, 0 ≤ t → dist (Ch06.StateDerivative.flow pendulum t z) p < ε
end D13Unified.Ch13.PendulumPortrait

namespace Specs.D13Unified.Ch13.PendulumPortrait
open _root_.D13Unified _root_.D13Unified.Ch13.PendulumPortrait
open Ch01.SolutionConcepts Ch01.AutonomousParameters

def Regularity : Prop := ContDiff ℝ 1 vectorField ∧ ContDiff ℝ 1 energy

def Equilibria : Prop := ∀ k : ℤ, vectorField (center k) = 0 ∧ vectorField (saddle k) = 0

/-- Constancy for arbitrary pairs of times on any classical solution interval. -/
def Conservation : Prop :=
  ∀ (I : OpenTimeInterval) (z : ℝ → Plane),
    classicalSolutionOnValue (autonomousToODEValue pendulum) I z →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, energy (z t) = energy (z s)

def StrictMinima : Prop := ∀ k : ℤ, ∃ r : ℝ, 0 < r ∧
  ∀ z : Plane, dist z (center k) < r → z ≠ center k → energy (center k) < energy z

def CenterStability : Prop := ∀ k : ℤ, StableAt (center k)
def SaddleInstability : Prop := ∀ k : ℤ, ¬ StableAt (saddle k)

/-- These are eigenvalues of the actual derivative, not a named surrogate. -/
def SaddleEigenvalues : Prop := ∀ k : ℤ,
  Module.End.HasEigenvalue (fderiv ℝ vectorField (saddle k)).toLinearMap (1 : ℝ) ∧
  Module.End.HasEigenvalue (fderiv ℝ vectorField (saddle k)).toLinearMap (-1 : ℝ)
end Specs.D13Unified.Ch13.PendulumPortrait
