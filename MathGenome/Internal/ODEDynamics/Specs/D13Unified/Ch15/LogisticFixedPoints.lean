import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent statements for paper.tex, Proposition `d13:15:logistic-fixed-points`.
All dynamics are on the real line; interval invariance is a separate assertion.
Repulsion means that every sufficiently close point other than the fixed point
has a finite first exit from a fixed ball. No threshold classification is made. -/
noncomputable section
namespace D13Unified.Ch15.LogisticFixedPoints

/-- All nearby punctured orbits leave a fixed neighborhood in finite time. -/
def Repelling (F : ℝ → ℝ) (p : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 0 < ‖x - p‖ → ‖x - p‖ < r →
    ∃ N : ℕ, 0 < N ∧ r ≤ ‖F^[N] x - p‖ ∧
      ∀ n : ℕ, n < N → ‖F^[n] x - p‖ < r

end D13Unified.Ch15.LogisticFixedPoints
namespace Specs.D13Unified.Ch15.LogisticFixedPoints
open _root_.D13Unified.Ch15.LogisticFixedPoints
open Specs.D13Unified.Ch15.DiscreteDefinitions

def logisticMapType := ℝ → ℝ → ℝ
def logisticMap : logisticMapType := fun μ x => μ * x * (1 - x)

def intervalInvariant : Prop := ∀ μ : ℝ, 0 ≤ μ → μ ≤ 4 →
  PositivelyInvariant (logisticMap μ) (Set.Icc 0 1)

def fixedPoints_zeroParameter : Prop := ∀ x : ℝ, logisticMap 0 x = x ↔ x = 0

def fixedPoints_nonzeroParameter : Prop := ∀ μ : ℝ, μ ≠ 0 → ∀ x : ℝ,
  logisticMap μ x = x ↔ x = 0 ∨ x = 1 - μ⁻¹

def coincident_fixedPoints : Prop := ∀ μ : ℝ, μ ≠ 0 → (1 - μ⁻¹ = 0 ↔ μ = 1)

def secondFixedPoint_mem : Prop := ∀ μ : ℝ, 1 ≤ μ → 1 - μ⁻¹ ∈ Set.Icc (0 : ℝ) 1

def derivative_zero : Prop := ∀ μ : ℝ, HasDerivAt (logisticMap μ) μ 0

def derivative_second : Prop := ∀ μ : ℝ, μ ≠ 0 →
  HasDerivAt (logisticMap μ) (2 - μ) (1 - μ⁻¹)

def zero_attracting : Prop := ∀ μ : ℝ, 0 ≤ μ → μ < 1 →
  LocallyExponentiallyStable (logisticMap μ) 0 ∧ AsymptoticallyStable (logisticMap μ) 0

def second_attracting : Prop := ∀ μ : ℝ, 1 < μ → μ < 3 →
  LocallyExponentiallyStable (logisticMap μ) (1 - μ⁻¹) ∧
    AsymptoticallyStable (logisticMap μ) (1 - μ⁻¹)

def zero_repelling : Prop := ∀ μ : ℝ, 1 < μ →
  Repelling (logisticMap μ) 0 ∧ ¬ LyapunovStable (logisticMap μ) 0

def second_repelling : Prop := ∀ μ : ℝ, 3 < μ →
  Repelling (logisticMap μ) (1 - μ⁻¹) ∧
    ¬ LyapunovStable (logisticMap μ) (1 - μ⁻¹)

end Specs.D13Unified.Ch15.LogisticFixedPoints
