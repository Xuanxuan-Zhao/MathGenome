import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.PeriodicMultipliers
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent specification of paper.tex, Proposition `d13:16:flip-normal-form`.
The stability conclusions use the original real metric and distance to the
whole orbit. The open interval (0,1) is retained in full. -/
noncomputable section
open Filter
open scoped Topology
namespace Specs.D13Unified.Ch16.FlipNormalForm
open Specs.D13Unified.Ch15.DiscreteDefinitions
open _root_.D13Unified.Ch15.PeriodicMultipliers

def flip (μ x : ℝ) : ℝ := -(1 + μ) * x + x ^ 3

def flipType := ℝ → ℝ → ℝ

def zeroAttraction : Prop :=
  ∀ μ : ℝ, -1 < μ → μ < 0 →
    flip μ 0 = 0 ∧ LocallyExponentiallyStable (flip μ) 0 ∧
    AsymptoticallyStable (flip μ) 0

def zeroInstability : Prop :=
  ∀ μ : ℝ, 0 < μ → flip μ 0 = 0 ∧ ¬ LyapunovStable (flip μ) 0

def cycleData : Prop :=
  ∀ μ : ℝ, 0 < μ → μ < 1 →
    Real.sqrt μ ≠ -Real.sqrt μ ∧
    flip μ (Real.sqrt μ) = -Real.sqrt μ ∧
    flip μ (-Real.sqrt μ) = Real.sqrt μ ∧
    HasLeastPeriod (flip μ) (Real.sqrt μ) 2 ∧
    HasLeastPeriod (flip μ) (-Real.sqrt μ) 2 ∧
    deriv ((flip μ)^[2]) (Real.sqrt μ) = (-1 + 2 * μ) ^ 2 ∧
    deriv ((flip μ)^[2]) (-Real.sqrt μ) = (-1 + 2 * μ) ^ 2

def cycleAttraction : Prop :=
  ∀ μ : ℝ, 0 < μ → μ < 1 →
    let O : Set ℝ := {Real.sqrt μ, -Real.sqrt μ}
    SetExponentiallyAttracting (flip μ) O ∧ SetLyapunovStable (flip μ) O ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, Metric.infDist x O < δ →
      Tendsto (fun n : ℕ => Metric.infDist ((flip μ)^[n] x) O) atTop (𝓝 0)

def amplitudeLimit : Prop :=
  (∀ μ : ℝ, 0 < μ → |Real.sqrt μ| = Real.sqrt μ ∧
    |-Real.sqrt μ| = Real.sqrt μ) ∧
  Tendsto Real.sqrt (𝓝[Set.Ioi 0] 0) (𝓝 0)

end Specs.D13Unified.Ch16.FlipNormalForm
