import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderReflector
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.DotProduct

/-! W32, the nonzero pivot-tail computation. The real input vector consists of
stored values; rounding and range checks are the abstract W02 interface. Signs,
negation, and copying are exact. Both choices of the W07 dot trace are covered.
The budget includes the adopted source amendment `d*u < 1`. -/
noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HouseholderPivotDefinitions
open MatrixDefinitions HouseholderDefinitions
open Rounding

def squaredNorm {d : ℕ} (fused : Bool) (round : ℝ → ℝ) (x : Vec ℝ d) : ℝ :=
  DotSpecs.finiteTrace fused round (⇑x) (⇑x)

def computedNorm {d : ℕ} (fused : Bool) (round : ℝ → ℝ) (x : Vec ℝ d) : ℝ :=
  round (Real.sqrt (squaredNorm fused round x))

def computedAlpha {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) : ℝ := -signPlus (x 0) * computedNorm fused round x

/-- Only the first component is rounded; all remaining components are copied. -/
def storedDirection {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) : Vec ℝ d :=
  x + (round (x 0 - computedAlpha fused round x) - x 0) • firstVector d

/-- Range checks for exactly the dot, square root, and first subtraction. The
nonnegativity of the square-root argument follows from the theorem's budget. -/
def safe {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ) (D : Set ℝ)
    (x : Vec ℝ d) : Prop :=
  DotSpecs.finiteSafe fused round D (⇑x) (⇑x) ∧
  Real.sqrt (squaredNorm fused round x) ∈ D ∧
  x 0 - computedAlpha fused round x ∈ D

def normError (d : ℕ) (u : ℝ) : ℝ :=
  max (1 - (1-u) * Real.sqrt (1 - _root_.Specs.NumAnalysis206.Rounding.gammaValue d u))
    ((1+u) * Real.sqrt (1 + _root_.Specs.NumAnalysis206.Rounding.gammaValue d u) - 1)

def directionError (d : ℕ) (u : ℝ) : ℝ := normError d u + u * (2 + normError d u)

def conclusion {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) (u : ℝ) : Prop :=
  let νhat := computedNorm fused round x
  let αhat := computedAlpha fused round x
  let w := storedDirection fused round x
  let a := normError d u
  let b₀ := directionError d u
  0 < νhat ∧ |νhat - ‖x‖| ≤ a * ‖x‖ ∧
  w ≠ 0 ∧ ‖w - direction x‖ ≤ b₀ * ‖x‖ ∧
  (reflector w).conjTranspose * reflector w = 1 ∧
  operatorNorm (reflector (direction x) - reflector w) ≤ 8 * b₀ ∧
  ‖αhat • firstVector d - (reflector w).toEuclideanLin x‖ ≤ (a + 8*b₀) * ‖x‖
end NumAnalysis206.HouseholderPivotDefinitions

namespace Specs.NumAnalysis206.HouseholderPivotStep
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.HouseholderPivotDefinitions

/-- Full pivot-step conclusion of W32, for either safe sequential dot trace. -/
def pivotStep : Prop :=
  ∀ {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ) (x : Vec ℝ d)
    (u : ℝ) (D : Set ℝ), x ≠ 0 →
    _root_.NumAnalysis206.Rounding.Specs.RelativeModelValue round u D →
    (d : ℝ) * u < 1 → _root_.Specs.NumAnalysis206.Rounding.gammaValue d u < 1 →
    safe fused round D x → conclusion fused round x u
end Specs.NumAnalysis206.HouseholderPivotStep
