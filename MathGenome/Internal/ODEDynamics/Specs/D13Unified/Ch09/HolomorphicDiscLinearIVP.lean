import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.HolomorphicDependence
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Matrix.Normed

/-! Independent specification of the whole-disc construction in the proof of
`paper.tex`, d13:09:ordinary-series. The coefficient is a complex linear
operator on the finite coordinate space; thus it represents an arbitrary
complex square matrix, with its genuine complex-time action. -/
open scoped ENNReal Matrix.Norms.Elementwise

namespace D13Unified.Ch09.HolomorphicDiscLinearIVP

open Metric
open D13Unified.Ch06.HolomorphicDependence

/-- The centered open complex disc, including the entire plane when `R = ∞`. -/
def disc (R : ℝ≥0∞) : Set ℂ := eball 0 R

/-- A holomorphic solution on the full prescribed disc with its initial value. -/
def IsDiscSolution {n : ℕ} (R : ℝ≥0∞)
    (A : ℂ → State n →L[ℂ] State n) (η : State n) (Y : ℂ → State n) : Prop :=
  Y 0 = η ∧ DifferentiableOn ℂ Y (disc R) ∧
    ∀ z ∈ disc R, HasDerivAt Y (A z (Y z)) z

end D13Unified.Ch09.HolomorphicDiscLinearIVP

namespace Specs.D13Unified.Ch09.HolomorphicDiscLinearIVP

open _root_.D13Unified.Ch06.HolomorphicDependence
open _root_.D13Unified.Ch09.HolomorphicDiscLinearIVP

/-- Existence and uniqueness on the whole disc, with no boundedness assumption
on the coefficient over the full open disc and with infinite radius allowed.
Uniqueness is equality on the prescribed domain, since values outside it are
irrelevant to this initial value problem. -/
def holomorphic_disc_linear_ivp_type : Prop :=
  ∀ (n : ℕ) (R : ℝ≥0∞), 0 < R →
    ∀ (A : ℂ → State n →L[ℂ] State n), DifferentiableOn ℂ A (disc R) →
    ∀ η : State n, ∃ Y : ℂ → State n,
      IsDiscSolution R A η Y ∧
      ∀ Z : ℂ → State n, IsDiscSolution R A η Z → Set.EqOn Z Y (disc R)

/-- The same whole-disc result in the literal matrix-times-vector notation of
the paper. The matrix space has its entrywise maximum norm, so its complex
differentiability is exactly entrywise holomorphy. -/
def holomorphic_disc_matrix_ivp_type : Prop :=
  ∀ (n : ℕ) (R : ℝ≥0∞), 0 < R →
    ∀ (A : ℂ → Matrix (Fin n) (Fin n) ℂ), DifferentiableOn ℂ A (disc R) →
    ∀ η : State n, ∃ Y : ℂ → State n,
      (Y 0 = η ∧ DifferentiableOn ℂ Y (disc R) ∧
        ∀ z ∈ disc R, HasDerivAt Y ((A z).mulVec (Y z)) z) ∧
      ∀ Z : ℂ → State n, Z 0 = η →
        (∀ z ∈ disc R, HasDerivAt Z ((A z).mulVec (Z z)) z) →
        Set.EqOn Z Y (disc R)

end Specs.D13Unified.Ch09.HolomorphicDiscLinearIVP
