import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.InexactBound
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.ResidualCertificate
import Mathlib.Order.LiminfLimsup

/-! W71 on a metric contraction domain. Completeness is unnecessary once the
fixed point is given. Membership of every computed iterate is a premise. -/
namespace Specs.NumAnalysis206.Iterations.InexactLimits

universe u

open Filter
open scoped Topology

/-- The upper limit for a common bound on the evaluation errors. -/
def CommonErrorLimsup : Prop :=
  ∀ {X : Type*} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (p : X) (x : ℕ → X) (δ : ℕ → ℝ) (ε : ℝ),
    0 ≤ q → q < 1 →
    (∀ z ∈ D, T z ∈ D) →
    (∀ u ∈ D, ∀ v ∈ D, dist (T u) (T v) ≤ q * dist u v) →
    p ∈ D → T p = p → (∀ j, x j ∈ D) →
    (∀ j, dist (x (j + 1)) (T (x j)) ≤ δ j) →
    (∀ j, δ j ≤ ε) →
    limsup (fun n => dist (x n) p) atTop ≤ ε / (1 - q)

/-- Vanishing errors suffice; summability is not required. -/
def VanishingErrorConvergence : Prop :=
  ∀ {X : Type*} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (p : X) (x : ℕ → X) (δ : ℕ → ℝ),
    0 ≤ q → q < 1 →
    (∀ z ∈ D, T z ∈ D) →
    (∀ u ∈ D, ∀ v ∈ D, dist (T u) (T v) ≤ q * dist u v) →
    p ∈ D → T p = p → (∀ j, x j ∈ D) →
    (∀ j, dist (x (j + 1)) (T (x j)) ≤ δ j) →
    Tendsto δ atTop (𝓝 0) → Tendsto x atTop (𝓝 p)

/-- Retain the exact finite convolution, including `n = 0` and `q = 0`. -/
def FiniteConvolution : Prop := Specs.NumAnalysis206.Iterations.InexactConvolutionBound.{u}

/-- Retain the finite common-error geometric estimate. -/
def FiniteCommonBound : Prop := Specs.NumAnalysis206.Iterations.InexactCommonBound.{u}

/-- Retain the stopping certificate with a separately certified evaluation error. -/
def ApproximateStopping : Prop :=
  Specs.NumAnalysis206.Iterations.ResidualCertificate.ApproximateResidualStopping.{u}

end Specs.NumAnalysis206.Iterations.InexactLimits
