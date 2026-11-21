import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
namespace Specs.NumAnalysis206.HermitianResidualGap
open _root_.NumAnalysis206.MatrixDefinitions

/-- A closest spectral value exists, and its distance is bounded by the residual.
The eigenvalue list is the full Hermitian spectrum, including multiplicities. -/
def residual_certificate : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian)
    (v : Vec K n) (μ : ℝ), ‖v‖ = 1 →
    ∃ i : Fin n, (∀ j, |eigenvalue A hA i - μ| ≤ |eigenvalue A hA j - μ|) ∧
      |eigenvalue A hA i - μ| ≤ ‖A.toEuclideanLin v - (μ : K) • v‖

/-- Distance to the actual real spectrum, with the Euclidean residual. -/
def residual_distance : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n) (_hA : A.IsHermitian)
    (v : Vec K n) (μ : ℝ), ‖v‖ = 1 →
    Metric.infDist μ (spectrum ℝ A) ≤ ‖A.toEuclideanLin v - (μ : K) • v‖

/-- An arbitrary set of eigenvalues selects their complete eigenspaces. No
nonemptiness or properness restriction is placed on the selection. -/
def residual_gap : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian)
    (v : Vec K n) (μ : ℝ) (s : Set ℝ) (δ : ℝ), 0 < δ →
    (∀ i, eigenvalue A hA i ∉ s → δ ≤ |eigenvalue A hA i - μ|) →
    ‖v - spectralProjection A hA s v‖ ≤ ‖A.toEuclideanLin v - (μ : K) • v‖ / δ

end Specs.NumAnalysis206.HermitianResidualGap
