import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.ChebyshevLebesgue
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.HolderBernstein
import Mathlib.Analysis.Asymptotics.Defs

/-! Independent statements for the final Hölder assertion and quantitative rate
of W53, paper.tex:1944–1946, 2012–2025. The interpolants are the same bounded
operators on continuous real functions with the uniform norm as in W52.
The nodes are the affine images of the `n+1` Chebyshev roots. -/
noncomputable section
open Filter
open scoped Topology

namespace Specs.NumAnalysis206.Approximation.ChebyshevConvergence
open _root_.NumAnalysis206.Approximation
open Specs.NumAnalysis206.Approximation
open Specs.NumAnalysis206.Approximation.ChebyshevLebesgue

/-- The quantitative bound, including the interval length and Hölder constant. -/
def quantitativeBound : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b) {α L : ℝ},
    0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    ∀ {n : ℕ}, 1 ≤ n →
      ‖f - interpolationOperatorValue (affineNodesValue a b hab n) f‖ ≤
        (1 + lebesgueConstantValue (affineNodesValue a b hab n)) *
          L * (b - a) ^ α * (4 * (n : ℝ)) ^ (-α / 2)

/-- The implied constant may depend on the fixed function and interval. -/
def asymptoticRate : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b) {α L : ℝ},
    0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    Asymptotics.IsBigO atTop
      (fun n : ℕ => ‖f - interpolationOperatorValue (affineNodesValue a b hab n) f‖)
      (fun n : ℕ => (1 + Real.log ((n : ℝ) + 1)) * (n : ℝ) ^ (-α / 2))

/-- Convergence in the common continuous-function space is uniform norm convergence. -/
def convergence : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b) {α L : ℝ},
    0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    Tendsto (fun n : ℕ => interpolationOperatorValue (affineNodesValue a b hab n) f)
      atTop (𝓝 f)

/-- The same conclusion expressed directly as uniform convergence at all points. -/
def uniformConvergence : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b) {α L : ℝ},
    0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    TendstoUniformly
      (fun (n : ℕ) (t : Set.Icc a b) =>
        interpolationOperatorValue (affineNodesValue a b hab n) f t) f atTop

end Specs.NumAnalysis206.Approximation.ChebyshevConvergence
