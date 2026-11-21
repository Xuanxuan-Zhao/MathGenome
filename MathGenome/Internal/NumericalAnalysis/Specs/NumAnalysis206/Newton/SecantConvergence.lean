import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.SecantError

/-! W75: local existence, stopping and convergence of the exact secant method.
States use the shared two-slot iteration. State zero is `(u,v)`; a non-root
state `(xₙ₋₁,xₙ)` advances to `(xₙ,xₙ₊₁)`. Either root slot is checked
before division. No regularity outside the supplied interval is imposed. -/
noncomputable section
namespace Specs.NumAnalysis206.Newton.SecantConvergence
open Set Filter
open scoped Topology
open NumAnalysis206.Approximation.IntervalCalculusSpec
open Specs.NumAnalysis206.Newton

/-- The complete behavior of the actual, root-stopped secant state sequence.
Validity and invariance hold at every state. The estimate applies at every used
secant step; the alternative is a finite successful stop or an infinite run
with no roots, distinct consecutive nodes, nonzero slopes and both slots tending
to the specified root. The zero-curvature clause includes initial root stops. -/
def RunProperties (f : ℝ → ℝ) (p r m M u v : ℝ) : Prop :=
  let X := secantIteratesValue f u v
  (∀ n, |(X n).1 - p| ≤ r ∧ |(X n).2 - p| ≤ r ∧ secantStateValidValue f (X n)) ∧
  (∀ n, f (X n).1 ≠ 0 → f (X n).2 ≠ 0 →
    m ≤ |secantSlopeValue f (X n).1 (X n).2| ∧
    X (n + 1) = ((X n).2, secantStepValue f (X n).1 (X n).2) ∧
    secantStepValue f (X n).1 (X n).2 ≠ (X n).2 ∧
    |secantStepValue f (X n).1 (X n).2 - p| ≤
      M / (2 * m) * |((X n).2 - p) * ((X n).1 - p)|) ∧
  (M = 0 → SuccessfulSecantStopValue f 1 X) ∧
  ((∃ N, SuccessfulSecantStopValue f N X) ∨
    ((∀ n, f (X n).1 ≠ 0 ∧ f (X n).2 ≠ 0 ∧
      (X n).1 ≠ (X n).2 ∧ secantSlopeValue f (X n).1 (X n).2 ≠ 0) ∧
      Tendsto (fun n => (X n).1) atTop (𝓝 p) ∧
      Tendsto (fun n => (X n).2) atTop (𝓝 p)))

/-- Quantitative version on any certified derivative-bound interval, including M=0. -/
def intervalConvergence : Prop :=
  ∀ (f : ℝ → ℝ) (D : ℕ → ℝ → ℝ) (p R m M r : ℝ),
    jetValue (p - R) (p + R) 2 f D → f p = 0 → 0 < m → 0 ≤ M →
    (∀ t ∈ Icc (p - R) (p + R), m ≤ |D 1 t| ∧ |D 2 t| ≤ M) →
    0 < r → r ≤ R → M / (2 * m) * r < 1 →
    ∀ u v : ℝ, |u - p| ≤ r → |v - p| ≤ r → u ≠ v →
      RunProperties f p r m M u v

/-- C² near a simple root supplies the interval, slope/curvature bounds and
positive convergence radius, uniformly for every distinct pair of starting points. -/
def localConvergence : Prop :=
  ∀ (f : ℝ → ℝ) (p : ℝ), ContDiffAt ℝ 2 f p → f p = 0 → deriv f p ≠ 0 →
    ∃ R m M r : ℝ, 0 < R ∧ 0 < m ∧ 0 ≤ M ∧ 0 < r ∧ r ≤ R ∧
      M / (2 * m) * r < 1 ∧
      jetValue (p - R) (p + R) 2 f (fun j => iteratedDeriv j f) ∧
      (∀ t ∈ Icc (p - R) (p + R),
        m ≤ |deriv f t| ∧ |deriv (deriv f) t| ≤ M) ∧
      ∀ u v : ℝ, |u - p| ≤ r → |v - p| ≤ r → u ≠ v →
        RunProperties f p r m M u v

end Specs.NumAnalysis206.Newton.SecantConvergence
