import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! The error estimates and coefficient limit in W75, paper.tex:2821–2875.
Only local C² regularity is assumed. The interval estimates use the shared jet
interface, including one-sided derivatives at the endpoints. -/
noncomputable section
namespace Specs.NumAnalysis206.Newton.SecantError
open Set Filter
open scoped Topology
open NumAnalysis206.Approximation.IntervalCalculusSpec

/-- A symmetric closed neighborhood with positive lower slope and finite curvature bound. -/
def localBounds : Prop :=
  ∀ (f : ℝ → ℝ) (p : ℝ), ContDiffAt ℝ 2 f p → deriv f p ≠ 0 →
    ∃ R m M : ℝ, 0 < R ∧ 0 < m ∧ 0 ≤ M ∧
      jetValue (p - R) (p + R) 2 f (fun j => iteratedDeriv j f) ∧
      ∀ t ∈ Icc (p - R) (p + R),
        m ≤ |deriv f t| ∧ |deriv (deriv f) t| ≤ M

/-- Exact algebraic error formula at three distinct nodes. -/
def errorIdentity : Prop :=
  ∀ (f : ℝ → ℝ) (p u v : ℝ), f p = 0 → u ≠ v → u ≠ p → v ≠ p →
    secantSlopeValue f u v ≠ 0 →
    secantStepValue f u v - p =
      (Specs.NumAnalysis206.Approximation.dividedDifferenceValue
        [(u, f u), (v, f v), (p, f p)] / secantSlopeValue f u v) * (v - p) * (u - p)

/-- The mean value theorem bounds every nondegenerate secant slope. -/
def slopeLower : Prop :=
  ∀ (f : ℝ → ℝ) (D : ℕ → ℝ → ℝ) (a b m u v : ℝ),
    jetValue a b 2 f D → (∀ t ∈ Icc a b, m ≤ |D 1 t|) →
    u ∈ Icc a b → v ∈ Icc a b → u ≠ v → m ≤ |secantSlopeValue f u v|

/-- The quantitative secant estimate, with the source's exact constant. -/
def errorBound : Prop :=
  ∀ (f : ℝ → ℝ) (D : ℕ → ℝ → ℝ) (a b m M p u v : ℝ),
    jetValue a b 2 f D → f p = 0 → 0 < m → 0 ≤ M →
    (∀ t ∈ Icc a b, m ≤ |D 1 t| ∧ |D 2 t| ≤ M) →
    p ∈ Icc a b → u ∈ Icc a b → v ∈ Icc a b →
    u ≠ v → u ≠ p → v ≠ p →
    |secantStepValue f u v - p| ≤ M / (2 * m) * |(v - p) * (u - p)|

/-- The local estimates together, under precisely the simple-root regularity
assumptions, with no slope or curvature certificate assumed in advance. -/
def localEstimates : Prop :=
  ∀ (f : ℝ → ℝ) (p : ℝ), ContDiffAt ℝ 2 f p → f p = 0 → deriv f p ≠ 0 →
    ∃ R m M : ℝ, 0 < R ∧ 0 < m ∧ 0 ≤ M ∧
      ∀ u ∈ Icc (p - R) (p + R), ∀ v ∈ Icc (p - R) (p + R),
        u ≠ v → u ≠ p → v ≠ p →
        m ≤ |secantSlopeValue f u v| ∧
        secantStepValue f u v - p =
          (Specs.NumAnalysis206.Approximation.dividedDifferenceValue
            [(u, f u), (v, f v), (p, f p)] / secantSlopeValue f u v) * (v - p) * (u - p) ∧
        |secantStepValue f u v - p| ≤ M / (2 * m) * |(v - p) * (u - p)|

/-- A reached root remains fixed even without a denominator certificate. -/
def stepOfRoot : Prop :=
  ∀ (f : ℝ → ℝ) (u v : ℝ), f v = 0 → secantStepValue f u v = v

/-- Before a root stop a valid step differs from its current node. -/
def stepNeCurrent : Prop :=
  ∀ (f : ℝ → ℝ) (u v : ℝ), f v ≠ 0 → secantSlopeValue f u v ≠ 0 →
    secantStepValue f u v ≠ v

/-- The absolute coefficient limit for arbitrary sequences approaching the simple root.
Distinctness is required only eventually; the limit also permits f''(p) = 0. -/
def coefficientLimit : Prop :=
  ∀ (f : ℝ → ℝ) (p : ℝ), ContDiffAt ℝ 2 f p → f p = 0 → deriv f p ≠ 0 →
    ∀ (u v : ℕ → ℝ), Tendsto u atTop (𝓝 p) → Tendsto v atTop (𝓝 p) →
      (∀ᶠ n in atTop, u n ≠ v n ∧ u n ≠ p ∧ v n ≠ p) →
      Tendsto (fun n => |Specs.NumAnalysis206.Approximation.dividedDifferenceValue
        [(u n, f (u n)), (v n, f (v n)), (p, f p)] / secantSlopeValue f (u n) (v n)|)
        atTop (𝓝 |deriv (deriv f) p / (2 * deriv f p)|)

end Specs.NumAnalysis206.Newton.SecantError
