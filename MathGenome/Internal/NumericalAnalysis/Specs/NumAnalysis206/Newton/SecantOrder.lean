import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.SecantConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio

/-! W75, paper.tex:2821–2893. The original closed theorem types, with no
conditional proof premises. The two-slot state at time n is (xₙ,xₙ₊₁), so
its second/first error ratio is precisely the stated consecutive-error ratio. -/
noncomputable section
namespace Specs.NumAnalysis206.Newton.SecantOrder
open Set Filter
open scoped Topology
open NumAnalysis206.Approximation.IntervalCalculusSpec
open Specs.NumAnalysis206.Newton

/-- Retain the full interval theorem, including stopping, denominator validity,
invariance, the quantitative error estimate, and the zero-curvature case. -/
def intervalConvergence : Prop := SecantConvergence.intervalConvergence

/-- Uniform local convergence together with the precise positive asymptotic
constant for every nonterminating run with nonzero second derivative. No error
ratio limit, or positivity of errors or divided differences, is assumed. -/
def localOrder : Prop :=
  ∀ (f : ℝ → ℝ) (p : ℝ), ContDiffAt ℝ 2 f p → f p = 0 → deriv f p ≠ 0 →
    ∃ R m M r : ℝ, 0 < R ∧ 0 < m ∧ 0 ≤ M ∧ 0 < r ∧ r ≤ R ∧
      M / (2 * m) * r < 1 ∧
      jetValue (p - R) (p + R) 2 f (fun j => iteratedDeriv j f) ∧
      (∀ t ∈ Icc (p - R) (p + R),
        m ≤ |deriv f t| ∧ |deriv (deriv f) t| ≤ M) ∧
      ∀ u v : ℝ, |u - p| ≤ r → |v - p| ≤ r → u ≠ v →
        SecantConvergence.RunProperties f p r m M u v ∧
        (¬ (∃ N, SuccessfulSecantStopValue f N (secantIteratesValue f u v)) →
          deriv (deriv f) p ≠ 0 →
          let C := |deriv (deriv f) p / (2 * deriv f p)|
          0 < C ^ (1 / Real.goldenRatio) ∧
          Tendsto (fun n => |(secantIteratesValue f u v n).2 - p| /
              |(secantIteratesValue f u v n).1 - p| ^ Real.goldenRatio)
            atTop (𝓝 (C ^ (1 / Real.goldenRatio))))

end Specs.NumAnalysis206.Newton.SecantOrder
