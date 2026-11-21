import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.GramSupport
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open MeasureTheory Polynomial

namespace NumAnalysis206.Quadrature

/-- The next query may depend arbitrarily on all previous answers.
Only stages below the query budget are used; later stages are irrelevant. -/
abbrev AdaptiveQueries := (k : ℕ) → (Fin k → ℝ) → ℝ

/-- Chronological answers to sequential point queries. -/
def pointTranscript (q : AdaptiveQueries) (f : ℝ → ℝ) : (k : ℕ) → Fin k → ℝ
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (pointTranscript q f k) (f (q k (pointTranscript q f k)))

/-- An arbitrary deterministic output from at most `n` point values.
An early-stopping rule is represented by continuing with arbitrary queries and
having the output ignore the answers after its stopping decision. Earlier query
locations and the stopping decision are themselves determined by the answers. -/
def pointRule (n : ℕ) (q : AdaptiveQueries) (output : (Fin n → ℝ) → ℝ)
    (f : ℝ → ℝ) : ℝ := output (pointTranscript q f n)

namespace Specs

/-- A polynomial indistinguishable from zero by the prescribed adaptive queries,
but with strictly positive integral. No interval or compact-support restriction
is needed for this stronger version of the source result. -/
def adaptiveFoolingPolynomial : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ),
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ q : AdaptiveQueries, ∃ p : ℝ[X],
      p.natDegree ≤ 2 * n ∧
      pointTranscript q (fun x => p.eval x) n =
        pointTranscript q (fun _ => 0) n ∧
      0 < ∫ x : ℝ, p.eval x ∂μ

/-- No deterministic adaptive point rule with query budget `n` can integrate
all polynomials of degree at most `2*n` exactly, even with nonlinear output. -/
def adaptiveOptimality : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ (q : AdaptiveQueries) (output : (Fin n → ℝ) → ℝ),
      ¬ ∀ p : ℝ[X], p.natDegree ≤ 2 * n →
        pointRule n q output (fun x => p.eval x) = ∫ x : ℝ, p.eval x ∂μ

end Specs
end NumAnalysis206.Quadrature
