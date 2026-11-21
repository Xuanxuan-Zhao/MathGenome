import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Independent specification for the variance necessity stage of Theorem 8.8,
paper.tex:2926–2972, in particular 2945–2971. The underlying probability
space need not be complete. No moment assumption is imposed on the original
variables. Natural indices start at zero, which simply reindexes the source's
sequence starting at one. -/

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityFoundations.Ch08

/-- Ordinary convergence of a real series in its given order. In particular,
this predicate permits conditional convergence. -/
def OrderedSeriesConverges (f : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop (𝓝 l)

/-- The exact truncation in Theorem 8.8; equality at the cutoff is retained. -/
noncomputable def symmetricTruncation {Ω : Type*} (a : ℝ) (X : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun k => {ω | |X k ω| ≤ a}.indicator (X k)

end ProbabilityFoundations.Ch08

namespace Specs.ProbabilityFoundations.Ch08.ThreeSeriesVarianceNecessity

universe u
open _root_.ProbabilityFoundations.Ch08

/-- Full assigned conclusion, with no assumption on the series of means.
The bounded truncations have finite second moments, so real variance agrees
with the usual finite integral of the squared centered variable. -/
def summableVarianceSymmetricTruncationType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ), (∀ k, Measurable (X k)) →
    ProbabilityTheory.iIndepFun X P →
    ∀ a : ℝ, 0 < a →
    (∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => X k ω)) →
    Summable (fun k => ProbabilityTheory.variance (symmetricTruncation a X k) P)

end Specs.ProbabilityFoundations.Ch08.ThreeSeriesVarianceNecessity
