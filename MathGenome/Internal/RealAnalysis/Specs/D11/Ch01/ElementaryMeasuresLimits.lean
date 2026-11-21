import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Independent statements for paper.tex:296–315 and 341–359.

All evaluations are on the given sigma-algebra. The measures are the canonical
native positive measures, whose equivalence with functions on measurable sets
is the upstream `MeasureDefinitions` interface. No measurability of singletons,
nonemptiness, completeness, or finiteness assumption is imposed on the space.

Atomic weights range over `[0,∞]`, without an injectivity assumption on their
locations. The general weighted sum instead has finite nonnegative coefficients
(`ℝ≥0`); the real-coefficient version records the literal `aₙ ≥ 0` formulation.
The increasing-limit hypothesis concerns every measurable set. Its conclusion
includes both the supremum formula and convergence to that value in `[0,∞]`.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

universe u

namespace Specs.D11.Ch01.ElementaryMeasuresLimits

def counting_measure : Prop :=
  ∀ {α : Type u} [MeasurableSpace α], ∃ c : Measure α,
    (∀ (s : Set α), MeasurableSet s → ∀ hs : s.Finite,
      c s = (hs.toFinset.card : ℝ≥0∞)) ∧
    (∀ (s : Set α), MeasurableSet s → s.Infinite → c s = ∞)

def point_measure : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (x : α), ∃ δ : Measure α,
    ∀ (s : Set α), MeasurableSet s → δ s = s.indicator (fun _ => (1 : ℝ≥0∞)) x

def atomic_measure : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (x : ℕ → α) (a : ℕ → ℝ≥0∞),
    ∃ μ : Measure α, ∀ (s : Set α), MeasurableSet s →
      μ s = ∑' n, a n * s.indicator (fun _ => (1 : ℝ≥0∞)) (x n)

def weighted_sum : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : ℕ → Measure α) (a : ℕ → ℝ≥0),
    ∃ ν : Measure α, ∀ (s : Set α), MeasurableSet s →
      ν s = ∑' n, (a n : ℝ≥0∞) * μ n s

def weighted_sum_real : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : ℕ → Measure α) (a : ℕ → ℝ),
    (∀ n, 0 ≤ a n) → ∃ ν : Measure α, ∀ (s : Set α), MeasurableSet s →
      ν s = ∑' n, ENNReal.ofReal (a n) * μ n s

def increasing_limit : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : ℕ → Measure α),
    (∀ (s : Set α), MeasurableSet s → Monotone (fun n => μ n s)) →
    ∃ ν : Measure α, ∀ (s : Set α), MeasurableSet s →
      ν s = (⨆ n, μ n s) ∧ Tendsto (fun n => μ n s) atTop (𝓝 (ν s))

end Specs.D11.Ch01.ElementaryMeasuresLimits
