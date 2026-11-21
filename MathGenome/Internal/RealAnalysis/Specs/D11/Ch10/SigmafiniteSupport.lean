import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions

/-! Independent statements for paper.tex:3407–3416.
The positive integers `k ≥ 1` are indexed as `n + 1`, with `n : ℕ`.
Support means the literal nonzero set, rather than topological support or an
almost-everywhere replacement. The cover uses the original reference measure.
For real and complex scalars the norm below is absolute value and the Borel
instance is canonical. No condition on the size or completeness of `μ` occurs.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v

namespace Specs.D11.Ch10.SigmafiniteSupport

def support_eq_iUnion : Prop :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] (f : X → E),
    {x | f x ≠ 0} = ⋃ n : ℕ, {x | 1 / (n + 1 : ℝ) < ‖f x‖}

/-- Each set in the displayed cover has the stated finite quantitative bound. -/
def level_measure_bound : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (p : ℝ) (f : X → E),
    1 ≤ p → f ∈ LpDefinition.rawLp_value μ p → ∀ n : ℕ,
    MeasurableSet {x | 1 / (n + 1 : ℝ) < ‖f x‖} ∧
    μ {x | 1 / (n + 1 : ℝ) < ‖f x‖} ≤
      ENNReal.ofReal ((n + 1 : ℝ) ^ p) * (LpDefinition.powerNorm_value μ p f) ^ p ∧
    ENNReal.ofReal ((n + 1 : ℝ) ^ p) * (LpDefinition.powerNorm_value μ p f) ^ p < ∞

def sigmafinite_support : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (p : ℝ) (f : X → E),
    1 ≤ p → f ∈ LpDefinition.rawLp_value μ p →
    Specs.D11.Ch01.MeasureDefinitions.isSigmaFiniteSet_value μ {x | f x ≠ 0}

end Specs.D11.Ch10.SigmafiniteSupport
