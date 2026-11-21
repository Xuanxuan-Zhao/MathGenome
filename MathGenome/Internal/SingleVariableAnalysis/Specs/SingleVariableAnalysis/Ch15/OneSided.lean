import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Jordan
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-! Independent specification of K03.15.one_sided (paper.tex:3602–3608).
The BV predicate is the upstream strict-partition predicate, which uses actual
values at every point of the closed interval. Finite limits have real values and
use the upstream relative one-sided definitions, including side accumulation.
The half-open ranges include precisely the available endpoint approaches.
Discontinuity means failure of continuity relative to the closed interval,
including its endpoints. Singleton intervals are allowed as well.
-/
namespace Specs.SingleVariableAnalysis.Ch15.OneSided

def finiteLeftLimits : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b →
    ∀ c ∈ Set.Ioc a b, ∃ L : ℝ,
      Ch02.OneSided.leftRelativeLimitValue f (Set.Icc a b) c L

def finiteRightLimits : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b →
    ∀ c ∈ Set.Ico a b, ∃ L : ℝ,
      Ch02.OneSided.rightRelativeLimitValue f (Set.Icc a b) c L

def countableDiscontinuities : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b →
    Set.Countable {c ∈ Set.Icc a b | ¬ ContinuousWithinAt f (Set.Icc a b) c}

end Specs.SingleVariableAnalysis.Ch15.OneSided
