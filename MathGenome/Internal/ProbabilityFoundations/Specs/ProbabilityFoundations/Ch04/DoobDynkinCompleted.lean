import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Independent specification of the completion assertion of Theorem 4.2
(`thm:doob-dynkin`, paper.tex:1105–1112).

The probability is on the original pullback sigma-algebra `σ(X)`, as is
the exceptional null set. In particular, this includes the restriction of
an ambient probability to `σ(X)`. Only the measurability hypothesis for `Y`
uses its completion. No measurable structure on `Ω` beyond `σ(X)`, and no
regularity or surjectivity assumption on `S` or `X`, is imposed. -/

namespace ProbabilityFoundations.Ch04.Specs

open MeasureTheory

universe u v w

/-- Completed-measurable maps into a nonempty standard Borel space factor
almost surely through `X`, with one original measurable null exception. -/
def DoobDynkinCompletedFactorization : Prop :=
  ∀ (Ω : Type u) (S : Type v) (T : Type w)
    [mS : MeasurableSpace S] [MeasurableSpace T] [Nonempty T],
    StandardBorelValue T → ∀ (X : Ω → S) (Y : Ω → T),
    letI : MeasurableSpace Ω := mS.comap X
    ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      @Measurable (NullMeasurableSpace Ω P) T _ _ Y →
      ∃ g : S → T, Measurable g ∧ Y =ᵐ[P] (g ∘ X) ∧
        ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
          ∀ ω, ω ∉ N → Y ω = g (X ω)

end ProbabilityFoundations.Ch04.Specs
