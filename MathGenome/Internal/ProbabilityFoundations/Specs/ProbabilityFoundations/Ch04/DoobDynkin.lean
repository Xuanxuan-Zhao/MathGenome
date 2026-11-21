import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel

/-! Independent specification of the first assertion of Theorem 4.2
(`thm:doob-dynkin`) in paper.tex, §4.1. The domain is just a type;
its measurable structure in the hypothesis is exactly the pullback along `X`.
The target has the source's standard Borel property for its specified sigma-algebra. -/

namespace ProbabilityFoundations.Ch04.Specs

open scoped MeasureTheory

universe u v w

/-- Pointwise measurable factorization, without a probability measure, a
surjectivity assumption, or a standard Borel assumption on the intermediate space. -/
def DoobDynkinFactorization : Prop :=
  ∀ (Ω : Type u) (S : Type v) (T : Type w)
    [mS : MeasurableSpace S] [MeasurableSpace T] [Nonempty T],
    StandardBorelValue T → ∀ (X : Ω → S) (Y : Ω → T),
    Measurable[mS.comap X] Y →
      ∃ g : S → T, Measurable g ∧ ∀ ω : Ω, Y ω = g (X ω)

end ProbabilityFoundations.Ch04.Specs
