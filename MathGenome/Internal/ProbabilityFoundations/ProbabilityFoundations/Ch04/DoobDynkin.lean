import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.DoobDynkin
import Mathlib.MeasureTheory.Function.FactorsThrough

namespace ProbabilityFoundations.Ch04

open scoped MeasureTheory

universe u v w

/-- The first assertion of Theorem 4.2: a map measurable for the pullback
sigma-algebra factors pointwise through `X` by a measurable map. -/
theorem doob_dynkin (Ω : Type u) (S : Type v) (T : Type w)
    [mS : MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (hT : IsStandardBorel T) (X : Ω → S) (Y : Ω → T)
    (hY : Measurable[mS.comap X] Y) :
    ∃ g : S → T, Measurable g ∧ ∀ ω : Ω, Y ω = g (X ω) := by
  let : StandardBorelSpace T := (isStandardBorel_iff T).mp hT
  obtain ⟨g, hg, h⟩ := hY.exists_eq_measurable_comp
  exact ⟨g, hg, fun ω ↦ congrFun h ω⟩

end ProbabilityFoundations.Ch04
