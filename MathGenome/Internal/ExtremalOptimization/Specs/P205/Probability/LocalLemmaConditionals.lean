import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.DependencyGraph
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open MeasureTheory
open scoped BigOperators Classical

universe u v

namespace Specs.P205.Probability

/-- The simultaneous positivity and conditional estimate in the proof of W28.
The empty intersection is the whole sample space; no positivity assumption on
any avoidance event is made. -/
def LocalLemmaConditionalsType : Prop :=
  ∀ {I : Type u} [Fintype I] {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (D : SimpleGraph I)
    (x : I → ℝ),
    IsDependencyGraphValue μ A D →
    (∀ i, 0 ≤ x i ∧ x i < 1) →
    (∀ i, μ.real (A i) ≤ x i *
      ∏ j ∈ Finset.univ.filter (D.Adj i), (1 - x j)) →
    ∀ S : Finset I,
      0 < μ.real (⋂ j ∈ S, (A j)ᶜ) ∧
      ∀ i ∉ S, μ.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) /
        μ.real (⋂ j ∈ S, (A j)ᶜ) ≤ x i

end Specs.P205.Probability
