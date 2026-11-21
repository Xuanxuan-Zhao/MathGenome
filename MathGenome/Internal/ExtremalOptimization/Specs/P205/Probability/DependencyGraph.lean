import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Independent specification of Definition 6.1 (p205:W27), paper.tex.
The generators are the events indexed by vertices outside the closed neighborhood.
`generateFrom` includes their complements and countable unions, not just the generators.
-/

open MeasureTheory

universe u v

namespace Specs.P205.Probability

/-- The interface for dependency graphs of finite event families on probability spaces. -/
def IsDependencyGraphType :=
  ∀ {I : Type u} [Finite I] {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ], (I → Set Ω) → SimpleGraph I → Prop

/-- Ambient measurability and independence from the entire nonneighbor sigma-algebra. -/
def IsDependencyGraphValue : IsDependencyGraphType.{u, v} :=
  fun {I} _ {Ω} _ μ _ A D =>
    (∀ i, MeasurableSet (A i)) ∧
    ∀ (i : I) (B : Set Ω),
      MeasurableSet[MeasurableSpace.generateFrom
        (A '' {j : I | j ≠ i ∧ ¬ D.Adj i j})] B →
      μ (A i ∩ B) = μ (A i) * μ B

end Specs.P205.Probability
