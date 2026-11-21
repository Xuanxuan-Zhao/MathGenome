import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy

/-!
Independent specification of paper.tex, lines 3410–3419.
The real lower bound excludes `-∞`, so `F` has exactly the source's range
`(-∞,+∞]`. Properness means it is not identically `+∞`.
-/
namespace Specs.ExpandedFA.P1

/-- Ekeland's variational principle, including the quantitative distance bound. -/
def Ekeland : Prop :=
  ∀ {X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : X → EReal),
    LowerSemicontinuous F →
    (∃ b : ℝ, ∀ x, (b : EReal) ≤ F x) →
    (∃ x, F x ≠ ⊤) →
    ∀ (x₀ : X) (α r : ℝ), 0 < α → 0 < r →
      F x₀ ≤ (⨅ x, F x) + ((α * r : ℝ) : EReal) →
      ∃ z : X, dist z x₀ ≤ r ∧ F z ≤ F x₀ ∧
        ∀ y : X, y ≠ z → F z - ((α * dist y z : ℝ) : EReal) < F y

end Specs.ExpandedFA.P1
