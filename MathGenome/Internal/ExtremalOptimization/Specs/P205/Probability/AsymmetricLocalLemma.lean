import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.LocalLemmaConditionals

open MeasureTheory
open scoped BigOperators Classical

universe u v

namespace Specs.P205.Probability

/-- The full finite asymmetric local lemma (Theorem 6.2, p205:W28).
The parameters may be zero, and the finite index type may be empty. -/
def AsymmetricLocalLemmaType : Prop :=
  ∀ {I : Type u} [Fintype I] {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (D : SimpleGraph I)
    (x : I → ℝ),
    IsDependencyGraphValue μ A D →
    (∀ i, 0 ≤ x i ∧ x i < 1) →
    (∀ i, μ.real (A i) ≤ x i *
      ∏ j ∈ Finset.univ.filter (D.Adj i), (1 - x j)) →
    (∏ i, (1 - x i)) ≤ μ.real (⋂ i, (A i)ᶜ) ∧
      0 < ∏ i, (1 - x i)

end Specs.P205.Probability
