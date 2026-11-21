import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.AsymmetricLocalLemma
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory
open scoped BigOperators Classical

universe u v

namespace Specs.P205.Probability

/-- Corollary 6.3 (p205:W29): the finite symmetric local lemma. The degree
bound is the number of neighbors in the simple graph. Zero bounds and empty
index types are included. -/
def SymmetricLocalLemmaType : Prop :=
  ∀ {I : Type u} [Fintype I] {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (D : SimpleGraph I)
    (d : ℕ) (p : ℝ),
    IsDependencyGraphValue μ A D →
    (∀ i, (Finset.univ.filter (D.Adj i)).card ≤ d) →
    0 ≤ p →
    (∀ i, μ.real (A i) ≤ p) →
    Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1 →
    0 < μ.real (⋂ i, (A i)ᶜ)

end Specs.P205.Probability
