import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CylinderFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel

/-! Independent specification of `paper.tex`, Theorem `thm:kolmogorov-extension`.
The Pi measurable structure is the cylinder sigma-algebra by the upstream
`CylinderSigmaEqPi` theorem. No completion or nonemptiness hypothesis is imposed.
The family includes the law on the empty finite product.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch05.KolmogorovExtension

open _root_.ProbabilityFoundations.Ch05.CylinderFramework

universe u v

/-- Every consistent family of finite-dimensional probabilities on standard
Borel factors, with arbitrary index type, has exactly one probability extension. -/
def Extension : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)],
    (∀ i, _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue (S i)) →
    ∀ μ : FiniteLaws S, IsProbabilityFamily S μ → Consistent S μ →
      ∃! ν : Measure (ProductSpace S), IsProbabilityMeasure ν ∧
        ∀ F : Finset I, ν.map (finiteProjection S F) = μ F

end Specs.ProbabilityFoundations.Ch05.KolmogorovExtension
