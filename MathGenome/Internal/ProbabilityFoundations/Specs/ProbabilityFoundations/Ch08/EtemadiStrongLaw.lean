import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Intervals

/-! Independent specification of the forward direction of Theorem 8.3
(`thm:etemadi`, paper.tex:2789–2795). Indices start at one: `X 0` is
unconstrained and is absent from every hypothesis and partial sum.
`Integrable |X 1|` expresses the finite first absolute moment, on the
specified probability space, without completing its sigma-algebra. -/

open MeasureTheory Filter
open scoped Topology

namespace Specs.ProbabilityFoundations.Ch08.EtemadiStrongLaw

universe u

/-- Pairwise independence and identical laws with a finite first absolute
moment imply almost sure convergence of the one-based averages. -/
def etemadiStrongLawType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (_hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (_hindep : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.PairwiseIndependentRandomElementsValue P (fun k : ℕ => X (k + 1)))
    (_hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X (k + 1)) (X 1) P P)
    (_hmoment : Integrable (fun ω => |X 1 ω|) P),
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, X k ω) / (n : ℝ))
      atTop (𝓝 (∫ ω, X 1 ω ∂P))

end Specs.ProbabilityFoundations.Ch08.EtemadiStrongLaw
