import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The dominated part of Theorem 3.7, paper.tex 1007–1041.
All inputs are measurable for the original sigma algebra F. The probability
space and sub-sigma-algebra G are arbitrary, with no completeness assumption.
L¹ convergence is expressed by convergence of the integral of absolute error. -/

open MeasureTheory Filter
open scoped Topology

namespace Specs.ProbabilityFoundations.Ch03.ConditionalDominatedConvergence

open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

universe u

def dominatedConvergenceType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ),
      (∀ n, Measurable[F] (Xn n)) → Measurable[F] X → Measurable[F] Y →
      (∀ᵐ ω ∂P, 0 ≤ Y ω) → Integrable Y P →
      (∀ n, ∀ᵐ ω ∂P, |Xn n ω| ≤ Y ω) →
      (∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) →
      Integrable X P ∧ (∀ n, Integrable (Xn n) P) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => realConditionalExpectationValue G P (Xn n) ω)
        atTop (𝓝 (realConditionalExpectationValue G P X ω))) ∧
      Tendsto (fun n => ∫ ω, |realConditionalExpectationValue G P (Xn n) ω -
        realConditionalExpectationValue G P X ω| ∂P) atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch03.ConditionalDominatedConvergence
