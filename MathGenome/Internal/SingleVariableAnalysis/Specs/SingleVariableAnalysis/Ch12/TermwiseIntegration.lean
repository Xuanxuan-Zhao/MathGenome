import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-!
Independent statements of K03.12.termwise_integration (paper.tex:1305–1316).
The hypothesis is uniform convergence of the inclusive partial sums on [a,b].
The conclusion supplies Darboux integrability of the limit and identifies its
integral as the ordinary sum of the series of integrals, using Chapter 11's
ordered-partial-sum predicate. Thus numerical convergence is a conclusion.
Both scalar choices and the singleton interval are included. Integrability,
continuity, or absolute convergence of the sum is not assumed.
-/
namespace Specs.SingleVariableAnalysis.Ch12.TermwiseIntegration
open scoped BigOperators

def realTermwiseIntegration : Prop :=
  ∀ (u : ℕ → ℝ → ℝ) (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    (hu : ∀ n, Ch08.Integral.realIntegrableValue (u n) a b) →
    Uniform.realUniformConvergesValue
      (fun N (x : Set.Icc a b) => Ch11.PartialSums.realPartialSumValue (fun n => u n x) N)
      (fun x => f x) →
    ∃ hf : Ch08.Integral.realIntegrableValue f a b,
      Ch11.PartialSums.realSeriesHasSumValue
        (fun n => Ch08.Integral.realIntegralValue (u n) (hu n))
        (Ch08.Integral.realIntegralValue f hf)

def complexTermwiseIntegration : Prop :=
  ∀ (u : ℕ → ℝ → ℂ) (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (hu : ∀ n, Ch08.Integral.complexIntegrableValue (u n) a b) →
    Uniform.complexUniformConvergesValue
      (fun N (x : Set.Icc a b) => Ch11.PartialSums.complexPartialSumValue (fun n => u n x) N)
      (fun x => f x) →
    ∃ hf : Ch08.Integral.complexIntegrableValue f a b,
      Ch11.PartialSums.complexSeriesHasSumValue
        (fun n => Ch08.Integral.complexIntegralValue (u n) (hu n))
        (Ch08.Integral.complexIntegralValue f hf)

end Specs.SingleVariableAnalysis.Ch12.TermwiseIntegration
