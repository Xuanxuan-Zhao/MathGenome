import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of K03.12.termwise_differentiation, paper.tex:1314–1323.
Scalar targets are the canonical real and complex fields. Inputs and derivatives
are real. Every series is an ordinary limit of the inclusive partial sums
indexed from zero; no absolute or unconditional summability is assumed.
Ambient functions represent their restrictions to [a,b], and derivatives are
asserted only in (a,b). No derivative continuity or endpoint derivative is required.
The given g represents the uniform sum of the derivative series on (a,b).
-/

namespace Specs.SingleVariableAnalysis.Ch12.TermwiseDifferentiation

open Set

def realTermwiseDifferentiation : Prop :=
  ∀ (u : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (u n) (Icc a b)) →
    (∀ n, ∀ x ∈ Ioo a b, DifferentiableAt ℝ (u n) x) →
    Ch11.PartialSums.realSeriesConvergesValue (fun n => u n x₀) →
    Uniform.realUniformConvergesValue
      (fun N (x : Ioo a b) =>
        Ch11.PartialSums.realPartialSumValue (fun n => deriv (u n) x) N)
      (fun x => g x) →
    ∃ f : ℝ → ℝ,
      Uniform.realUniformConvergesValue
        (fun N (x : Icc a b) =>
          Ch11.PartialSums.realPartialSumValue (fun n => u n x) N)
        (fun x => f x) ∧
      ContinuousOn f (Icc a b) ∧
      (∀ x ∈ Icc a b, Ch11.PartialSums.realSeriesHasSumValue
        (fun n => u n x) (f x)) ∧
      ∀ x ∈ Ioo a b, HasDerivAt f (g x) x ∧
        Ch11.PartialSums.realSeriesHasSumValue (fun n => deriv (u n) x) (g x)

def complexTermwiseDifferentiation : Prop :=
  ∀ (u : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (u n) (Icc a b)) →
    (∀ n, ∀ x ∈ Ioo a b, DifferentiableAt ℝ (u n) x) →
    Ch11.PartialSums.complexSeriesConvergesValue (fun n => u n x₀) →
    Uniform.complexUniformConvergesValue
      (fun N (x : Ioo a b) =>
        Ch11.PartialSums.complexPartialSumValue (fun n => deriv (u n) x) N)
      (fun x => g x) →
    ∃ f : ℝ → ℂ,
      Uniform.complexUniformConvergesValue
        (fun N (x : Icc a b) =>
          Ch11.PartialSums.complexPartialSumValue (fun n => u n x) N)
        (fun x => f x) ∧
      ContinuousOn f (Icc a b) ∧
      (∀ x ∈ Icc a b, Ch11.PartialSums.complexSeriesHasSumValue
        (fun n => u n x) (f x)) ∧
      ∀ x ∈ Ioo a b, HasDerivAt f (g x) x ∧
        Ch11.PartialSums.complexSeriesHasSumValue (fun n => deriv (u n) x) (g x)

end Specs.SingleVariableAnalysis.Ch12.TermwiseDifferentiation
