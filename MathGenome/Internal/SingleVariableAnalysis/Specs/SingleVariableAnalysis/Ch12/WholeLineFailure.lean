import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction

/-!
Independent specification of K03.12.whole_line_failure, paper.tex:1339–1347.
P_N(x) is the existing inclusive partial sum of x^n/n!, with indices 0,…,N.
The exponential is the real series constructed in Ch07; no new exponential
or convergence predicate is introduced. The error lower bound applies at
all nonnegative x and every N, including N=0. Unboundedness means that
every real bound is exceeded at some nonnegative argument.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch12.WholeLineFailure
open Ch11.PartialSums Ch07.ExpConstruction Ch12.Uniform

def uniformInterval : Prop :=
  ∀ A : ℝ, 0 < A → realUniformConvergesValue
    (fun N (x : Set.Icc (-A) A) =>
      realPartialSumValue (fun n => (x : ℝ)^n / (n.factorial : ℝ)) N)
    (fun x => realSeriesExpValue x)

def remainderLower : Prop :=
  ∀ (N : ℕ) (x : ℝ), 0 ≤ x →
    x^(N+1) / ((N+1).factorial : ℝ) ≤
      realSeriesExpValue x - realPartialSumValue (fun n => x^n / (n.factorial : ℝ)) N

def errorUnbounded : Prop :=
  ∀ (N : ℕ) (B : ℝ), ∃ x : ℝ, 0 ≤ x ∧
    B < realSeriesExpValue x - realPartialSumValue (fun n => x^n / (n.factorial : ℝ)) N

def notUniform : Prop :=
  ¬ realUniformConvergesValue
    (fun N (x : ℝ) => realPartialSumValue (fun n => x^n / (n.factorial : ℝ)) N)
    realSeriesExpValue

end Specs.SingleVariableAnalysis.Ch12.WholeLineFailure
