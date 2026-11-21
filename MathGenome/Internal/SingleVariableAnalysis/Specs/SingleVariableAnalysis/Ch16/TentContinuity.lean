import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification for the continuity part of K03.16.nowhere_differentiable
(paper.tex:3958–3971). The quotient norm is distance to the even integers.
The period and base-interval theorems identify it with the specified extension.
The two cell formulas include endpoints and cover all consecutive integer cells;
the general affine assertion also records this without a parity convention.
The sum is the actual real tsum of the displayed terms, with ordinary inclusive
partial-sum convergence proved separately, uniformly on the entire real line.
-/

namespace Specs.SingleVariableAnalysis.Ch16.TentContinuity

def periodicTentType : Type := ℝ → ℝ
noncomputable def periodicTentValue : periodicTentType :=
  fun x => ‖(x : AddCircle (2 : ℝ))‖

def periodicTentPeriod : Prop := Function.Periodic periodicTentValue 2

def periodicTentBase : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → periodicTentValue x = |x|

def periodicTentBounds : Prop :=
  ∀ x : ℝ, 0 ≤ periodicTentValue x ∧ periodicTentValue x ≤ 1

def periodicTentLipschitz : Prop :=
  ∀ s t : ℝ, |periodicTentValue s - periodicTentValue t| ≤ |s - t|

def periodicTentContinuous : Prop := Continuous periodicTentValue

def periodicTentEvenCell : Prop :=
  ∀ (k : ℤ) (x : ℝ), 2 * (k : ℝ) ≤ x → x ≤ 2 * (k : ℝ) + 1 →
    periodicTentValue x = x - 2 * (k : ℝ)

def periodicTentOddCell : Prop :=
  ∀ (k : ℤ) (x : ℝ), 2 * (k : ℝ) + 1 ≤ x → x ≤ 2 * (k : ℝ) + 2 →
    periodicTentValue x = 2 * (k : ℝ) + 2 - x

def periodicTentAffine : Prop :=
  ∀ k : ℤ, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
    ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
      periodicTentValue x = periodicTentValue k + a * (x - k)

def tentSeriesTermType : Type := ℕ → ℝ → ℝ
noncomputable def tentSeriesTermValue : tentSeriesTermType :=
  fun n x => (3 / 4 : ℝ) ^ n * periodicTentValue ((4 : ℝ) ^ n * x)

def tentSeriesType : Type := ℝ → ℝ
noncomputable def tentSeriesValue : tentSeriesType :=
  fun x => ∑' n : ℕ, tentSeriesTermValue n x

def tentSeriesSummable : Prop := ∀ x : ℝ, Summable (fun n => tentSeriesTermValue n x)

def tentSeriesUniform : Prop :=
  Ch12.Uniform.realUniformConvergesValue
    (fun N x => Ch11.PartialSums.realPartialSumValue (fun n => tentSeriesTermValue n x) N)
    tentSeriesValue

def tentSeriesContinuous : Prop := Continuous tentSeriesValue

end Specs.SingleVariableAnalysis.Ch16.TentContinuity
