import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.UniformContinuity
import Mathlib.Analysis.Real.Sqrt

/-!
Independent propositions for K03.03.counterexamples, paper.tex:627–634.
All domains have the usual real metric. Natural indices in the displayed
witness formulae start at one, as in the manuscript. The limits ignore the
irrelevant zeroth term. The square-root obstruction rules out even a bound
against the value at zero on any relative neighborhood of zero.
-/
namespace Specs.SingleVariableAnalysis.Ch03.Counterexamples

open scoped Topology
open Specs.SingleVariableAnalysis.Ch03.Continuity
open Specs.SingleVariableAnalysis.Ch03.UniformContinuity

def reciprocalContinuous : Prop :=
  relativeContinuousValue (fun x : ℝ => 1 / x) (Set.Ioo 0 1)

def reciprocalUnbounded : Prop :=
  ∀ B : ℝ, ∃ x ∈ Set.Ioo (0 : ℝ) 1, B < |1 / x|

def reciprocalPairValues : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    1 / ((n : ℝ) + 1) ∈ Set.Ioo (0 : ℝ) 1 ∧
    1 / ((n : ℝ) + 2) ∈ Set.Ioo (0 : ℝ) 1 ∧
    dist (1 / (1 / ((n : ℝ) + 1))) (1 / (1 / ((n : ℝ) + 2))) = 1

def reciprocalPairDistanceLimit : Prop :=
  Filter.Tendsto
    (fun n : ℕ => dist (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 2)))
    Filter.atTop (𝓝 (0 : ℝ))

def reciprocalNotUniformContinuous : Prop :=
  ¬ relativeUniformContinuousValue (fun x : ℝ => 1 / x) (Set.Ioo 0 1)

def squareContinuous : Prop :=
  relativeContinuousValue (fun x : ℝ => x ^ 2) Set.univ

def squarePairValues : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    dist (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)) = 1 / (n : ℝ) ∧
    dist ((n : ℝ) ^ 2) (((n : ℝ) + 1 / (n : ℝ)) ^ 2) =
      2 + 1 / (n : ℝ) ^ 2

def squarePairDistanceLimit : Prop :=
  Filter.Tendsto (fun n : ℕ => dist (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)))
    Filter.atTop (𝓝 (0 : ℝ))

def squareNotUniformContinuous : Prop :=
  ¬ relativeUniformContinuousValue (fun x : ℝ => x ^ 2) Set.univ

def sqrtDifferenceSqLe : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    |Real.sqrt x - Real.sqrt y| ^ 2 ≤ |x - y|

def sqrtUniformContinuous : Prop :=
  relativeUniformContinuousValue Real.sqrt (Set.Icc (0 : ℝ) 1)

def sqrtNotLipschitzAtZero : Prop :=
  ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x < r →
      |Real.sqrt x - Real.sqrt 0| ≤ C * |x - 0|

def sqrtNotLipschitz : Prop :=
  ¬ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Real.sqrt x - Real.sqrt y| ≤ C * |x - y|

def stepBounded : Prop :=
  ∀ x : ℝ, |(if x < 0 then 0 else 1 : ℝ)| ≤ 1

def stepDiscontinuous : Prop :=
  ¬ relativeContinuousAtValue (fun x : ℝ => (if x < 0 then 0 else 1 : ℝ)) Set.univ 0

end Specs.SingleVariableAnalysis.Ch03.Counterexamples
