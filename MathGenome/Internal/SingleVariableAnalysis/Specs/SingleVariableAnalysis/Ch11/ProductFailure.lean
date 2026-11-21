import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import Mathlib.Analysis.Real.Sqrt

/-!
Independent specification of K03.11.product_failure (paper.tex:1123–1130).
Both factors are exactly (-1)^n / sqrt(n+1), n ≥ 0. The product coefficient
is the inclusive Cauchy convolution. Convergence is ordinary ordered
partial-sum convergence, including in the definition of absolute convergence.
-/

namespace Specs.SingleVariableAnalysis.Ch11.ProductFailure

open PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open scoped BigOperators

def factorType : Type := ℕ → ℝ
noncomputable def factorAValue : factorType :=
  fun n => (-1 : ℝ) ^ n / Real.sqrt ((n : ℝ) + 1)
noncomputable def factorBValue : factorType := factorAValue
noncomputable def productValue : factorType :=
  fun n => ∑ k ∈ Finset.range (n + 1), factorAValue k * factorBValue (n - k)

def factorsConditional : Prop :=
  (realSeriesConvergesValue factorAValue ∧
    ¬ realSeriesConvergesValue (fun n => |factorAValue n|)) ∧
  (realSeriesConvergesValue factorBValue ∧
    ¬ realSeriesConvergesValue (fun n => |factorBValue n|))

def productMagnitude : Prop := ∀ n : ℕ,
  |productValue n| = ∑ k ∈ Finset.range (n + 1),
    1 / Real.sqrt (((k : ℝ) + 1) * ((n - k : ℕ) + 1 : ℝ))

def productLowerBound : Prop := ∀ n : ℕ,
  2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ |productValue n| ∧
    1 ≤ 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2)

def productTermNotZeroLimit : Prop :=
  ¬ realSequenceConvergesValue productValue 0

def productDiverges : Prop := realSeriesDivergesValue productValue

end Specs.SingleVariableAnalysis.Ch11.ProductFailure
