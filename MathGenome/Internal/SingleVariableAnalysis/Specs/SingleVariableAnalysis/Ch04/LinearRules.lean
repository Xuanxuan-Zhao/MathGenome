import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Independent specification of K03.04.linear_rules, paper.tex:670–682.
The normed real algebra formulation specializes to both canonical scalar
fields ℝ and ℂ. All inputs and increments are real. A finite set permits
arbitrary finite families, including the empty family. The interior-domain
version uses the upstream ambient-extension representation of functions on I.
-/

namespace Specs.SingleVariableAnalysis.Ch04.LinearRules

open scoped BigOperators
universe u v

def incrementDerivativeLinearCombination : Prop :=
  ∀ {K : Type u} [NormedField K] [NormedAlgebra ℝ K]
    {ι : Type v} (s : Finset ι) (f : ι → ℝ → K) (L c : ι → K) (a : ℝ),
    (∀ j ∈ s, Derivative.hasRealIncrementDerivativeValue (f j) (L j) a) →
    Derivative.hasRealIncrementDerivativeValue
      (fun x => ∑ j ∈ s, c j * f j x) (∑ j ∈ s, c j * L j) a

def derivLinearCombination : Prop :=
  ∀ {K : Type u} [NormedField K] [NormedAlgebra ℝ K]
    {ι : Type v} (s : Finset ι) (f : ι → ℝ → K) (c : ι → K) (a : ℝ),
    (∀ j ∈ s, DifferentiableAt ℝ (f j) a) →
    deriv (fun x => ∑ j ∈ s, c j * f j x) a = ∑ j ∈ s, c j * deriv (f j) a

def withinDerivativeLinearCombination : Prop :=
  ∀ {K : Type u} [NormedField K] [NormedAlgebra ℝ K]
    {ι : Type v} (s : Finset ι) (f : ι → ℝ → K) (L c : ι → K)
    (I : Set ℝ) (a : ℝ), a ∈ interior I →
    (∀ j ∈ s, Derivative.hasRealIncrementDerivativeWithinValue (f j) (L j) I a) →
    Derivative.hasRealIncrementDerivativeWithinValue
      (fun x => ∑ j ∈ s, c j * f j x) (∑ j ∈ s, c j * L j) I a

def incrementDerivativeConst : Prop :=
  ∀ {K : Type u} [NormedField K] [NormedAlgebra ℝ K] (c : K) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue (fun _ => c) 0 a

def incrementDerivativeId : Prop :=
  ∀ a : ℝ, Derivative.hasRealIncrementDerivativeValue (fun x : ℝ => x) 1 a

end Specs.SingleVariableAnalysis.Ch04.LinearRules
