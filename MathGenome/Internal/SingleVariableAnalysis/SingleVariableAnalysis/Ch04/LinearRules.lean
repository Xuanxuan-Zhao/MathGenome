import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.LinearRules

/-!
# Finite linearity of the real-variable derivative

K03.04.linear_rules (paper.tex:670–682). We transport Mathlib's finite
sum and constant-multiplication rules through the proved real-increment
derivative bridge. The scalar target can be ℝ or ℂ; the differentiation
field is always ℝ. No continuity of the derivatives is required.
-/

namespace SingleVariableAnalysis

open scoped BigOperators
universe u v

theorem incrementDerivative_linear_combination
    {K : Type u} [NormedField K] [NormedAlgebra ℝ K]
    {ι : Type v} (s : Finset ι) (f : ι → ℝ → K) (L c : ι → K) (a : ℝ)
    (hf : ∀ j ∈ s, HasRealIncrementDerivative (f j) (L j) a) :
    HasRealIncrementDerivative (fun x => ∑ j ∈ s, c j * f j x)
      (∑ j ∈ s, c j * L j) a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  exact HasDerivAt.fun_sum fun j hj =>
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp (hf j hj)).const_mul (c j)

theorem deriv_linear_combination
    {K : Type u} [NormedField K] [NormedAlgebra ℝ K]
    {ι : Type v} (s : Finset ι) (f : ι → ℝ → K) (c : ι → K) (a : ℝ)
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) a) :
    deriv (fun x => ∑ j ∈ s, c j * f j x) a = ∑ j ∈ s, c j * deriv (f j) a := by
  exact (HasDerivAt.fun_sum fun j hj => (hf j hj).hasDerivAt.const_mul (c j)).deriv

theorem withinDerivative_linear_combination
    {K : Type u} [NormedField K] [NormedAlgebra ℝ K]
    {ι : Type v} (s : Finset ι) (f : ι → ℝ → K) (L c : ι → K)
    (I : Set ℝ) (a : ℝ) (ha : a ∈ interior I)
    (hf : ∀ j ∈ s, HasRealIncrementDerivativeWithin (f j) (L j) I a) :
    HasRealIncrementDerivativeWithin (fun x => ∑ j ∈ s, c j * f j x)
      (∑ j ∈ s, c j * L j) I a := by
  apply (withinDerivative_interior_iff _ _ I a ha).mpr
  exact HasDerivAt.fun_sum fun j hj =>
    ((withinDerivative_interior_iff _ _ I a ha).mp (hf j hj)).const_mul (c j)

theorem incrementDerivative_const
    {K : Type u} [NormedField K] [NormedAlgebra ℝ K] (c : K) (a : ℝ) :
    HasRealIncrementDerivative (fun _ => c) 0 a := by
  exact (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr (hasDerivAt_const a c)

theorem incrementDerivative_id (a : ℝ) :
    HasRealIncrementDerivative (fun x : ℝ => x) 1 a := by
  exact (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr (hasDerivAt_id' a)

end SingleVariableAnalysis
