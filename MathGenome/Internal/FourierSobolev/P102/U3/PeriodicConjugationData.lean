import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationData

/-! Defining equations for the shared periodic-conjugation data.
The analytic principal-value and norm estimates are separate obligations. -/

noncomputable section

namespace P102.Periodic.Conjugation

/-- The shared data have the manuscript's multiplier, normalization, and
ordinary symmetric truncation formulas. -/
theorem data_formulas : Expected.DataFormulas := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro T c x
    simp only [polynomialAction, Finsupp.linearCombination_apply, Finsupp.sum,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  · intro T t
    simp only [coordinateKernel, one_div]
  · intro T ε f x
    rfl
  · intro T f x
    rfl

end P102.Periodic.Conjugation
