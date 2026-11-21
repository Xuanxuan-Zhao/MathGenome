import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.SumCondition

namespace NumAnalysis206.Rounding.SumCondition

open scoped BigOperators

/-- Linearity identifies the exact change with the sum of the perturbations. -/
theorem sumChange_eq {n : ℕ} (x δ : Fin n → ℝ) :
    sumChange x δ = ∑ i, δ i := by
  simp [sumChange, exactSum, Finset.sum_add_distrib]

/-- Triangle inequality with the componentwise bounds; no nonzero scale is needed. -/
theorem absolute_bound : SumConditionSpecs.absoluteBound := by
  intro n x ε _ δ hδ
  rw [sumChange_eq]
  calc
    |∑ i, δ i| ≤ ∑ i, |δ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * |x i| := Finset.sum_le_sum (fun i _ => hδ i)
    _ = ε * sumMagnitude x := (Finset.mul_sum _ _ _).symm

/-- The perturbation specified in the source is feasible and attains the bound. -/
theorem aligned_attains : SumConditionSpecs.alignedAttains := by
  intro n x ε hε
  have hnonneg (i : Fin n) : 0 ≤ ε * |x i| := mul_nonneg hε (abs_nonneg _)
  constructor
  · intro i
    exact le_of_eq (abs_of_nonneg (hnonneg i))
  · rw [sumChange_eq]
    change |∑ i, (ε * |x i|)| = ε * sumMagnitude x
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => hnonneg i))]
    exact (Finset.mul_sum _ _ _).symm

/-- The absolute bound is a maximum, including zero budgets and zero exact sums. -/
theorem absolute_maximum : SumConditionSpecs.absoluteMaximum := by
  intro n x ε hε
  obtain ⟨hfeasible, hattains⟩ := aligned_attains x ε hε
  refine ⟨⟨alignedPerturbation x ε, hfeasible, hattains.symm⟩, ?_⟩
  rintro a ⟨δ, hδ, rfl⟩
  exact absolute_bound x ε hε δ hδ

/-- Normalization of the attained maximum for every positive input budget. -/
theorem relative_maximum : SumConditionSpecs.relativeMaximum := by
  intro n x hs ε hε
  have hden : 0 < ε * |exactSum x| := mul_pos hε (abs_pos.mpr hs)
  have hcancel : (ε * sumMagnitude x) / (ε * |exactSum x|) =
      sumMagnitude x / |exactSum x| := mul_div_mul_left _ _ (ne_of_gt hε)
  obtain ⟨hfeasible, hattains⟩ := aligned_attains x ε hε.le
  refine ⟨⟨alignedPerturbation x ε, hfeasible, ?_⟩, ?_⟩
  · rw [hattains, hcancel]
  · rintro r ⟨δ, hδ, rfl⟩
    calc
      |sumChange x δ| / (ε * |exactSum x|) ≤
          (ε * sumMagnitude x) / (ε * |exactSum x|) :=
        div_le_div_of_nonneg_right (absolute_bound x ε hε.le δ hδ) hden.le
      _ = sumMagnitude x / |exactSum x| := hcancel

/-- Thus the componentwise relative condition number has the source's formula. -/
theorem condition_formula : SumConditionSpecs.conditionFormula := by
  intro n x hs
  exact (relative_maximum x hs 1 zero_lt_one).csSup_eq

/-- The zero-sum case is stated without any relative division. -/
theorem zero_sum_maximum : SumConditionSpecs.zeroSumMaximum := by
  intro n x hs ε hε
  refine ⟨absolute_maximum x ε hε, (aligned_attains x ε hε).1, ?_⟩
  simpa [sumChange, hs] using (aligned_attains x ε hε).2

end NumAnalysis206.Rounding.SumCondition
