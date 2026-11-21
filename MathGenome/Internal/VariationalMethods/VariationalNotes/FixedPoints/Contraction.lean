import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.Contraction

namespace VariationalNotes.FixedPoints

universe u

/-- Banach's contraction principle, including the quantitative convergence
estimate for every starting point. -/
theorem banach_contraction : Specs.VariationalNotes.FixedPoints.BanachContraction.{u} := by
  intro M _ _ _ q T hq0 hq1 hT
  let K : NNReal := ⟨q, hq0⟩
  have hK_real : (K : ℝ) = q := rfl
  have hK : ContractingWith K T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · change q < 1
      exact hq1
    · intro x y
      exact hT x y
  refine ⟨hK.fixedPoint T, hK.fixedPoint_isFixedPt, ?_, ?_⟩
  · intro y hy
    exact hK.fixedPoint_unique hy
  · intro x0
    refine ⟨hK.tendsto_iterate_fixedPoint x0, ?_⟩
    intro n
    simpa only [hK_real, mul_comm (dist x0 (T x0))] using
      hK.apriori_dist_iterate_fixedPoint_le x0 n

end VariationalNotes.FixedPoints
