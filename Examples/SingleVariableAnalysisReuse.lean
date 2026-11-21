import MathGenome
import Examples.AbstractAlgebraReuse

/-! Actual downstream uses of new analysis and preserved algebra interfaces. -/
namespace MathGenome.SingleVariableAnalysisExamples

theorem fejer_zero (t : ℝ) : SingleVariableAnalysis.fejerKernel 0 t = 1 := by
  simpa [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue] using
    SingleVariableAnalysis.fejerKernel_normSquare 0 t

theorem continuous_variation (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Specs.SingleVariableAnalysis.Ch15.Variation.boundedVariationValue f a b)
    (hc : ContinuousOn f (Set.Icc a b)) :
    ContinuousOn (fun x => (SingleVariableAnalysis.BV.totalVariation f a x).toReal)
      (Set.Icc a b) :=
  SingleVariableAnalysis.BV.continuousOn_totalVariation f hab hf hc

theorem preserved_algebra (p : ℕ) (hp : p.Prime) :
    Irreducible ((Polynomial.X : Polynomial ℚ)^3 - Polynomial.C (p : ℚ)) :=
  MathGenome.AbstractAlgebraExamples.eisenstein_prime_cube p hp

end MathGenome.SingleVariableAnalysisExamples
