import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.FixedPointErrorBounds
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.Banach

/-! A priori and a posteriori bounds (paper.tex, Proposition p206:W69). -/

universe u

namespace NumAnalysis206.Iterations

/-- Both error bounds hold at every index, including zero, for every initial point. -/
theorem fixedPointErrorBounds :
    Specs.NumAnalysis206.Iterations.FixedPointErrorBoundsStatement.{u} := by
  intro X _ _ _ T q hq₀ hq₁ hT p hp x₀ n
  let K : NNReal := .mk q hq₀
  have hK : ContractingWith K T :=
    ⟨hq₁, LipschitzWith.of_dist_le_mul hT⟩
  have hpK : p = hK.fixedPoint T := hK.fixedPoint_unique hp
  rw [hpK]
  constructor
  · simpa only [K, NNReal.coe_mk, dist_comm x₀ (T x₀), mul_comm] using
      hK.apriori_dist_iterate_fixedPoint_le x₀ n
  · simpa only [K, NNReal.coe_mk, dist_comm (T^[n] x₀) (T^[n + 1] x₀)] using
      hK.aposteriori_dist_iterate_fixedPoint_le x₀ n

end NumAnalysis206.Iterations
