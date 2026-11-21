import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.Banach
import Mathlib.Topology.MetricSpace.Contracting

/-! Banach's fixed-point theorem (paper.tex, Theorem p206:W66). -/

universe u

namespace NumAnalysis206.Iterations

/-- A real `q`-contraction on a nonempty complete metric space has a unique
fixed point, and all its iterates converge to that point. -/
theorem banach : Specs.NumAnalysis206.Iterations.BanachStatement.{u} := by
  intro X _ _ _ T q hq₀ hq₁ hT
  -- Retain the real factor exactly when packaging it as a nonnegative real.
  let K : NNReal := ⟨q, hq₀⟩
  have hK : ContractingWith K T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul hT⟩
    exact hq₁
  refine ⟨hK.fixedPoint T, hK.fixedPoint_isFixedPt, ?_, ?_⟩
  · intro p' hp'
    exact hK.fixedPoint_unique hp'
  · intro x₀
    exact hK.tendsto_iterate_fixedPoint x₀

end NumAnalysis206.Iterations
