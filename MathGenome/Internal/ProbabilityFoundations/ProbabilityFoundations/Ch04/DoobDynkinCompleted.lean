import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.DoobDynkin
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.CompletedMeasurableVersions
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.DoobDynkinCompleted

namespace ProbabilityFoundations.Ch04

open MeasureTheory

universe u v w

/-- The completion assertion of Theorem 4.2. First choose an original
measurable version, then factor that version pointwise through `X`.
The version's original measurable null set supports the final agreement. -/
theorem doob_dynkin_completed : Specs.DoobDynkinCompletedFactorization.{u, v, w} := by
  intro Ω S T mS mT _ hT X Y
  let : MeasurableSpace Ω := mS.comap X
  intro P _ hY
  let : StandardBorelSpace T := (isStandardBorel_iff T).mp hT
  obtain ⟨Y0, hY0, hEq, N, hN, hzero, houtside⟩ :=
    Ch01.completed_measurable_version P Y hY
  obtain ⟨g, hg, hfactor⟩ := doob_dynkin Ω S T hT X Y0 hY0
  refine ⟨g, hg, ?_, N, hN, hzero, ?_⟩
  · exact hEq.mono (fun ω hω ↦ hω.trans (hfactor ω))
  · intro ω hω
    exact (houtside ω hω).symm.trans (hfactor ω)

end ProbabilityFoundations.Ch04
