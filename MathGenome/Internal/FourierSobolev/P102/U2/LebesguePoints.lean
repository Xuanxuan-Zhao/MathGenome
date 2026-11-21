import MathGenome.Internal.FourierSobolev.Specs.P102.U2.LebesguePoints
import MathGenome.Internal.RealAnalysis.D11.Ch13.LebesgueDifferentiation

/-! Lebesgue points for locally integrable measurable representatives,
including all containing-ball families at each such point. The library's
measure, local integrability, averages and Lebesgue-point predicate are
definitionally the canonical objects used in the independent specification. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
universe u
namespace P102.U2.LebesguePoints

local instance (d : ℕ) [NeZero d] : MeasurableSpace (D11.Ch03.Point d) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d

theorem ae_lebesguePoint : Specs.P102.U2.LebesguePoints.ae_lebesguePoint := by
  intro d _ 𝕜 _ _ _ f hf
  exact D11.Ch13.LebesgueDifferentiation.ae_lebesguePoint f hf

theorem average_tendsto_of_lebesguePoint :
    Specs.P102.U2.LebesguePoints.average_tendsto_of_lebesguePoint := by
  intro d _ 𝕜 _ _ _ f hf x hx
  exact D11.Ch13.LebesgueDifferentiation.average_tendsto_of_lebesguePoint f hf hx

theorem containing_balls_tendsto :
    Specs.P102.U2.LebesguePoints.containing_balls_tendsto.{u} := by
  intro d _ 𝕜 _ _ _ f hf x hx ι l z r hr hxball
  exact D11.Ch13.LebesgueDifferentiation.containing_balls_tendsto f hf hx z r hr hxball

theorem lebesgue_differentiation :
    Specs.P102.U2.LebesguePoints.lebesgue_differentiation.{u} := by
  intro d _ 𝕜 _ _ _ f hf
  obtain ⟨N, hsub, hN, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (ae_lebesguePoint f hf))
  refine ⟨N, hN, hnull, ?_⟩
  intro x hx
  have hp : Specs.D11.Ch13.AveragesMaximalDefinition.lebesguePoint_value f hf x := by
    by_contra h
    exact hx (hsub h)
  refine ⟨hp, average_tendsto_of_lebesguePoint f hf hp, ?_⟩
  intro ι l z r hr hxball
  exact containing_balls_tendsto f hf hp z r hr hxball

end P102.U2.LebesguePoints
