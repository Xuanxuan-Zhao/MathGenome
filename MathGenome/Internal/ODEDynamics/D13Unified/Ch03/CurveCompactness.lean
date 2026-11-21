import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.CurveCompactness
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

namespace D13Unified.Ch03

/-- Uniformly bounded equicontinuous curves on a compact real interval
have a subsequence converging uniformly to a continuous curve. -/
theorem curve_compactness : Specs.D13Unified.Ch03.curveCompactness := by
  intro n a b u hbounded hequi
  obtain ⟨M, hM⟩ := hbounded
  -- Equicontinuity supplies the continuity needed to enter the space of
  -- bounded continuous functions, whose metric is uniform convergence.
  let F : ℕ → BoundedContinuousFunction (Set.Icc a b) (EuclideanSpace ℝ (Fin n)) :=
    fun k => BoundedContinuousFunction.mkOfCompact ⟨u k, hequi.continuous k⟩
  have hFequi : Equicontinuous
      ((↑) : Set.range F → Set.Icc a b → EuclideanSpace ℝ (Fin n)) := by
    intro x U hU
    filter_upwards [hequi x U hU] with y hy
    rintro ⟨f, k, rfl⟩
    exact hy k
  -- Heine--Borel is used only in the finite-dimensional target: the common
  -- closed ball containing every curve value is compact.
  have hcompact : IsCompact (closure (Set.range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 M)
      (isCompact_closedBall 0 M) (Set.range F)
      (by
        intro f t hf
        obtain ⟨k, rfl⟩ := hf
        change dist (u k t) 0 ≤ M
        simpa only [dist_zero_right] using hM k t)
      hFequi
  obtain ⟨v, _, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq (fun k => subset_closure (Set.mem_range_self k))
  refine ⟨φ, v, hφ, v.continuous, ?_⟩
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim

end D13Unified.Ch03
