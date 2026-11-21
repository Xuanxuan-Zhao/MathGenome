import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.D04.C01.TopologicalTests
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.Contraction
import Mathlib.Topology.MetricSpace.Contracting

/-! The contraction principle on a complete Euclidean subset, with a priori
and residual error bounds. The Banach theorem is applied to the subtype with
its induced metric. The nonnegative real constant is packaged as an NNReal;
no strict positivity is required, so this includes `q = 0` and `q ^ 0 = 1`.
-/

open Set Filter Topology
namespace D04

theorem contraction_principle {n : ℕ} (S : Set (E n))
    (hS : IsComplete S) (hne : S.Nonempty) (T : S → S) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hT : ∀ x y : S, ‖(T x : E n) - (T y : E n)‖ ≤
      q * ‖(x : E n) - (y : E n)‖) :
    ∃ xStar : S,
      T xStar = xStar ∧
      (∀ y : S, T y = y → y = xStar) ∧
      (∀ x₀ : S,
        Tendsto (fun j : ℕ => (T^[j] x₀ : E n)) atTop (𝓝 (xStar : E n)) ∧
        ∀ j : ℕ, ‖(T^[j] x₀ : E n) - (xStar : E n)‖ ≤
          q ^ j / (1 - q) * ‖(T x₀ : E n) - (x₀ : E n)‖) ∧
      (∀ x : S, ‖(x : E n) - (xStar : E n)‖ ≤
        ‖(x : E n) - (T x : E n)‖ / (1 - q)) := by
  let : Nonempty S := hne.to_subtype
  let : CompleteSpace S := hS.completeSpace_coe
  let K : NNReal := NNReal.mk q hq₀
  have hc : ContractingWith K T := by
    refine ⟨hq₁, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [Subtype.dist_eq, dist_eq_norm, K, NNReal.coe_mk] using hT x y
  refine ⟨hc.fixedPoint T, hc.fixedPoint_isFixedPt, ?_, ?_, ?_⟩
  · intro y hy
    exact hc.fixedPoint_unique hy
  · intro x₀
    refine ⟨continuous_subtype_val.continuousAt.tendsto.comp
      (hc.tendsto_iterate_fixedPoint x₀), ?_⟩
    intro j
    have hb := hc.apriori_dist_iterate_fixedPoint_le x₀ j
    simpa only [Subtype.dist_eq, dist_eq_norm, K, NNReal.coe_mk, norm_sub_rev,
      mul_div_assoc, div_mul_eq_mul_div, mul_comm] using hb
  · intro x
    simpa only [Subtype.dist_eq, dist_eq_norm, K, NNReal.coe_mk] using hc.dist_fixedPoint_le x

/-- Closed Euclidean subsets are complete, including the empty set. -/
theorem closed_set_complete {n : ℕ} (S : Set (E n)) (hS : Closed S) :
    IsComplete S := by
  let : CompleteSpace (E n) := euclidean_complete n
  exact ((closed_iff_isClosed S).mp hS).isComplete

/-- In particular, every closed ball is complete. Nonpositive radii and
zero-dimensional spaces require no exception to the statement. -/
theorem closed_ball_complete {n : ℕ} (a : E n) (r : ℝ) :
    IsComplete {x : E n | ‖x - a‖ ≤ r} := by
  apply closed_set_complete
  apply (closed_iff_isClosed _).mpr
  simpa only [Metric.closedBall, dist_eq_norm] using
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall a r))

end D04
