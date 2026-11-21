import MathGenome.Internal.MultivariableAnalysis.D04.C01.EuclideanInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.DistanceFunction

/-! Distance to a nonempty subset of the shared Euclidean space.
The definition is the real infimum of the norms, and its identification
with `Metric.infDist` transfers the metric distance estimates. In particular
the zero set is the paper's ball-defined closure, even for nonclosed or
unbounded sets and in dimension zero. -/

noncomputable section
open Set
namespace D04

/-- Distance to a nonempty set. The explicit hypothesis excludes an empty
real infimum from the domain of this definition. -/
def distanceToSet {n : ℕ} (A : Set (E n)) (hA : A.Nonempty) (x : E n) : ℝ :=
  Specs.D04.C01.DistanceFunction.Model.distanceToSet A hA x

/-- The infimum of norms agrees with Mathlib's metric distance to a set. -/
theorem distanceToSet_eq_infDist {n : ℕ} (A : Set (E n)) (hA : A.Nonempty)
    (x : E n) : distanceToSet A hA x = Metric.infDist x A := by
  simpa only [distanceToSet, Specs.D04.C01.DistanceFunction.Model.distanceToSet,
    dist_eq_norm] using
    (Metric.isGLB_infDist (x := x) hA).csInf_eq (hA.image (dist x))

/-- The distance function is 1-Lipschitz, with the quantitative norm bound. -/
theorem distanceToSet_abs_sub_le {n : ℕ} (A : Set (E n)) (hA : A.Nonempty)
    (x y : E n) : |distanceToSet A hA x - distanceToSet A hA y| ≤ ‖x - y‖ := by
  rw [distanceToSet_eq_infDist, distanceToSet_eq_infDist]
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    (Metric.lipschitz_infDist_pt A).dist_le_mul x y

/-- Vanishing is equivalent to membership in closure, with no closedness
assumption on the original set. -/
theorem distanceToSet_eq_zero_iff {n : ℕ} (A : Set (E n)) (hA : A.Nonempty)
    (x : E n) : distanceToSet A hA x = 0 ↔ x ∈ Closure A := by
  rw [distanceToSet_eq_infDist, closure_eq]
  exact (Metric.mem_closure_iff_infDist_zero hA).symm

end D04
