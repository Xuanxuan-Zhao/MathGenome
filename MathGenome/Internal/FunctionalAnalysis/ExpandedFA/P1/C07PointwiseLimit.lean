import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07PointwiseLimit
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Continuity of an existing pointwise limit

Theorem `fa2:p1:c07:pointwise-limit`. Pointwise convergence gives bounded
orbits, so uniform boundedness on the Banach domain gives a common operator
bound. Passing the linear identities and norm inequalities to the existing
limits constructs the bounded linear limit without completeness of F.
Finally choose indices tending to infinity along which the operator norms
converge to their finite lower limit and pass the pointwise norm bound to
the limit along those indices.
-/

namespace ExpandedFA.P1.C07PointwiseLimit

open Filter
open scoped Topology

theorem pointwise_limit : Spec.PointwiseLimit := by
  intro 𝕜 E F _ _ _ _ _ _ A T h
  have hpoint : ∀ x : E, ∃ C : ℝ, ∀ n, ‖A n x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (h x))
    exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
  obtain ⟨M, hM, hbound⟩ :=
    C07UniformBoundedness.uniform_boundedness 𝕜 E F ℕ A hpoint
  let L : E →ₗ[𝕜] F :=
    { toFun := T
      map_add' := fun x y => tendsto_nhds_unique (h (x + y))
        (by simpa only [map_add] using (h x).add (h y))
      map_smul' := fun a x => tendsto_nhds_unique (h (a • x))
        (by simpa only [map_smul, RingHom.id_apply] using (h x).const_smul a) }
  have hTbound : ∀ x : E, ‖L x‖ ≤ M * ‖x‖ := by
    intro x
    exact le_of_tendsto (h x).norm (Eventually.of_forall fun n =>
      (A n).le_of_opNorm_le (hbound n) x)
  let S : E →L[𝕜] F := L.mkContinuous M hTbound
  have hu : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖A n‖) :=
    isBoundedUnder_of ⟨M, hbound⟩
  have hl : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖A n‖) :=
    isBoundedUnder_of ⟨0, fun n => norm_nonneg (A n)⟩
  obtain ⟨k, hk, hkinfty⟩ := exists_seq_tendsto_liminf hu.isCoboundedUnder_ge hl
  have hnonneg : 0 ≤ liminf (fun n => ‖A n‖) atTop :=
    ge_of_tendsto hk (Eventually.of_forall fun n => norm_nonneg (A (k n)))
  refine ⟨S, rfl, ⟨M, hM, hbound⟩, hnonneg, ?_⟩
  apply S.opNorm_le_bound hnonneg
  intro x
  exact le_of_tendsto_of_tendsto ((h x).comp hkinfty).norm
    (hk.mul tendsto_const_nhds)
    (Eventually.of_forall fun n => (A (k n)).le_opNorm x)

end ExpandedFA.P1.C07PointwiseLimit
