import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.CzeroUncomplemented
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C0NotComplemented
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C0NotDual

/-! Assembly of the noncomplementation theorem from its proved sequence-space
and bidual consequences. -/

namespace ExpandedFA.P1.CzeroUncomplemented
open C01SequenceSpaces Filter
open scoped Topology
universe u v

/-- A supremum-norm limit of null sequences is a null sequence. -/
theorem c0_isClosed (𝕜 : Type u) [RCLike 𝕜] :
    IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun n => x n) atTop (𝓝 0)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  have hy0 : Tendsto (fun n => y n) atTop (𝓝 0) := hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy0 (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hcoord : ‖x n - y n‖ ≤ ‖x - y‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) n
  have hnear : ‖x - y‖ < ε / 2 := by simpa only [dist_eq_norm] using hxy
  have htail : ‖y n‖ < ε / 2 := by simpa only [dist_zero_right] using hN n hn
  have hnorm : ‖x n‖ ≤ ‖x n - y n‖ + ‖y n‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x n - y n) (y n)
  simpa only [Real.dist_eq, sub_zero, abs_norm, add_halves] using
    lt_of_le_of_lt hnorm (add_lt_add (lt_of_le_of_lt hcoord hnear) htail)

/-- The closed c₀ subspace is uncomplemented in ℓ∞ and in its bidual, and
it is not isomorphic to the continuous linear dual of any normed space. -/
theorem czero_uncomplemented : Spec.Noncomplementation.{u,v} := by
  intro 𝕜 _
  exact ⟨c0_isClosed 𝕜, C0NotComplemented.not_complemented 𝕜,
    C0NotDual.canonical_image_not_complemented 𝕜,
    fun Y _ _ => C0NotDual.not_isomorphic_to_dual 𝕜 Y⟩

end ExpandedFA.P1.CzeroUncomplemented
