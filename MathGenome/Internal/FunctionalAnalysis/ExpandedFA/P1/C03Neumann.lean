import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03Neumann
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorComplete
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Neumann inversion with its full geometric remainder estimate. The geometric
series lemmas used here hold in complete normed rings without `NormOneClass`.
For n = 0 we use only norm(id) ≤ 1, retaining the zero space.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C03Neumann

theorem neumann_inversion : Spec.NeumannInversion := by
  intro 𝕜 E _ _ _ _ T hT
  let : CompleteSpace (E →L[𝕜] E) := C03OperatorComplete.operator_completeSpace 𝕜 E E
  have hs : Summable (fun n : ℕ => T ^ n) :=
    summable_geometric_of_norm_lt_one hT
  have hp (n : ℕ) : ‖T ^ n‖ ≤ ‖T‖ ^ n := by
    cases n with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using
        (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E))
    | succ n => exact norm_pow_le' T (Nat.succ_pos n)
  have hg : HasSum (fun n : ℕ => ‖T‖ ^ n) (1 - ‖T‖)⁻¹ :=
    hasSum_geometric_of_lt_one (norm_nonneg T) hT
  refine ⟨∑' n : ℕ, T ^ n, hs.hasSum, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  · exact mul_neg_geom_series T hT
  · exact geom_series_mul_neg T hT
  · simpa only [one_div] using tsum_of_norm_bounded hg hp
  · intro N
    have htail : (∑' n : ℕ, T ^ n) - (∑ n ∈ Finset.range (N + 1), T ^ n) =
        ∑' n : ℕ, T ^ (n + (N + 1)) := by
      exact (eq_sub_of_add_eq' (hs.sum_add_tsum_nat_add (N + 1))).symm
    rw [htail]
    have hmajor : HasSum (fun n : ℕ => ‖T‖ ^ (n + (N + 1)))
        (‖T‖ ^ (N + 1) / (1 - ‖T‖)) := by
      simpa only [pow_add, div_eq_mul_inv, mul_comm] using hg.mul_left (‖T‖ ^ (N + 1))
    exact tsum_of_norm_bounded hmajor (fun n => hp (n + (N + 1)))
  · rfl

end ExpandedFA.P1.C03Neumann
