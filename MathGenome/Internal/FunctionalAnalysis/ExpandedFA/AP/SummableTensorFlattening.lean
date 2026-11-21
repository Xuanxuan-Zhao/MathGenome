import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.AlgebraicRankOneTensors
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.SummableTensorFlattening
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
namespace ExpandedFA.AP
open AlgebraicRankOneTensorsSpec SummableTensorFlatteningSpec
open Filter
universe u v
variable {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The zero-padded enumeration of a finite list has the expected sum. -/
theorem hasSum_list_getD {A B : Type*} [Zero A] [AddCommGroup B]
    [TopologicalSpace B] [IsTopologicalAddGroup B]
    (h : A → B) (h0 : h 0 = 0) (l : List A) :
    HasSum (fun n : ℕ => h (l.getD n 0)) (l.map h).sum := by
  induction l with
  | nil => simp [h0]
  | cons p l ih =>
    apply (hasSum_nat_add_iff' 1).mp
    simpa [List.getD_cons_succ, List.getD_cons_zero, add_comm] using ih

/-- Absolute summability of the padded two-index array follows from the costs. -/
theorem summable_padded_cost (l : ℕ → List ((X →L[𝕜] 𝕜) × X))
    (hl : Summable (fun m => cost (l m))) :
    Summable (fun p : ℕ × ℕ =>
      ‖((l p.1).getD p.2 (0, 0)).1‖ * ‖((l p.1).getD p.2 (0, 0)).2‖) := by
  have hb (m : ℕ) := hasSum_list_getD
    (fun p : (X →L[𝕜] 𝕜) × X => ‖p.1‖ * ‖p.2‖) (by simp) (l m)
  apply (summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  refine ⟨fun m => (hb m).summable, ?_⟩
  have heq (m : ℕ) :
      (∑' n : ℕ, ‖((l m).getD n (0, 0)).1‖ * ‖((l m).getD n (0, 0)).2‖) =
        cost (l m) := (hb m).tsum_eq
  simpa only [heq] using hl

/-- Enumeration by `Nat.unpair` preserves absolute summability. -/
theorem summable_flattened_cost (l : ℕ → List ((X →L[𝕜] 𝕜) × X))
    (hl : Summable (fun m => cost (l m))) :
    Summable (fun j => ‖(flattenedPair l j).1‖ * ‖(flattenedPair l j).2‖) := by
  exact Nat.pairEquiv.symm.summable_iff.mpr (summable_padded_cost l hl)

/-- Any termwise contractive map of the rank-one terms commutes with flattening. -/
theorem hasSum_flattened {B : Type*} [NormedAddCommGroup B] [CompleteSpace B]
    (H : ((X →L[𝕜] 𝕜) × X) → B) (H0 : H (0, 0) = 0)
    (hH : ∀ p, ‖H p‖ ≤ ‖p.1‖ * ‖p.2‖)
    (l : ℕ → List ((X →L[𝕜] 𝕜) × X)) (hl : Summable (fun m => cost (l m))) :
    HasSum (fun j => H (flattenedPair l j)) (∑' m, ((l m).map H).sum) := by
  have hb (m : ℕ) := hasSum_list_getD H H0 (l m)
  have hs : Summable (fun p : ℕ × ℕ => H ((l p.1).getD p.2 (0, 0))) :=
    (summable_padded_cost l hl).of_norm_bounded (fun p => hH _)
  have heq : (∑' p : ℕ × ℕ, H ((l p.1).getD p.2 (0, 0))) =
      ∑' m, ((l m).map H).sum := by
    rw [hs.tsum_prod']
    · exact tsum_congr fun m => (hb m).tsum_eq
    · exact fun m => (hb m).summable
  apply (Nat.pairEquiv.symm.hasSum_iff
    (f := fun p : ℕ × ℕ => H ((l p.1).getD p.2 (0, 0)))).mpr
  rw [← heq]
  exact hs.hasSum

/-- Near-infimum representations can be chosen with a summable total cost. -/
theorem exists_summable_representations (w : ℕ → Tensor 𝕜 X)
    (hw : Summable (fun m => nu (w m))) :
    ∃ l : ℕ → List ((X →L[𝕜] 𝕜) × X),
      (∀ m, tensorSum (l m) = w m) ∧ Summable (fun m => cost (l m)) := by
  classical
  have hn (m : ℕ) := projectiveInfimum_near (w m) ((1 / 2 : ℝ) ^ m)
    (pow_pos (by norm_num) m)
  choose r hr using hn
  refine ⟨fun m => (r m).val, fun m => (r m).property, ?_⟩
  exact Summable.of_nonneg_of_le (fun m => cost_nonneg _)
    (fun m => (hr m).le)
    (hw.add (summable_geometric_of_lt_one (by norm_num) (by norm_num)))

/-- The operator of a finite tensor representation is the sum of its rank-one maps. -/
theorem tensor_operator_list_formula (l : List ((X →L[𝕜] 𝕜) × X)) :
    operator (tensorSum l) = (l.map fun p => p.1.smulRight p.2).sum := by
  induction l with
  | nil => simp [tensorSum]
  | cons p l ih =>
    simpa [operator, ContinuousLinearMap.smulRightLₗ] using
      congrArg (fun z => p.1.smulRight p.2 + z) ih

/-- Flatten an absolutely projectively summable series of finite algebraic tensors.
The resulting rank-one series has the same trace and operator limits as the
original finite partial sums. -/
theorem summableTensorFlattening [CompleteSpace X]
    (a : Tensor 𝕜 X) (v : ℕ → Tensor 𝕜 X)
    (hv : Summable (fun m => nu (v m))) : Flattening a v := by
  classical
  let w : ℕ → Tensor 𝕜 X
    | 0 => a
    | m + 1 => v m
  have hw : Summable (fun m => nu (w m)) :=
    (summable_nat_add_iff 1).mp (by simpa only [w] using hv)
  obtain ⟨l, hlw, hl⟩ := exists_summable_representations w hw
  have ht : Summable (fun m => trace (v m)) :=
    hv.of_norm_bounded (fun m => tensor_trace_bound _)
  have ho : Summable (fun m => operator (v m)) :=
    hv.of_norm_bounded (fun m => tensor_operator_bound _)
  have htw : Summable (fun m => trace (w m)) :=
    hw.of_norm_bounded (fun m => tensor_trace_bound _)
  have how : Summable (fun m => operator (w m)) :=
    hw.of_norm_bounded (fun m => tensor_operator_bound _)
  refine ⟨l, hlw 0, fun m => hlw (m + 1), hl, summable_flattened_cost l hl, ?_, ?_, ?_, ?_⟩
  · have h := hasSum_flattened (fun p : (X →L[𝕜] 𝕜) × X => p.1 p.2)
      (by simp) (fun p => p.1.le_opNorm p.2) l hl
    have hb (m : ℕ) : ((l m).map fun p => p.1 p.2).sum = trace (w m) := by
      rw [← tensor_trace_formula, hlw]
    simp only [hb] at h
    rw [htw.tsum_eq_zero_add] at h
    simpa only [w] using h
  · have h := hasSum_flattened (fun p : (X →L[𝕜] 𝕜) × X => p.1.smulRight p.2)
      (by simp) (fun p => (ContinuousLinearMap.norm_smulRight_apply p.1 p.2).le) l hl
    have hb (m : ℕ) : ((l m).map fun p => p.1.smulRight p.2).sum = operator (w m) := by
      rw [← tensor_operator_list_formula, hlw]
    simp only [hb] at h
    rw [how.tsum_eq_zero_add] at h
    simpa only [w] using h
  · simpa only [map_add, map_sum] using
      (tendsto_const_nhds.add ht.hasSum.tendsto_sum_nat)
  · simpa only [map_add, map_sum] using
      (tendsto_const_nhds.add ho.hasSum.tendsto_sum_nat)

end ExpandedFA.AP
