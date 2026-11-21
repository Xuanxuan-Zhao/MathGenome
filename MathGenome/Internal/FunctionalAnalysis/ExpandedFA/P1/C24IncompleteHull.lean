import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24IncompleteHull
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.IncompleteCompactHull

noncomputable section
open Filter Set
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C24IncompleteHull
open IncompleteCompactHull

theorem model_identification : Spec.ModelIdentification.{u} :=
  IncompleteCompactHull.model_identification

theorem compact_points : Spec.CompactPoints.{u} := by
  intro 𝕜 _
  exact ⟨point_tendsto_zero 𝕜, compact_set 𝕜⟩

theorem partialCombination_cauchy (𝕜 : Type u) [RCLike 𝕜] :
    CauchySeq (partialCombination 𝕜) := by
  apply SeminormedAddCommGroup.cauchySeq_of_le_geometric (r := (1/2 : ℝ))
    (C := 1) (by norm_num)
  intro n
  rw [partialCombination, partialCombination, Finset.sum_range_succ,
    sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by dsimp [weight]; positivity), norm_point]
  have hn : (n + 1 : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  calc
    weight n * (n + 1 : ℝ)⁻¹ ≤ weight n * 1 :=
      mul_le_mul_of_nonneg_left hn (by dsimp [weight]; positivity)
    _ ≤ 1 * (1 / 2 : ℝ) ^ n := by
      simp only [weight, pow_succ, mul_one, one_mul]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

theorem partial_sums : Spec.PartialSums.{u} := by
  intro 𝕜 _
  exact ⟨partialCombination_mem_convexHull 𝕜, partialCombination_cauchy 𝕜⟩

theorem limitCoordinate_ne_zero (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    limitCoordinate 𝕜 n ≠ 0 := by
  apply smul_ne_zero
  · dsimp [weight]; positivity
  · apply inv_ne_zero
    exact_mod_cast (Nat.succ_ne_zero n)

theorem coordinate_tendsto (𝕜 : Type u) [RCLike 𝕜] (j : ℕ) :
    Tendsto (fun N => (partialCombination 𝕜 N).val j) atTop
      (𝓝 (limitCoordinate 𝕜 j)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  simp [partialCombination_apply, hN, limitCoordinate]

theorem completion_limit : Spec.CompletionLimit.{u} := by
  intro 𝕜 _
  have hc : CauchySeq (fun N =>
      (partialCombination 𝕜 N : UniformSpace.Completion (C00 𝕜))) :=
    (UniformSpace.Completion.uniformContinuous_coe (C00 𝕜)).comp_cauchySeq
      (partialCombination_cauchy 𝕜)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  have hcoord : ∀ n, completionCoordinates 𝕜 z n = limitCoordinate 𝕜 n := by
    intro n
    have h := ((lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 1 n).continuous.comp
      (inclusion 𝕜).fromCompletion.continuous).tendsto z |>.comp hz
    have h' : Tendsto (fun N => (partialCombination 𝕜 N).val n) atTop
        (𝓝 (completionCoordinates 𝕜 z n)) := by
      change Tendsto (fun N => ((inclusion 𝕜).fromCompletion
        (partialCombination 𝕜 N : UniformSpace.Completion (C00 𝕜))) n) atTop
        (𝓝 (completionCoordinates 𝕜 z n)) at h
      apply h.congr'
      exact Filter.Eventually.of_forall fun N =>
        congrArg (fun f : C01SequenceSpaces.SequenceLp 𝕜 1 => f n)
          ((inclusion 𝕜).fromCompletion_apply_coe (partialCombination 𝕜 N))
    exact tendsto_nhds_unique h' (coordinate_tendsto 𝕜 n)
  have hne : ∀ n, completionCoordinates 𝕜 z n ≠ 0 := by
    intro n; rw [hcoord]; exact limitCoordinate_ne_zero 𝕜 n
  refine ⟨z, hz, hcoord, hne, ?_⟩
  have hs : Function.support (completionCoordinates 𝕜 z) = Set.univ :=
    Set.eq_univ_of_forall hne
  rw [hs]
  exact Set.infinite_univ

theorem no_convergent_subsequence : Spec.NoConvergentSubsequence.{u} := by
  intro 𝕜 _ φ hφ x hx
  apply coordinate_limit_not_finite_support 𝕜
  refine ⟨x, funext fun n => ?_⟩
  have h := (coordinate 𝕜 n).continuous.tendsto x |>.comp hx
  exact tendsto_nhds_unique h ((coordinate_tendsto 𝕜 n).comp hφ.tendsto_atTop)

theorem space_incomplete : Spec.IncompleteSpace.{u} := by
  intro 𝕜 _ hc
  let := hc
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (partialCombination_cauchy 𝕜)
  exact no_convergent_subsequence 𝕜 id strictMono_id x hx

theorem hull_noncompact : Spec.NoncompactHull.{u} := by
  intro 𝕜 _ h
  obtain ⟨x, _, φ, hφ, hx⟩ := h.tendsto_subseq (fun n =>
    partialCombination_mem_hull 𝕜 n)
  exact no_convergent_subsequence 𝕜 φ hφ x hx

end ExpandedFA.P1.C24IncompleteHull
