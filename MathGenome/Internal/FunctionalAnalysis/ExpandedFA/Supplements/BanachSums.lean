import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BanachSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.BanachSumDefinitions

/-! Arbitrary Banach sums, paper.tex:6234–6269. The native `lp` completeness
and unconditional finite truncations apply to the accepted carriers verbatim.
The c₀ arguments below use the exact finite-positive-level-set condition, with
no countability restriction. -/

open scoped ENNReal Classical
noncomputable section
universe u v w
namespace ExpandedFA.Supplements.BanachSums
open ExpandedFA.Supplements.BanachSumDefinitions

theorem complete_power_sum : Spec.CompletePowerSum := by
  intro I E _ _ p _ _
  infer_instance

theorem complete_bounded_product : Spec.CompleteBoundedProduct := by
  intro I E _ _
  infer_instance

/-- A uniform ε/2 approximation controls the ε level set by the approximant's
ε/2 level set, which is finite. No completeness of the summands is needed. -/
theorem closed_c0 : Spec.ClosedC0 := by
  intro I E _ 𝕜 _ _
  apply isClosed_of_closure_subset
  intro x hx
  change VanishesAtInfinity E (fun i => x i)
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  apply (hy (ε / 2) (half_pos hε)).subset
  intro i hi
  change ε ≤ ‖x i‖ at hi
  change ε / 2 ≤ ‖y i‖
  have hd : ‖x i - y i‖ < ε / 2 := by
    have h := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (x - y) i
    exact h.trans_lt (by simpa only [dist_eq_norm] using hxy)
  have hn := norm_le_norm_sub_add (x i) (y i)
  linarith

theorem complete_c0 : Spec.CompleteC0 := by
  intro I E _ _ 𝕜 _ _
  exact (closed_c0 E (𝕜 := 𝕜)).isComplete.completeSpace_coe

theorem contractive_coordinates : Spec.ContractiveCoordinates := by
  intro I E _ 𝕜 _ _ p _ i
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using lp.norm_apply_le_norm hp x i
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change ‖lp.single p i a‖ ≤ 1 * ‖a‖
    rw [lp.norm_single (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)), one_mul]
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x.val i‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using
      lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) x.val i
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change ‖lp.single ∞ i a‖ ≤ 1 * ‖a‖
    rw [lp.norm_single (by simp), one_mul]

theorem power_truncations_converge : Spec.PowerTruncationsConverge := by
  intro I E _ p _ hp x
  exact lp.hasSum_single hp x

theorem dense_power_finiteSupport : Spec.DensePowerFiniteSupport := by
  intro I E _ p _ hp x
  exact mem_closure_of_tendsto (power_truncations_converge E p hp x)
    (Filter.Eventually.of_forall fun A => truncate_finiteSupport E p A (fun i => x i))

/-- Truncate at the finite ε/2 level set; the supremum of the remaining
coordinate norms is at most ε/2. This also handles the empty index set. -/
theorem c0_truncation_approximation : Spec.C0TruncationApproximation := by
  intro I E _ 𝕜 _ _ x ε hε
  let hF := x.property (ε / 2) (half_pos hε)
  refine ⟨hF.toFinset, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  change ‖x.val - (c0Truncate E hF.toFinset (fun i => x.val i)).val‖ ≤ ε / 2
  apply lp.norm_le_of_forall_le (le_of_lt (half_pos hε))
  intro i
  change ‖x.val i - (c0Truncate E hF.toFinset (fun i => x.val i)).val i‖ ≤ ε / 2
  rw [c0Truncate_apply]
  by_cases hi : i ∈ hF.toFinset
  · simp [hi, le_of_lt (half_pos hε)]
  · rw [ite_eq_right hi, sub_zero]
    exact le_of_lt (lt_of_not_ge (by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hi))

theorem dense_c0_finiteSupport : Spec.DenseC0FiniteSupport := by
  intro I E _ 𝕜 _ _ x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := c0_truncation_approximation E x ε hε
  exact ⟨c0Truncate E A (fun i => x.val i),
    c0Truncate_finiteSupport E A (fun i => x.val i), by simpa only [dist_eq_norm] using hA⟩

theorem bounded_constant_obstruction : Spec.BoundedConstantObstruction := by
  intro I _ 𝕜 _
  let c : BoundedProduct (fun _ : I => 𝕜) :=
    ⟨fun _ => 1, memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; simp⟩⟩
  refine ⟨c, fun _ => rfl, ?_, ?_⟩
  · apply le_antisymm
    · exact lp.norm_le_of_forall_le zero_le_one (by intro i; simp [c])
    · obtain ⟨i⟩ := (inferInstance : Nonempty I)
      simpa [c] using lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) c i
  · intro y hy
    obtain ⟨i, hi⟩ := hy.exists_notMem
    have hyi : y i = 0 := by simpa using hi
    have h := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (c - y) i
    change ‖(1 : 𝕜) - y i‖ ≤ ‖c - y‖ at h
    simpa only [dist_eq_norm, hyi, sub_zero, norm_one] using h

theorem not_dense_bounded_finiteSupport : Spec.NotDenseBoundedFiniteSupport := by
  intro I _ 𝕜 _ hd
  obtain ⟨c, _, _, hc⟩ := bounded_constant_obstruction I 𝕜
  obtain ⟨y, hy, hcy⟩ := Metric.mem_closure_iff.mp (hd c) 1 zero_lt_one
  exact (not_lt.mpr (hc y hy)) hcy

end ExpandedFA.Supplements.BanachSums
