import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07IncompleteCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03BoundedCriterion
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! Both incomplete-domain counterexamples over ℝ and ℂ, with literal supremum norm. -/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C07IncompleteCounterexample
open C01SequenceSpaces

abbrev partialSums : Spec.PartialSumType.{u} := partialSumValue
abbrev finiteSum : Spec.SumType.{u} := sumValue

abbrev weightedCoordinate : Spec.WeightedCoordinateType.{u} := weightedCoordinateValue

theorem weighted_coordinate_formula : Spec.WeightedCoordinateFormula.{u} := by
  intro 𝕜 _ n x
  rfl

theorem weighted_coordinate_norm : Spec.WeightedCoordinateNorm.{u} := by
  intro 𝕜 _ n
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
    intro x
    change ‖(n.val : 𝕜) * x.val (n.val - 1)‖ ≤ _
    rw [norm_mul, RCLike.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x.val _) (Nat.cast_nonneg _)
  · let e : C00Sup 𝕜 := ⟨C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞
        (Finsupp.single (n.val - 1) 1), ⟨Finsupp.single (n.val - 1) 1, rfl⟩⟩
    have he : ‖e‖ = 1 := by
      apply le_antisymm
      · apply lp.norm_le_of_forall_le (by norm_num : (0 : ℝ) ≤ 1)
        intro j
        change ‖(Finsupp.single (n.val - 1) (1 : 𝕜)) j‖ ≤ 1
        by_cases hj : n.val - 1 = j <;> simp [hj]
      · have h := lp.norm_apply_le_norm ENNReal.top_ne_zero e.val (n.val - 1)
        change ‖(Finsupp.single (n.val - 1) (1 : 𝕜)) (n.val - 1)‖ ≤ ‖e‖ at h
        simpa using h
    have h := (weightedCoordinateValue 𝕜 n).le_opNorm e
    change ‖(n.val : 𝕜) * (Finsupp.single (n.val - 1) (1 : 𝕜)) (n.val - 1)‖ ≤ _ at h
    simpa [he, RCLike.norm_natCast] using h

theorem weighted_coordinate_eventually_zero : Spec.EventuallyZero.{u} := by
  intro 𝕜 _ x
  obtain ⟨y, hy⟩ := x.property
  have hevent : ∀ᶠ k : ℕ in atTop, y k = 0 := by
    classical
    apply eventually_atTop.mpr
    refine ⟨y.support.sup id + 1, fun k hk => ?_⟩
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hle : k ≤ y.support.sup id := Finset.le_sup (f := id) hmem
    omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  apply eventually_atTop.mpr
  refine ⟨⟨N + 1, Nat.zero_lt_succ _⟩, ?_⟩
  intro n hn
  have hk : N ≤ n.val - 1 := by
    have : N + 1 ≤ n.val := hn
    omega
  change (n.val : 𝕜) * x.val (n.val - 1) = 0
  have hcoord : x.val (n.val - 1) = y (n.val - 1) := by
    exact congrArg (fun z : SequenceLInfinity 𝕜 => z (n.val - 1)) hy.symm
  rw [hcoord, hN _ hk, mul_zero]

theorem weighted_coordinate_pointwise_convergence : Spec.PointwiseConvergence.{u} := by
  intro 𝕜 _ x
  have h : (fun n : ℕ+ => weightedCoordinateValue 𝕜 n x)
      =ᶠ[atTop] (fun _ => 0) := weighted_coordinate_eventually_zero 𝕜 x
  exact tendsto_const_nhds.congr' h.symm

theorem weighted_coordinate_pointwise_bounded : Spec.PointwiseBounded.{u} := by
  intro 𝕜 _ x
  classical
  obtain ⟨y, hy⟩ := x.property
  let C : ℝ := ∑ k ∈ y.support, ((k + 1 : ℕ) : ℝ) * ‖y k‖
  refine ⟨C, Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)), ?_⟩
  intro n
  have hcoord : x.val (n.val - 1) = y (n.val - 1) :=
    congrArg (fun z : SequenceLInfinity 𝕜 => z (n.val - 1)) hy.symm
  change ‖(n.val : 𝕜) * x.val (n.val - 1)‖ ≤ C
  rw [hcoord, norm_mul, RCLike.norm_natCast]
  by_cases hn : n.val - 1 ∈ y.support
  · have h := Finset.single_le_sum
      (f := fun k => ((k + 1 : ℕ) : ℝ) * ‖y k‖)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hn
    have heq : n.val - 1 + 1 = n.val := Nat.sub_add_cancel (show 1 ≤ n.val from n.pos)
    simpa only [heq] using h
  · rw [Finsupp.notMem_support_iff.mp hn, norm_zero, mul_zero]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

theorem weighted_coordinate_unbounded_norms : Spec.UnboundedNorms.{u} := by
  intro 𝕜 _ C
  obtain ⟨N, hN⟩ := exists_nat_gt C
  refine ⟨⟨N + 1, Nat.zero_lt_succ _⟩, ?_⟩
  have hnorm := weighted_coordinate_norm 𝕜 (⟨N + 1, Nat.zero_lt_succ _⟩ : ℕ+)
  change C < ‖weightedCoordinateValue 𝕜
    (⟨N + 1, Nat.zero_lt_succ _⟩ : ℕ+)‖
  rw [hnorm]
  change C < ((N + 1 : ℕ) : ℝ)
  exact hN.trans (by exact_mod_cast Nat.lt_succ_self N)

@[simp] lemma c00SupEquiv_apply_coord (𝕜 : Type u) [RCLike 𝕜]
    (x : SequenceC00 𝕜) (j : ℕ) : (c00SupEquiv 𝕜 x).val j = x j := rfl

lemma partialSumValue_apply (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : C00Sup 𝕜) :
    partialSumValue 𝕜 n x = ∑ j ∈ Finset.range n, x.val j := by
  change (∑ j ∈ Finset.range n, lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ j) x.val = _
  simp only [sum_apply]
  rfl

lemma sumValue_apply (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC00 𝕜) :
    sumValue 𝕜 (c00SupEquiv 𝕜 x) = x.sum (fun _ a => a) := by
  unfold sumValue
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

theorem domain_identification : Spec.DomainIdentification.{u} := by
  intro 𝕜 _
  refine ⟨c00SupEquiv_apply_coord 𝕜, fun x => lp.norm_eq_ciSup x.val, ?_⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.hasFiniteSupport
  · intro hx
    exact ⟨Finsupp.ofSupportFinite (fun j => x j) hx, lp.ext rfl⟩

theorem functional_formulas : Spec.Formulas.{u} := by
  intro 𝕜 _
  exact ⟨partialSumValue_apply 𝕜, sumValue_apply 𝕜⟩

lemma onesBlock_coord (𝕜 : Type u) [RCLike 𝕜] (n j : ℕ) :
    (onesBlock 𝕜 n).val j = if j < n then 1 else 0 := by
  classical
  change (∑ i ∈ Finset.range n, Finsupp.single i (1 : 𝕜)) j = _
  simp [Finsupp.single_apply, eq_comm]

lemma onesBlock_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (hn : 0 < n) :
    ‖onesBlock 𝕜 n‖ = 1 := by
  change ‖(onesBlock 𝕜 n).val‖ = 1
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (by norm_num : (0 : ℝ) ≤ 1)
    intro j
    rw [onesBlock_coord]
    split_ifs <;> simp
  · have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (onesBlock 𝕜 n).val 0
    simpa [onesBlock_coord, hn] using h

lemma partialSumValue_onesBlock (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    partialSumValue 𝕜 n (onesBlock 𝕜 n) = (n : 𝕜) := by
  rw [partialSumValue_apply]
  calc
    (∑ j ∈ Finset.range n, (onesBlock 𝕜 n).val j) = ∑ _j ∈ Finset.range n, (1 : 𝕜) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [onesBlock_coord, Finset.mem_range.mp hj]
    _ = (n : 𝕜) := by simp

lemma sumValue_onesBlock (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    sumValue 𝕜 (onesBlock 𝕜 n) = (n : 𝕜) := by
  classical
  simp [onesBlock, map_sum, sumValue_apply, Finsupp.sum_single_index]

theorem unit_block_witnesses : Spec.Witnesses.{u} := by
  intro 𝕜 _ n
  exact ⟨onesBlock_coord 𝕜 n, onesBlock_norm 𝕜 n,
    sumValue_onesBlock 𝕜 n, partialSumValue_onesBlock 𝕜 n⟩

theorem partial_sum_norm : Spec.PartialSumNorm.{u} := by
  intro 𝕜 _ n
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg n)
    intro x
    rw [partialSumValue_apply]
    calc
      ‖∑ j ∈ Finset.range n, x.val j‖ ≤ ∑ j ∈ Finset.range n, ‖x.val j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, ‖x‖ := Finset.sum_le_sum fun j _ =>
        lp.norm_apply_le_norm ENNReal.top_ne_zero x.val j
      _ = (n : ℝ) * ‖x‖ := by simp
  · by_cases hn : n = 0
    · subst n
      exact_mod_cast norm_nonneg (partialSumValue 𝕜 0)
    · have h := (partialSumValue 𝕜 n).le_opNorm (onesBlock 𝕜 n)
      simpa [partialSumValue_onesBlock, onesBlock_norm 𝕜 n (Nat.pos_of_ne_zero hn),
        RCLike.norm_natCast] using h

lemma partialSums_eventually_equal_sum (𝕜 : Type u) [RCLike 𝕜] (x : C00Sup 𝕜) :
    ∀ᶠ n in atTop, partialSumValue 𝕜 n x = sumValue 𝕜 x := by
  classical
  obtain ⟨y, rfl⟩ := (c00SupEquiv 𝕜).surjective x
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range y.support
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [partialSumValue_apply, sumValue_apply]
  simp only [c00SupEquiv_apply_coord]
  symm
  apply Finsupp.sum_of_support_subset
  · exact hN.trans (Finset.range_mono hn)
  · intro j _
    rfl

theorem pointwise_limit : Spec.PointwiseLimit.{u} := by
  intro 𝕜 _ x
  apply tendsto_const_nhds.congr'
  filter_upwards [partialSums_eventually_equal_sum 𝕜 x] with n hn
  exact hn.symm

theorem limit_unbounded : Spec.UnboundedLimit.{u} := by
  intro 𝕜 _
  have hbound : ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : C00Sup 𝕜, ‖sumValue 𝕜 x‖ ≤ C * ‖x‖ := by
    rintro ⟨C, hC, h⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
    have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_right C 0) hn)
    have hb := h (onesBlock 𝕜 n)
    rw [sumValue_onesBlock, RCLike.norm_natCast, onesBlock_norm 𝕜 n hn0, mul_one] at hb
    exact (lt_of_le_of_lt (le_max_left C 0) hn).not_ge hb
  have hcont : ¬ Continuous (sumValue 𝕜) := by
    intro hc
    exact hbound ((C03BoundedCriterion.continuous_iff_norm_bound (sumValue 𝕜)).mp hc)
  refine ⟨hbound, hcont, ?_⟩
  intro hb
  exact hcont ((C03BoundedCriterion.continuous_iff_norm_bound (sumValue 𝕜)).mpr
    (C03BoundedCriterion.norm_bound_of_bounded_unit_ball (sumValue 𝕜) hb))

/-- Completeness would contradict uniform boundedness for the first family.
This uses the library theorem on complete domains only after introducing the
hypothetical completeness instance. -/
theorem domain_incomplete_target_complete : Spec.Completeness.{u} := by
  intro 𝕜 _
  refine ⟨?_, inferInstance⟩
  intro hc
  have : CompleteSpace (C00Sup 𝕜) := hc
  obtain ⟨C, hC⟩ := banach_steinhaus (g := weightedCoordinateValue 𝕜) (by
    intro x
    obtain ⟨B, _, hB⟩ := weighted_coordinate_pointwise_bounded 𝕜 x
    exact ⟨B, hB⟩)
  obtain ⟨n, hn⟩ := weighted_coordinate_unbounded_norms 𝕜 C
  exact hn.not_ge (hC n)

end ExpandedFA.P1.C07IncompleteCounterexample
