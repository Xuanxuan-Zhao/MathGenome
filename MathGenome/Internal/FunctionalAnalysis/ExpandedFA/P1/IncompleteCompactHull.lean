import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.IncompleteCompactHull

noncomputable section
open Filter Set
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.IncompleteCompactHull

@[simp] theorem ofFinsupp_apply (𝕜 : Type u) [RCLike 𝕜]
    (x : C01SequenceSpaces.SequenceC00 𝕜) (n : ℕ) :
    (ofFinsupp 𝕜 x).val n = x n := rfl

theorem model_identification : Spec.ModelIdentification.{u} := by
  intro 𝕜 _
  refine ⟨⟨?_, ?_⟩, ofFinsupp_apply 𝕜, ?_⟩
  · intro x y h
    exact Finsupp.ext fun n => congrArg (fun z : C00 𝕜 => z.val n) h
  · intro x
    obtain ⟨y, hy⟩ := x.property
    exact ⟨y, Subtype.ext hy⟩
  · intro x
    simpa using (lp.hasSum_norm (by norm_num) x.val).tsum_eq.symm

@[simp] theorem point_apply (𝕜 : Type u) [RCLike 𝕜] (n j : ℕ) :
    (point 𝕜 n).val j = if n = j then (n + 1 : 𝕜)⁻¹ else 0 := by
  simp [point, Finsupp.single_apply]

theorem norm_point (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖point 𝕜 n‖ = (n + 1 : ℝ)⁻¹ := by
  have h : (point 𝕜 n).val = lp.single 1 n ((n + 1 : 𝕜)⁻¹) := by
    ext j
    simp [point_apply, lp.single_apply, Pi.single_apply, eq_comm]
  change ‖(point 𝕜 n).val‖ = _
  rw [h, lp.norm_single (by norm_num), norm_inv]
  norm_cast

theorem point_tendsto_zero (𝕜 : Type u) [RCLike 𝕜] :
    Tendsto (point 𝕜) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [norm_point]
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))

theorem compact_set : Spec.CompactSet.{u} := by
  intro 𝕜 _
  exact (point_tendsto_zero 𝕜).isCompact_insert_range

theorem sum_weight (m : ℕ) :
    ∑ i ∈ Finset.range m, weight i = 1 - (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ, hm]
    simp only [weight, pow_succ]
    ring

theorem partialCombination_mem_convexHull (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) :
    partialCombination 𝕜 m ∈ convexHull ℝ (compactSet 𝕜) := by
  classical
  let w : ℕ → ℝ := fun i => if i < m then weight i else 1 - ∑ j ∈ Finset.range m, weight j
  let z : ℕ → C00 𝕜 := fun i => if i < m then point 𝕜 i else 0
  have hsum : ∑ i ∈ Finset.range m, w i = ∑ i ∈ Finset.range m, weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [w, Finset.mem_range.mp hi]
  have h := (convex_convexHull ℝ (compactSet 𝕜)).sum_mem
    (t := Finset.range (m+1)) (w := w) (z := z) ?_ ?_ ?_
  · convert h using 1
    rw [Finset.sum_range_succ]
    simp only [z, lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    simp [w, Finset.mem_range.mp hi]
  · intro i hi
    dsimp [w]
    split_ifs
    · exact pow_nonneg (by norm_num) _
    · rw [sum_weight]
      have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := pow_nonneg (by norm_num) _
      linarith
  · rw [Finset.sum_range_succ, hsum]
    simp [w]
  · intro i hi
    apply subset_convexHull ℝ (compactSet 𝕜)
    dsimp [z]
    split_ifs
    · exact mem_insert_of_mem _ (mem_range_self i)
    · exact mem_insert _ _

theorem partialCombination_mem_hull (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) :
    partialCombination 𝕜 m ∈ closedHull 𝕜 :=
  subset_closure (partialCombination_mem_convexHull 𝕜 m)

/-- The original norm-continuous, scalar-linear coordinate functional. -/
def coordinate (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : C00 𝕜 →L[𝕜] 𝕜 :=
  (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 1 n).comp (finiteSupportSubmodule 𝕜).subtypeL

@[simp] theorem coordinate_apply (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : C00 𝕜) :
    coordinate 𝕜 n x = x.val n := rfl

@[simp] theorem partialCombination_apply (𝕜 : Type u) [RCLike 𝕜] (m j : ℕ) :
    (partialCombination 𝕜 m).val j =
      if j < m then weight j • (j + 1 : 𝕜)⁻¹ else 0 := by
  classical
  have hsmul (i : ℕ) :
      coordinate 𝕜 j (weight i • point 𝕜 i) =
        weight i • (if i = j then (i + 1 : 𝕜)⁻¹ else 0) := by
    change weight i • (point 𝕜 i).val j = _
    rw [point_apply]
  change coordinate 𝕜 j (partialCombination 𝕜 m) = _
  simp only [partialCombination, map_sum, hsmul]
  by_cases hj : j < m
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · intro h
      exact (h (Finset.mem_range.mpr hj)).elim
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by
      intro he
      exact hj (he ▸ Finset.mem_range.mp hi)
    simp [hij]

theorem coordinates_tendsto (𝕜 : Type u) [RCLike 𝕜] :
    Tendsto (fun m j => (partialCombination 𝕜 m).val j) atTop
      (𝓝 (fun j => weight j • (j + 1 : 𝕜)⁻¹)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with m hm
  simp [hm]

theorem coordinate_limit_not_finite_support (𝕜 : Type u) [RCLike 𝕜] :
    ¬ ∃ x : C00 𝕜, (fun j => x.val j) = fun j => weight j • (j + 1 : 𝕜)⁻¹ := by
  rintro ⟨x, hx⟩
  obtain ⟨f, hf⟩ := x.property
  obtain ⟨j, hj⟩ := f.support.exists_notMem
  have hz : x.val j = 0 := by
    rw [← hf]
    exact Finsupp.notMem_support_iff.mp hj
  have hne : weight j • (j + 1 : 𝕜)⁻¹ ≠ 0 := by
    apply smul_ne_zero
    · dsimp [weight]
      positivity
    · apply inv_ne_zero
      exact_mod_cast (Nat.succ_ne_zero j)
  exact hne ((congrFun hx j).symm.trans hz)

/-- The coordinate image of the hull contains a convergent sequence whose
limit is outside the image. This works for either topology in the example. -/
theorem hull_not_compact_of_continuous_coordinates (𝕜 : Type u) [RCLike 𝕜]
    (t : TopologicalSpace (C00 𝕜))
    (hc : @Continuous (C00 𝕜) (ℕ → 𝕜) t inferInstance (fun x j => x.val j)) :
    ¬ @IsCompact (C00 𝕜) t (closedHull 𝕜) := by
  intro h
  have hclosed := (h.image hc).isClosed
  have hmem := hclosed.mem_of_tendsto (coordinates_tendsto 𝕜)
    (Filter.Eventually.of_forall fun m =>
      ⟨partialCombination 𝕜 m, partialCombination_mem_hull 𝕜 m, rfl⟩)
  exact coordinate_limit_not_finite_support 𝕜 (by
    obtain ⟨x, _, hx⟩ := hmem
    exact ⟨x, hx⟩)

theorem weak_coordinates_continuous (𝕜 : Type u) [RCLike 𝕜] :
    @Continuous (C00 𝕜) (ℕ → 𝕜) (weakTopology 𝕜) inferInstance
      (fun x j => x.val j) := by
  let B := (topDualPairing 𝕜 (C00 𝕜)).flip
  have h (j : ℕ) := WeakBilin.eval_continuous B (coordinate 𝕜 j)
  let _ : TopologicalSpace (C00 𝕜) := weakTopology 𝕜
  exact continuous_pi fun j => (h j).comp continuous_induced_dom

theorem hull_not_weakly_compact : Spec.HullNotWeaklyCompact.{u} := by
  intro 𝕜 _
  exact hull_not_compact_of_continuous_coordinates 𝕜 (weakTopology 𝕜)
    (weak_coordinates_continuous 𝕜)

theorem hull_not_norm_compact : Spec.HullNotNormCompact.{u} := by
  intro 𝕜 _
  apply hull_not_compact_of_continuous_coordinates
  exact continuous_pi fun j => (coordinate 𝕜 j).continuous

end ExpandedFA.P1.IncompleteCompactHull
