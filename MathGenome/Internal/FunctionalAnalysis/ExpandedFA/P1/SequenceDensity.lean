import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SequenceDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces

/-! Initial coordinate truncations converge in finite-exponent ℓᵖ and c₀.
The inclusions are the canonical pointwise maps from the shared sequence Specs.
In ℓ∞, approximation by finite supports forces the coordinates to vanish;
conversely, c₀ truncations give every point of that closure. -/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.SequenceDensity
open C01SequenceSpaces

theorem sequence_truncation_coordinates : Spec.TruncationCoordinates.{u} := by
  intro 𝕜 _ x N j
  classical
  simp [sequenceTruncation, Finsupp.finsetSum_apply, Finsupp.single_apply,
    eq_comm]

theorem lp_truncation_convergence : Spec.LpTruncationConvergence.{u} := by
  intro 𝕜 _ p _ hp x
  have heq (N : ℕ) : C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p
      (sequenceTruncation (fun j => x j) N) =
        ∑ j ∈ Finset.range N, lp.single p j (x j) := by
    classical
    change C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p
      (∑ j ∈ Finset.range N, Finsupp.single j (x j)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply lp.ext
    funext i
    change (Finsupp.single j (x j)) i = lp.single (E := fun _ : ℕ => 𝕜) p j (x j) i
    by_cases h : i = j
    · subst i; simp
    · simp [h]
  simp_rw [heq]
  exact (lp.hasSum_single hp x).tendsto_sum_nat

theorem c0_truncation_convergence : Spec.C0TruncationConvergence.{u} := by
  intro 𝕜 _ x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp x.property (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  change ‖(sequenceFiniteInC0 𝕜 (sequenceTruncation (fun j => x.val j) n)).val - x.val‖ < ε
  apply lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity : 0 ≤ ε / 2) ?_)
    (half_lt_self hε)
  intro j
  change ‖sequenceTruncation (fun j => x.val j) n j - x.val j‖ ≤ ε / 2
  rw [sequence_truncation_coordinates]
  by_cases hj : j < n
  · simp [hj]; positivity
  · simpa [hj, dist_eq_norm] using (hN j (hn.trans (Nat.le_of_not_gt hj))).le

theorem lp_finite_sequences_dense : Spec.LpDensity.{u} := by
  intro 𝕜 _ p _ hp x
  exact mem_closure_of_tendsto (lp_truncation_convergence 𝕜 p hp x)
    (Eventually.of_forall fun N => ⟨sequenceTruncation (fun j => x j) N, rfl⟩)

theorem c0_finite_sequences_dense : Spec.C0Density.{u} := by
  intro 𝕜 _ x
  exact mem_closure_of_tendsto (c0_truncation_convergence 𝕜 x)
    (Eventually.of_forall fun N => ⟨sequenceTruncation (fun j => x.val j) N, rfl⟩)

theorem infinity_closure_finite_sequences : Spec.InfinityClosure.{u} := by
  intro 𝕜 _
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hx ε hε
    have hz : ∀ᶠ j in atTop, a j = 0 := by
      rw [← Nat.cofinite_eq_atTop]
      filter_upwards [a.hasFiniteSupport.eventually_cofinite_notMem] with j hj
      simpa [Function.mem_support] using hj
    obtain ⟨N, hN⟩ := eventually_atTop.mp hz
    refine ⟨N, fun j hj => ?_⟩
    rw [dist_zero_right]
    calc
      ‖x j‖ = ‖(x - C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ a) j‖ := by
        change ‖x j‖ = ‖x j - a j‖
        rw [hN j hj, sub_zero]
      _ ≤ ‖x - C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ a‖ :=
        lp.norm_apply_le_norm (by simp) _ j
      _ < ε := by simpa only [dist_eq_norm] using ha
  · rintro _ ⟨x, rfl⟩
    have ht := (continuous_subtype_val.tendsto x).comp (c0_truncation_convergence 𝕜 x)
    exact mem_closure_of_tendsto ht (Eventually.of_forall fun N =>
      ⟨sequenceTruncation (fun j => x.val j) N, rfl⟩)

theorem constant_distance_finite_sequences : Spec.ConstantDistance.{u} := by
  intro 𝕜 _
  have hne : (Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞)).Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := (1 : SequenceLInfinity 𝕜))
      (Set.mem_range.mpr ⟨0, rfl⟩ :
        C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ 0 ∈ Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞))
    simpa using h
  · apply (Metric.le_infDist hne).mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨j, hj⟩ := a.hasFiniteSupport.exists_notMem
    have hz : a j = 0 := by simpa [Function.mem_support] using hj
    have h := lp.norm_apply_le_norm (E := fun _ : ℕ => 𝕜) (p := ∞) (by simp)
      (1 - C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ a) j
    change ‖(1 : 𝕜) - a j‖ ≤ ‖(1 : SequenceLInfinity 𝕜) -
      C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ a‖ at h
    simpa [hz, dist_eq_norm] using h

theorem c0_proper_in_infinity : Spec.C0Proper.{u} := by
  intro 𝕜 _
  have hnot : (1 : SequenceLInfinity 𝕜) ∉
      Set.range (fun x : SequenceC0 𝕜 => x.val) := by
    intro h
    have hmem : (1 : SequenceLInfinity 𝕜) ∈
        closure (Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞)) := by
      rw [infinity_closure_finite_sequences 𝕜]
      exact h
    have hzero := Metric.mem_closure_iff_infDist_zero
      (x := (1 : SequenceLInfinity 𝕜))
      (show (Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞)).Nonempty from ⟨_, ⟨0, rfl⟩⟩)
      |>.mp hmem
    rw [constant_distance_finite_sequences 𝕜] at hzero
    exact one_ne_zero hzero
  exact ⟨hnot, Set.ssubset_univ_iff.mpr (fun h => hnot (h.symm ▸ Set.mem_univ 1))⟩

end ExpandedFA.P1.SequenceDensity
