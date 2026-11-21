import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07DenseCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01ExamplesComplete

/-! The weighted coordinate functionals on the canonical Banach space c₀.
Finite truncations give density; coordinate unit vectors attain the exact norm.
The sequence (n+1)^(-1/2) vanishes, while its weighted coordinates diverge. -/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C07DenseCounterexample
open C01SequenceSpaces

/-- Manuscript Tₙx = n xₙ, with positive indices shifted to natural indices. -/
def weightedCoordinate (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    SequenceC0 𝕜 →L[𝕜] 𝕜 :=
  (n + 1 : 𝕜) • (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ n).domRestrict
    (sequenceC0Submodule 𝕜)

theorem weightedCoordinate_apply (𝕜 : Type u) [RCLike 𝕜] (n : ℕ)
    (x : SequenceC0 𝕜) :
    weightedCoordinate 𝕜 n x = (n + 1 : 𝕜) * x.val n := rfl

/-- Coordinate truncations approximate each zero-limit sequence uniformly. -/
theorem finite_support_dense (𝕜 : Type u) [RCLike 𝕜] :
    Dense {x : SequenceC0 𝕜 | (Function.support (fun j => x.val j)).Finite} := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp x.property (ε / 2) (half_pos hε)
  classical
  let a : SequenceC00 𝕜 := ∑ j ∈ Finset.range N, Finsupp.single j (x.val j)
  have ha (j : ℕ) : a j = if j < N then x.val j else 0 := by
    simp [a, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
  refine ⟨c00ToC0 𝕜 a, a.hasFiniteSupport, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (c00ToC0 𝕜 a).val‖ < ε
  apply lt_of_le_of_lt (lp.norm_le_of_forall_le (half_pos hε).le ?_) (half_lt_self hε)
  intro j
  change ‖x.val j - a j‖ ≤ ε / 2
  rw [ha]
  by_cases hj : j < N
  · simp [hj]; positivity
  · simpa [hj, dist_zero_right] using (hN j (Nat.le_of_not_gt hj)).le

theorem weightedCoordinate_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖weightedCoordinate 𝕜 n‖ = (n + 1 : ℝ) := by
  have hn : ‖(n + 1 : 𝕜)‖ = (n + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (RCLike.norm_natCast (K := 𝕜) (n+1))
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    rw [weightedCoordinate_apply, norm_mul, hn]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by simp) x.val n) (by positivity)
  · let e : SequenceC0 𝕜 := c00ToC0 𝕜 (Finsupp.single n 1)
    have hval : e.val n = 1 := by
      change (Finsupp.single n (1 : 𝕜)) n = 1
      simp
    have heq : e.val = lp.single ∞ n (1 : 𝕜) := by
      apply lp.ext
      funext j
      change (Finsupp.single n (1 : 𝕜)) j =
        lp.single (E := fun _ : ℕ => 𝕜) ∞ n (1 : 𝕜) j
      by_cases hj : j = n
      · subst j; simp
      · simp [hj]
    have hnorm : ‖e‖ = 1 := by
      change ‖e.val‖ = 1
      rw [heq, lp.norm_single (by simp)]
      exact norm_one
    have h := (weightedCoordinate 𝕜 n).le_opNorm e
    simpa [weightedCoordinate_apply, hval, hn, hnorm] using h

theorem dense_set_boundedness_counterexample :
    Spec.Counterexample.{u} := by
  intro 𝕜 _
  have hc : CompleteSpace (SequenceC0 𝕜) :=
    (C01ExamplesComplete.sequence_c0_closed 𝕜).isComplete.completeSpace_coe
  refine ⟨hc, finite_support_dense 𝕜,
    weightedCoordinate 𝕜, weightedCoordinate_apply 𝕜, weightedCoordinate_norm 𝕜,
    ?_, ?_, ?_⟩
  · intro a ha
    have hz : ∀ᶠ n in atTop, a.val n = 0 := by
      rw [← Nat.cofinite_eq_atTop]
      filter_upwards [ha.eventually_cofinite_notMem] with n hn
      simpa [Function.mem_support] using hn
    have hev : ∀ᶠ n in atTop,
        weightedCoordinate 𝕜 n a = 0 := by
      filter_upwards [hz] with n hn
      change (n + 1 : 𝕜) * a.val n = 0
      rw [hn, mul_zero]
    have ht : Tendsto (fun n => weightedCoordinate 𝕜 n a)
        atTop (𝓝 0) := (tendsto_congr' hev).2 tendsto_const_nhds
    obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
    exact ⟨hev, ⟨C, fun n => hC ⟨n, rfl⟩⟩, ht⟩
  · have hnat : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n + 1 : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hnat
    have hx0 : Tendsto (fun j : ℕ =>
        (RCLike.ofReal ((Real.sqrt (j + 1 : ℝ))⁻¹) : 𝕜)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, RCLike.ofReal_zero] using
        RCLike.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero.comp hsqrt)
    obtain ⟨x, hx⟩ := (c0_identification 𝕜).1 _ |>.mpr hx0
    have hxj (j : ℕ) : x.val j = RCLike.ofReal ((Real.sqrt (j + 1 : ℝ))⁻¹) :=
      congrFun hx j
    have hval (n : ℕ) : weightedCoordinate 𝕜 n x =
        RCLike.ofReal (Real.sqrt (n + 1 : ℝ)) := by
      have hn : 0 < (n + 1 : ℝ) := by positivity
      have hr : (n + 1 : ℝ) * (Real.sqrt (n + 1 : ℝ))⁻¹ =
          Real.sqrt (n + 1 : ℝ) := by
        apply (mul_inv_eq_iff_eq_mul₀ (ne_of_gt (Real.sqrt_pos.2 hn))).2
        exact (Real.mul_self_sqrt hn.le).symm
      rw [weightedCoordinate_apply, hxj]
      calc
        (n + 1 : 𝕜) * RCLike.ofReal ((Real.sqrt (n + 1 : ℝ))⁻¹) =
            RCLike.ofReal ((n + 1 : ℝ) * (Real.sqrt (n + 1 : ℝ))⁻¹) := by
          rw [RCLike.ofReal_mul]
          simp
        _ = _ := congrArg RCLike.ofReal hr
    have hnorm (n : ℕ) : ‖weightedCoordinate 𝕜 n x‖ = Real.sqrt (n + 1 : ℝ) := by
      rw [hval, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]
    have ht : Tendsto (fun n => ‖weightedCoordinate 𝕜 n x‖) atTop atTop := by
      simpa only [hnorm] using hsqrt
    refine ⟨x, ?_, hval, ht, ?_⟩
    · intro j
      rw [hxj, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    · rintro ⟨C, hC⟩
      exact not_bddAbove_of_tendsto_atTop ht ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩
  · rintro ⟨M, hM⟩
    obtain ⟨n, hn⟩ := exists_nat_gt M
    have h := hM n
    rw [weightedCoordinate_norm] at h
    linarith

end ExpandedFA.P1.C07DenseCounterexample
