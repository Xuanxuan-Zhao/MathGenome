import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.TraceObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.ApproximationPropertyDefinitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ExpandedFA.AP

noncomputable section
open Filter Finset
open scoped Topology

/-- Positive null weights that preserve summability after division. -/
lemma summable_div_null_weights {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hs : Summable b) :
    ∃ w : ℕ → ℝ, (∀ n, 0 < w n) ∧ Tendsto w atTop (𝓝 0) ∧
      Summable (fun n => b n / w n) := by
  let t : ℕ → ℝ := fun n => ∑' k, b (k + n)
  have ht : ∀ n, 0 ≤ t n := fun n => tsum_nonneg fun k => hb _
  have hrec : ∀ n, t n = b n + t (n+1) := by
    intro n
    have hn : Summable (fun k => b (k + n)) := hs.comp_injective (add_left_injective n)
    simpa [t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn.tsum_eq_zero_add
  have hmono : ∀ n, t (n+1) ≤ t n := by
    intro n
    rw [hrec n]
    exact le_add_of_nonneg_left (hb n)
  have hsqrt : Summable (fun n => Real.sqrt (t n) - Real.sqrt (t (n+1))) := by
    apply summable_of_sum_range_le (c := Real.sqrt (t 0))
    · intro n
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt (hmono n))
    · intro n
      rw [Finset.sum_range_sub']
      exact sub_le_self _ (Real.sqrt_nonneg _)
  have hdiv : ∀ n, b n / Real.sqrt (t n) ≤
      2 * (Real.sqrt (t n) - Real.sqrt (t (n+1))) := by
    intro n
    by_cases hz : t n = 0
    · have hbn : b n = 0 := by have := ht (n+1); have := hrec n; linarith [hb n]
      have htn : t (n+1) = 0 := by have := hb n; have := hrec n; linarith [ht (n+1)]
      simp [hz, hbn, htn]
    · have hp : 0 < Real.sqrt (t n) := Real.sqrt_pos.2 (lt_of_le_of_ne (ht n) (Ne.symm hz))
      apply (div_le_iff₀ hp).2
      have hsq := Real.sq_sqrt (ht n)
      have hsq' := Real.sq_sqrt (ht (n+1))
      nlinarith [sq_nonneg (Real.sqrt (t n) - Real.sqrt (t (n+1))), hrec n]
  have hsum : Summable (fun n => b n / Real.sqrt (t n)) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (hb n) (Real.sqrt_nonneg _))
      hdiv (hsqrt.mul_left 2)
  let w : ℕ → ℝ := fun n => Real.sqrt (t n) + 1 / ((n : ℝ) + 1)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro n
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)
  · have hzero : Tendsto t atTop (𝓝 0) := tendsto_sum_nat_add b
    have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hzero
    simpa [w] using hroot.add tendsto_one_div_add_atTop_nhds_zero_nat
  · refine Summable.of_nonneg_of_le (fun n => div_nonneg (hb n) (by dsimp [w]; positivity))
      (fun n => ?_) hsum
    by_cases hz : t n = 0
    · have hbn : b n = 0 := by have := ht (n+1); have := hrec n; linarith [hb n]
      simp [hbn]
    · apply div_le_div_of_nonneg_left (hb n) (Real.sqrt_pos.2 (lt_of_le_of_ne (ht n) (Ne.symm hz)))
      exact le_add_of_nonneg_right (by positivity)


universe u v
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A bounded finite-rank operator is a finite sum of bounded rank-one maps. -/
lemma finiteRank_eq_sum (T : X →L[𝕜] X)
    (hT : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) :
    ∃ (n : ℕ) (h : Fin n → X →L[𝕜] 𝕜) (z : Fin n → X),
      ∀ v, T v = ∑ r, (h r v) • z r := by
  haveI := hT
  let B := Module.finBasis 𝕜 (LinearMap.range T.toLinearMap)
  refine ⟨_, fun r => (B.coord r).toContinuousLinearMap.comp T.rangeRestrict,
    fun r => (B r : X), ?_⟩
  intro v
  have hv := congrArg (fun z : LinearMap.range T.toLinearMap => (z : X))
    (B.sum_repr (T.rangeRestrict v))
  change T v = ∑ r, (B.repr (T.rangeRestrict v)) r • (B r : X)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, ContinuousLinearMap.coe_rangeRestrict, Set.rangeFactorization_coe] using hv.symm

variable [CompleteSpace X]

/-- Absolute convergence of the vector series associated to a rank-one expansion. -/
lemma summable_rankOne (f : ℕ → X →L[𝕜] 𝕜) (x : ℕ → X)
    (hs : Summable (fun j => ‖f j‖ * ‖x j‖)) (z : X) :
    Summable (fun j => (f j z) • x j) := by
  apply (hs.mul_right ‖z‖).of_norm_bounded
  intro j
  rw [norm_smul]
  calc
    ‖f j z‖ * ‖x j‖ ≤ (‖f j‖ * ‖z‖) * ‖x j‖ :=
      mul_le_mul_of_nonneg_right ((f j).le_opNorm z) (norm_nonneg _)
    _ = (‖f j‖ * ‖x j‖) * ‖z‖ := by ring

/-- A zero associated operator has zero trace after composition with a bounded
finite-rank operator. This uses only a finite interchange of absolutely convergent sums. -/
lemma trace_comp_finiteRank_eq_zero (f : ℕ → X →L[𝕜] 𝕜) (x : ℕ → X)
    (hs : Summable (fun j => ‖f j‖ * ‖x j‖))
    (hz : ∀ z : X, (∑' j, (f j z) • x j) = 0)
    (T : X →L[𝕜] X) (hT : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) :
    (∑' j, f j (T (x j))) = 0 := by
  obtain ⟨n, h, z, hrepr⟩ := finiteRank_eq_sum T hT
  have hsum : ∀ r : Fin n, Summable (fun j => (f j (z r)) * (h r (x j))) := by
    intro r
    simpa only [map_smul, smul_eq_mul] using
      (h r).summable (summable_rankOne f x hs (z r))
  calc
    (∑' j, f j (T (x j))) = ∑' j, ∑ r : Fin n, (f j (z r)) * (h r (x j)) := by
      apply tsum_congr
      intro j
      rw [hrepr (x j), map_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [map_smul, smul_eq_mul, mul_comm]
    _ = ∑ r : Fin n, ∑' j, (f j (z r)) * (h r (x j)) :=
      Summable.tsum_finsetSum (fun r _ => hsum r)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hh := (h r).map_tsum (summable_rankOne f x hs (z r))
      simpa only [hz, map_zero, map_smul, smul_eq_mul] using hh.symm


/-- Trace obstruction to the ordinary approximation property, over either ℝ or ℂ. -/
theorem trace_obstruction : TraceObstructionSpec.TraceObstruction := by
  intro 𝕜 _ X _ _ _ f x hs hz htrace hAP
  obtain ⟨w, hw, hwlim, hsw⟩ :=
    summable_div_null_weights (fun j => mul_nonneg (norm_nonneg (f j)) (norm_nonneg (x j))) hs
  let y : ℕ → X := fun j => ((w j / ‖x j‖ : ℝ) : 𝕜) • x j
  have hynorm : ∀ j, ‖y j‖ ≤ w j := by
    intro j
    dsimp [y]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (div_nonneg (hw j).le (norm_nonneg _))]
    by_cases hx : ‖x j‖ = 0
    · simp [hx, (hw j).le]
    · rw [div_mul_cancel₀ _ hx]
  have hylim : Tendsto y atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    exact squeeze_zero (fun _ => norm_nonneg _) hynorm hwlim
  have hyrep : ∀ j, ((‖x j‖ / w j : ℝ) : 𝕜) • y j = x j := by
    intro j
    by_cases hx : x j = 0
    · simp [y, hx]
    · dsimp [y]
      rw [smul_smul, ← RCLike.ofReal_mul]
      have heq : ‖x j‖ / w j * (w j / ‖x j‖) = 1 := by
        field_simp [ne_of_gt (hw j), norm_ne_zero_iff.mpr hx]
      rw [heq, RCLike.ofReal_one, one_smul]
  let C : ℝ := ∑' j, ‖f j‖ * ‖x j‖ / w j
  have hC : 0 ≤ C := tsum_nonneg fun j =>
    div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw j).le
  have hp : 0 < ‖∑' j, f j (x j)‖ := norm_pos_iff.mpr htrace
  let δ : ℝ := ‖∑' j, f j (x j)‖ / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (2 * (C+1)) = ‖∑' j, f j (x j)‖ :=
    div_mul_cancel₀ _ (by positivity)
  obtain ⟨T, hT, herr⟩ :=
    (Compactness.hasApproximationProperty_iff_pointwise 𝕜 X).mp hAP
      (insert 0 (Set.range y)) hylim.isCompact_insert_range δ hδ
  have herror : ∀ j, ‖x j - T (x j)‖ ≤ (‖x j‖ / w j) * δ := by
    intro j
    have hy : ‖y j - T (y j)‖ ≤ δ := by
      rw [norm_sub_rev]
      exact (herr _ (Set.mem_insert_of_mem _ (Set.mem_range_self j))).le
    have heq : x j - T (x j) = ((‖x j‖ / w j : ℝ) : 𝕜) • (y j - T (y j)) := by
      rw [smul_sub, ← map_smul, hyrep]
    rw [heq, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (hw j).le)]
    exact mul_le_mul_of_nonneg_left hy (div_nonneg (norm_nonneg _) (hw j).le)
  have hscalar : Summable (fun j => f j (x j)) :=
    hs.of_norm_bounded fun j => (f j).le_opNorm (x j)
  have hcomposed : Summable (fun j => f j (T (x j))) := by
    apply (hs.mul_left ‖T‖).of_norm_bounded
    intro j
    calc
      ‖f j (T (x j))‖ ≤ ‖f j‖ * ‖T (x j)‖ := (f j).le_opNorm _
      _ ≤ ‖f j‖ * (‖T‖ * ‖x j‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = ‖T‖ * (‖f j‖ * ‖x j‖) := by ring
  have hzero := trace_comp_finiteRank_eq_zero f x hs hz T hT
  have hsum : (∑' j, f j (x j - T (x j))) = ∑' j, f j (x j) := by
    simp only [map_sub]
    rw [hscalar.tsum_sub hcomposed, hzero, sub_zero]
  have hbound : ∀ j, ‖f j (x j - T (x j))‖ ≤ δ * (‖f j‖ * ‖x j‖ / w j) := by
    intro j
    calc
      ‖f j (x j - T (x j))‖ ≤ ‖f j‖ * ‖x j - T (x j)‖ := (f j).le_opNorm _
      _ ≤ ‖f j‖ * ((‖x j‖ / w j) * δ) :=
        mul_le_mul_of_nonneg_left (herror j) (norm_nonneg _)
      _ = δ * (‖f j‖ * ‖x j‖ / w j) := by ring
  have hle : ‖∑' j, f j (x j)‖ ≤ δ * C := by
    have hh := tsum_of_norm_bounded (hsw.mul_left δ).hasSum hbound
    rw [hsum, tsum_mul_left] at hh
    exact hh
  nlinarith

end
end ExpandedFA.AP
