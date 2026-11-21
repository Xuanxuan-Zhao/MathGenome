import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeanErgodic
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.HilbertProjection
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace D13Unified.Ch19.MeanErgodic
open Filter Topology
open Specs.D13Unified.Ch19.MeanErgodic
open scoped ComplexConjugate
universe u v
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] (U : H →ₗᵢ[𝕜] H)

@[simp] theorem mem_fixedSpace (h : H) : h ∈ fixedSpace U ↔ U h = h := by
  simp [fixedSpace, sub_eq_zero]

theorem fixedSpace_closed : IsClosed (fixedSpace U : Set H) :=
  (U.toContinuousLinearMap - ContinuousLinearMap.id 𝕜 H).isClosed_ker

theorem coboundary_orthogonal : (coboundarySpace U)ᗮ = fixedSpace U := by
  ext h
  rw [coboundarySpace, Submodule.orthogonal_closure, Submodule.mem_orthogonal',
    mem_fixedSpace]
  constructor
  · intro hh
    have hi : inner 𝕜 h (h - U h) = 0 := hh _ ⟨h, rfl⟩
    have hi' : inner 𝕜 h (U h) = inner 𝕜 h h := by
      exact (sub_eq_zero.mp (by simpa only [inner_sub_right] using hi)).symm
    have hn : ‖h - U h‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := 𝕜), hi', U.norm_map, inner_self_eq_norm_sq_to_K]
      simp
      ring
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))).symm
  · intro hh y hy
    obtain ⟨g, rfl⟩ := hy
    change inner 𝕜 h (g - U g) = 0
    have hi : inner 𝕜 h (U g) = inner 𝕜 h g := by
      calc
        inner 𝕜 h (U g) = inner 𝕜 (U h) (U g) := by rw [hh]
        _ = inner 𝕜 h g := U.inner_map_map h g
    rw [inner_sub_right, hi, sub_self]

@[simp] theorem average_apply (n : ℕ) (h : H) :
    average U n h = (n : 𝕜)⁻¹ • ∑ j ∈ Finset.range n, (U ^ j) h := by
  simp [average]

theorem average_norm_le (n : ℕ) (h : H) : ‖average U n h‖ ≤ ‖h‖ := by
  rw [average_apply, norm_smul, norm_inv, RCLike.norm_natCast]
  calc
    (n : ℝ)⁻¹ * ‖∑ j ∈ Finset.range n, (U ^ j) h‖ ≤
        (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ‖(U ^ j) h‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (n : ℝ)⁻¹ * ((n : ℝ) * ‖h‖) := by simp
    _ ≤ ‖h‖ := by
      by_cases hn : n = 0
      · simp [hn]
      · rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

theorem average_telescopes (n : ℕ) (g : H) :
    average U n (g - U g) = (n : 𝕜)⁻¹ • (g - (U ^ n) g) := by
  rw [average_apply]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, map_sub, pow_succ]
    change g - (U ^ n) g + ((U ^ n) g - (U ^ n) (U g)) =
      g - (U ^ n) (U g)
    abel

theorem average_coboundary_bound (n : ℕ) (g : H) :
    ‖average U n (g - U g)‖ ≤ 2 * ‖g‖ / (n : ℝ) := by
  rw [average_telescopes, norm_smul, norm_inv, RCLike.norm_natCast]
  calc
    (n : ℝ)⁻¹ * ‖g - (U ^ n) g‖ ≤ (n : ℝ)⁻¹ * (‖g‖ + ‖(U ^ n) g‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = 2 * ‖g‖ / (n : ℝ) := by rw [(U ^ n).norm_map]; ring

theorem average_fixed (n : ℕ) (hn : n ≠ 0) (h : H) (hh : U h = h) :
    average U n h = h := by
  have hp : ∀ j : ℕ, (U ^ j) h = h := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      change (U ^ j) (U h) = h
      rw [hh, ih]
  rw [average_apply]
  simp only [hp, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn),
    one_smul]

theorem average_coboundary_tendsto (g : H) :
    Tendsto (fun n => average U n (g - U g)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => average_coboundary_bound U n g)
    (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖g‖))

theorem average_lipschitz (n : ℕ) : LipschitzWith 1 (average U n) := by
  apply LipschitzWith.of_dist_le_mul
  intro h g
  simpa only [one_mul, NNReal.coe_one, dist_eq_norm, ← map_sub] using
    average_norm_le U n (h - g)

theorem average_closure_tendsto (h : H) (hh : h ∈ coboundarySpace U) :
    Tendsto (fun n => average U n h) atTop (𝓝 0) := by
  have hc : IsClosed {h : H | Tendsto (fun n => average U n h) atTop (𝓝 (0 : H))} :=
    ((LipschitzWith.uniformEquicontinuous (fun n => (average U n : H → H)) 1
      (average_lipschitz U)).equicontinuous).isClosed_setOfPred_tendsto continuous_const
  apply closure_minimal (t := {h : H | Tendsto (fun n => average U n h) atTop (𝓝 (0 : H))})
    ?_ hc hh
  rintro _ ⟨g, rfl⟩
  exact average_coboundary_tendsto U g

variable [CompleteSpace H]

theorem fixed_orthogonal : (fixedSpace U)ᗮ = coboundarySpace U := by
  let : CompleteSpace (coboundarySpace U) :=
    (LinearMap.range (LinearMap.id - U.toLinearMap)).isClosed_topologicalClosure.isComplete.completeSpace_coe
  rw [← coboundary_orthogonal U]
  exact (coboundarySpace U).orthogonal_orthogonal

theorem fixed_coboundary_complement : IsCompl (fixedSpace U) (coboundarySpace U) := by
  rw [← fixed_orthogonal U]
  exact (HilbertProjection.closed_subspace_projection 𝕜 H (fixedSpace U)
    (fixedSpace_closed U)).1

theorem average_tendsto_projection (h : H) :
    Tendsto (fun n => average U n h) atTop (𝓝 (fixedProjection U h)) := by
  let : CompleteSpace (fixedSpace U) := (fixedSpace_closed U).isComplete.completeSpace_coe
  have hp : fixedProjection U h ∈ fixedSpace U :=
    (fixedSpace U).starProjection_apply_mem h
  have hz : h - fixedProjection U h ∈ coboundarySpace U := by
    rw [← fixed_orthogonal U]
    exact (fixedSpace U).sub_starProjection_mem_orthogonal h
  have ha : Tendsto (fun n => average U n (fixedProjection U h)) atTop
      (𝓝 (fixedProjection U h)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (average_fixed U n hn _ ((mem_fixedSpace U _).mp hp)).symm
  have ht := ha.add (average_closure_tendsto U _ hz)
  simpa only [← map_add, add_sub_cancel, add_zero] using ht

/-- Mean ergodic theorem for arbitrary real or complex Hilbert-space isometries. -/
theorem mean_ergodic : Specs.D13Unified.Ch19.MeanErgodic.mean_ergodic_type := by
  intro 𝕜 H _ _ _ _ U
  exact ⟨fixedSpace_closed U, coboundary_orthogonal U, fixed_coboundary_complement U,
    average_norm_le U, fun n g => ⟨average_telescopes U n g, average_coboundary_bound U n g⟩,
    average_tendsto_projection U⟩

end D13Unified.Ch19.MeanErgodic
