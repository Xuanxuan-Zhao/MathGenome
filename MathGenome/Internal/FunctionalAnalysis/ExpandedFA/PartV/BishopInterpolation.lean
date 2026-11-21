import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.BishopInterpolation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.BishopRestrictionIsometry
import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact Bishop interpolation from the accepted ball-image density theorem.
The domain is complete because the subspace is norm closed. The series
argument below removes the closure of the image, with strict norm control. -/

noncomputable section

namespace ExpandedFA.PartV.BishopInterpolation

open Set Filter Finset
open scoped Topology
open BishopRestrictionIsometrySpec BishopInterpolationSpec

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 G] [CompleteSpace E]

/-- A preliminary exact lift with a fixed norm bound. Only the domain must
be complete. Approximate lifts are iterated on the residual, whose norm
decreases geometrically. -/
lemma exists_preimage_norm_le_four
    (T : E →L[𝕜] G)
    (hd : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : G) r ⊆
      closure (T '' Metric.ball (0 : E) r)) (x : G) :
    ∃ y : E, T y = x ∧ ‖y‖ ≤ 4 * ‖x‖ := by
  classical
  have ha : ∀ v : G, ∃ y : E,
      ‖v - T y‖ ≤ (1 / 2 : ℝ) * ‖v‖ ∧ ‖y‖ ≤ 2 * ‖v‖ := by
    intro v
    by_cases hv : v = 0
    · subst v
      exact ⟨0, by simp, by simp⟩
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hc : v ∈ closure (T '' Metric.ball (0 : E) (2 * ‖v‖)) :=
      hd _ (by positivity) (by rw [mem_closedBall_zero_iff]; linarith)
    obtain ⟨w, ⟨y, hy, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp hc
      (‖v‖ / 2) (by positivity)
    refine ⟨y, ?_, (mem_ball_zero_iff.mp hy).le⟩
    rw [dist_eq_norm] at hw
    linarith
  choose a ha using ha
  let residual (v : G) := v - T (a v)
  have hres (n : ℕ) : ‖residual^[n] x‖ ≤ (1 / 2 : ℝ) ^ n * ‖x‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖residual (residual^[n] x)‖ ≤ (1 / 2 : ℝ) * ‖residual^[n] x‖ :=
          (ha _).1
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * ‖x‖) := by gcongr
        _ = (1 / 2 : ℝ) ^ (n + 1) * ‖x‖ := by ring
  let term (n : ℕ) := a (residual^[n] x)
  have ht (n : ℕ) : ‖term n‖ ≤ (1 / 2 : ℝ) ^ n * (2 * ‖x‖) := by
    calc
      ‖term n‖ ≤ 2 * ‖residual^[n] x‖ := (ha _).2
      _ ≤ 2 * ((1 / 2 : ℝ) ^ n * ‖x‖) := by gcongr; exact hres n
      _ = (1 / 2 : ℝ) ^ n * (2 * ‖x‖) := by ring
  have hns : Summable (fun n => ‖term n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ht
      (summable_geometric_two.mul_right _)
  have hs : Summable term := hns.of_norm
  refine ⟨∑' n, term n, ?_, ?_⟩
  · have htel (n : ℕ) : T (∑ i ∈ range n, term i) = x - residual^[n] x := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ, map_add, ih, Function.iterate_succ_apply']
        dsimp [term, residual]
        abel
    have hzero : Tendsto (fun n => residual^[n] x) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      apply squeeze_zero (fun _ => norm_nonneg _) hres
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num :
        (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖x‖
    have h₁ : Tendsto (fun n => T (∑ i ∈ range n, term i)) atTop
        (𝓝 (T (∑' n, term n))) :=
      T.continuous.continuousAt.tendsto.comp hs.hasSum.tendsto_sum_nat
    have h₂ := tendsto_const_nhds.sub hzero (a := x)
    simp only [htel] at h₁
    exact (tendsto_nhds_unique h₁ h₂).trans (sub_zero x)
  · calc
      ‖∑' n, term n‖ ≤ ∑' n, ‖term n‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (2 * ‖x‖) :=
        hns.tsum_le_tsum ht (summable_geometric_two.mul_right _)
      _ = 4 * ‖x‖ := by rw [tsum_mul_right, tsum_geometric_two]; ring

/-- Ball-image density at every radius gives an exact lift within any
strictly larger norm budget. A first approximation uses most of the budget;
the preliminary exact-lifting bound handles its small residual. -/
lemma exists_preimage_norm_lt
    (T : E →L[𝕜] G)
    (hd : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : G) r ⊆
      closure (T '' Metric.ball (0 : E) r))
    (x : G) {r : ℝ} (hx : ‖x‖ < r) :
    ∃ y : E, T y = x ∧ ‖y‖ < r := by
  obtain ⟨s, hxs, hsr⟩ := exists_between hx
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg x) hxs
  have hc := hd s hs (mem_closedBall_zero_iff.mpr hxs.le)
  obtain ⟨w, ⟨y, hy, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp hc
    ((r - s) / 4) (by linarith)
  obtain ⟨z, hz, hzn⟩ := exists_preimage_norm_le_four T hd (x - T y)
  refine ⟨y + z, by rw [map_add, hz]; abel, ?_⟩
  have hyn := mem_ball_zero_iff.mp hy
  rw [dist_eq_norm] at hw
  have : ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le _ _
  linarith

/-- Contractivity supplies the other inclusion in the equality of balls. -/
lemma image_ball_eq_of_density
    (T : E →L[𝕜] G) (hcontract : ∀ y, ‖T y‖ ≤ ‖y‖)
    (hd : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : G) r ⊆
      closure (T '' Metric.ball (0 : E) r)) (r : ℝ) :
    T '' Metric.ball (0 : E) r = Metric.ball (0 : G) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_ball_zero_iff.mpr ((hcontract y).trans_lt (mem_ball_zero_iff.mp hy))
  · intro hx
    obtain ⟨y, hy, hyn⟩ := exists_preimage_norm_lt T hd x (mem_ball_zero_iff.mp hx)
    exact ⟨y, mem_ball_zero_iff.mpr hyn, hy⟩

/-- Apply exact lifting to the shared real or complex restriction map.
All measure hypotheses remain the upstream total-variation condition. -/
lemma interpolation_of_density
    {𝕜 : Type} [RCLike 𝕜] (hd : BallImageDensity.{u} 𝕜) :
    Interpolation.{u} 𝕜 := by
  intro K _ _ _ _ _ Y hY F hF
  let : CompleteSpace Y := hY.completeSpace_coe
  have hd' := hd K Y hY F hF
  refine ⟨image_ball_eq_of_density (restriction Y F)
    (BishopRestrictionIsometry.restriction_norm_le Y F) hd' 1, ?_⟩
  intro g
  obtain ⟨y, hy, _⟩ := exists_preimage_norm_lt (restriction Y F) hd' g
    (lt_add_one ‖g‖)
  exact ⟨y, hy⟩

theorem real_interpolation : RealInterpolation.{u} :=
  interpolation_of_density BishopRestrictionIsometry.real_ball_image_density

theorem complex_interpolation : ComplexInterpolation.{u} :=
  interpolation_of_density BishopRestrictionIsometry.complex_ball_image_density

end ExpandedFA.PartV.BishopInterpolation
