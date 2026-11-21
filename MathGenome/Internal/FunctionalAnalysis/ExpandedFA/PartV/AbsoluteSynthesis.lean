import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AbsoluteSynthesis
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative absolute synthesis, `fa2:p5:absolute-synthesis`.
We first prove a ball-closure consequence of the transpose lower bound, then
sum controlled residual lifts, and finally identify the synthesis operator. -/
open scoped lp ENNReal

namespace ExpandedFA.PartV.AbsoluteSynthesis

open Set Metric Filter Finset
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The transpose lower bound forces quantitative density of images of balls. -/
theorem closedBall_subset_closure_image (T : E →L[𝕜] F) {β : ℝ} (_hβ : 0 < β)
    (hd : ∀ ℓ : F →L[𝕜] 𝕜, β * ‖ℓ‖ ≤ ‖ℓ.comp T‖)
    {r : ℝ} (hr : 0 < r) :
    closedBall (0 : F) (β * r) ⊆ closure (T '' closedBall 0 r) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  intro y hy
  by_contra hn
  have hc : Convex ℝ (closure (T '' closedBall 0 r)) :=
    ((convex_closedBall (0 : E) r).linear_image (T.restrictScalars ℝ).toLinearMap).closure
  obtain ⟨ℓ, u, hu, huy⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := 𝕜) hc isClosed_closure hn
  have hzero : (0 : F) ∈ closure (T '' closedBall 0 r) :=
    subset_closure ⟨0, by simpa using hr.le, T.map_zero⟩
  have hu0 : 0 < u := by simpa using hu 0 hzero
  have hnorm : ‖ℓ.comp T‖ ≤ u / r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro z hz
    obtain ⟨c, hc, hcz⟩ := RCLike.exists_norm_eq_mul_self (ℓ (T z))
    have hmem : (r : 𝕜) • c • z ∈ closedBall (0 : E) r := by
      simp [mem_closedBall, dist_eq_norm, norm_smul, hc, hz,
        abs_of_pos hr]
    have hh := hu _ (subset_closure (mem_image_of_mem T hmem))
    have heq : RCLike.re (ℓ (T ((r : 𝕜) • c • z))) = r * ‖ℓ (T z)‖ := by
      simp only [map_smul, smul_eq_mul, ← hcz,
        ← RCLike.ofReal_mul, RCLike.ofReal_re]
    rw [heq] at hh
    exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using hh.le)
  have hy' : ‖y‖ ≤ β * r := by simpa using hy
  have hly : RCLike.re (ℓ y) ≤ ‖ℓ‖ * (β * r) :=
    (RCLike.re_le_norm _).trans ((ℓ.le_opNorm y).trans (by gcongr))
  have hlow : β * ‖ℓ‖ * r ≤ u := (le_div_iff₀ hr).1 ((hd ℓ).trans hnorm)
  nlinarith

/-- Arbitrarily accurate lifts with the sharp coefficient budget. -/
theorem exists_approx_lift (T : E →L[𝕜] F) {β : ℝ} (hβ : 0 < β)
    (hd : ∀ ℓ : F →L[𝕜] 𝕜, β * ‖ℓ‖ ≤ ‖ℓ.comp T‖)
    (y : F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z, dist (T z) y < δ ∧ ‖z‖ ≤ β⁻¹ * ‖y‖ := by
  by_cases hy : y = 0
  · exact ⟨0, by simpa [hy] using hδ, by simp [hy]⟩
  have hr : 0 < β⁻¹ * ‖y‖ := mul_pos (inv_pos.mpr hβ) (norm_pos_iff.mpr hy)
  have hmem : y ∈ closedBall (0 : F) (β * (β⁻¹ * ‖y‖)) := by
    simp [mem_closedBall, dist_eq_norm, hβ.ne']
  obtain ⟨w, hw, hwy⟩ := Metric.mem_closure_iff.1
    (closedBall_subset_closure_image T hβ hd hr hmem) δ hδ
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, by simpa [dist_comm] using hwy, by simpa using hz⟩

/-- Summing half-size residual lifts yields an exact lift with a coarse bound. -/
theorem exists_lift_norm_le [CompleteSpace E] (T : E →L[𝕜] F) {β : ℝ}
    (hβ : 0 < β) (hd : ∀ ℓ : F →L[𝕜] 𝕜, β * ‖ℓ‖ ≤ ‖ℓ.comp T‖) (y : F) :
    ∃ z, T z = y ∧ ‖z‖ ≤ 2 * β⁻¹ * ‖y‖ := by
  have ha : ∀ w : F, ∃ z, dist (T z) w ≤ 1 / 2 * ‖w‖ ∧ ‖z‖ ≤ β⁻¹ * ‖w‖ := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw], by simp [hw]⟩
    · obtain ⟨z, hz, hzn⟩ := exists_approx_lift T hβ hd w
        (mul_pos (by norm_num) (norm_pos_iff.mpr hw) : 0 < 1 / 2 * ‖w‖)
      exact ⟨z, hz.le, hzn⟩
  choose g hg using ha
  let h (w : F) := w - T (g w)
  have hle : ∀ w, ‖h w‖ ≤ 1 / 2 * ‖w‖ := by
    intro w
    simpa [h, dist_eq_norm, norm_sub_rev] using (hg w).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ']
      calc
        ‖h (h^[n] y)‖ ≤ 1 / 2 * ‖h^[n] y‖ := hle _
        _ ≤ 1 / 2 * ((1 / 2) ^ n * ‖y‖) := by gcongr
        _ = (1 / 2) ^ (n + 1) * ‖y‖ := by ring
  let u (n : ℕ) := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (β⁻¹ * ‖y‖) := by
    intro n
    calc
      ‖u n‖ ≤ β⁻¹ * ‖h^[n] y‖ := (hg _).2
      _ ≤ β⁻¹ * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (β⁻¹ * ‖y‖) := by ring
  have sNu : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ule
      (summable_geometric_two.mul_right _)
  have su : Summable u := sNu.of_norm
  refine ⟨∑' n, u n, ?_, ?_⟩
  · have fsumeq : ∀ n : ℕ, T (∑ i ∈ range n, u i) = y - h^[n] y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ, map_add, ih, Function.iterate_succ_apply']
        simp only [h, u]
        abel
    have L₁ := (T.continuous.tendsto _).comp su.hasSum.tendsto_sum_nat
    simp only [Function.comp_def, fsumeq] at L₁
    have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
      refine tendsto_const_nhds.sub ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
      rw [← zero_mul ‖y‖]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul tendsto_const_nhds
    simpa using tendsto_nhds_unique L₁ L₂
  · calc
      ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (β⁻¹ * ‖y‖) :=
        sNu.tsum_le_tsum ule (summable_geometric_two.mul_right _)
      _ = 2 * β⁻¹ * ‖y‖ := by rw [tsum_mul_right, tsum_geometric_two]; ring

/-- One sharp approximate lift plus a small exact residual lift gives the strict
near-optimal bound. -/
theorem exists_lift_norm_lt [CompleteSpace E] (T : E →L[𝕜] F) {β : ℝ}
    (hβ : 0 < β) (hd : ∀ ℓ : F →L[𝕜] 𝕜, β * ‖ℓ‖ ≤ ‖ℓ.comp T‖)
    (y : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ z, T z = y ∧ ‖z‖ < β⁻¹ * ‖y‖ + ε := by
  obtain ⟨z₀, hz₀, hn₀⟩ := exists_approx_lift T hβ hd y
    (show 0 < β * ε / 2 by positivity)
  obtain ⟨z₁, hz₁, hn₁⟩ := exists_lift_norm_le T hβ hd (y - T z₀)
  refine ⟨z₀ + z₁, by rw [map_add, hz₁]; abel, ?_⟩
  have he : ‖y - T z₀‖ < β * ε / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hz₀
  have hsmall : 2 * β⁻¹ * ‖y - T z₀‖ < ε := by
    calc
      2 * β⁻¹ * ‖y - T z₀‖ < 2 * β⁻¹ * (β * ε / 2) := by
        gcongr
      _ = ε := by field_simp [hβ.ne']
  exact (norm_add_le _ _).trans_lt (by linarith)

variable [CompleteSpace F]

omit [CompleteSpace F] in
/-- Term norms of the synthesis series are summable for ℓ¹ coefficients. -/
theorem synthesis_summable_norm (v : ℕ → F) (hv : ∀ n, ‖v n‖ ≤ 1)
    (a : ℓ¹(ℕ, 𝕜)) : Summable (fun n => ‖a n • v n‖) := by
  have ha : Summable (fun n => ‖a n‖) := by simpa using a.property.summable
  exact ha.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hv n))

/-- The bounded synthesis map associated with a sequence in the unit ball. -/
noncomputable def synthesis (v : ℕ → F) (hv : ∀ n, ‖v n‖ ≤ 1) : ℓ¹(ℕ, 𝕜) →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' n, a n • v n
      map_add' := fun a b => by
        simpa only [lp.coeFn_add, Pi.add_apply, add_smul] using
          ((synthesis_summable_norm v hv a).of_norm.tsum_add
            (synthesis_summable_norm v hv b).of_norm)
      map_smul' := fun c a => by
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        simpa only [smul_eq_mul, mul_smul] using
          (synthesis_summable_norm v hv a).of_norm.tsum_const_smul c }
    1 (fun a => by
      have ha : Summable (fun n => ‖a n‖) := by simpa using a.property.summable
      calc
        ‖∑' n, a n • v n‖ ≤ ∑' n, ‖a n • v n‖ :=
          norm_tsum_le_tsum_norm (synthesis_summable_norm v hv a)
        _ ≤ ∑' n, ‖a n‖ := (synthesis_summable_norm v hv a).tsum_le_tsum
          (fun n => by rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hv n)) ha
        _ = 1 * ‖a‖ := by rw [lp.norm_eq_tsum_rpow (by norm_num) a]; norm_num)

@[simp] theorem synthesis_single (v : ℕ → F) (hv : ∀ n, ‖v n‖ ≤ 1) (n : ℕ) (c : 𝕜) :
    synthesis v hv (lp.single (E := fun _ : ℕ => 𝕜) 1 n c) = c • v n := by
  change (∑' i, lp.single (E := fun _ : ℕ => 𝕜) 1 n c i • v i) = _
  rw [tsum_eq_single n]
  · simp
  · intro i hi
    simp [lp.single_apply, Pi.single_eq_of_ne hi]

/-- Every vector has an exact absolutely convergent expansion with coefficient
norm arbitrarily close to the reciprocal dual lower bound. -/
theorem quantitative_absolute_synthesis : Spec.QuantitativeAbsoluteSynthesis := by
  intro 𝕜 X _ _ _ _ v β hv hβ hd x ε hε
  let T := synthesis (𝕜 := 𝕜) v hv
  have hT : ∀ ℓ : X →L[𝕜] 𝕜, β * ‖ℓ‖ ≤ ‖ℓ.comp T‖ := by
    intro ℓ
    apply (hd ℓ).trans
    apply ciSup_le
    intro n
    have hn := (ℓ.comp T).le_opNorm (lp.single (E := fun _ : ℕ => 𝕜) 1 n 1)
    simpa [T, ContinuousLinearMap.comp_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
      using hn
  obtain ⟨a, ha, han⟩ := exists_lift_norm_lt T hβ hT x hε
  refine ⟨a, ?_, synthesis_summable_norm v hv a, han⟩
  have hs := (synthesis_summable_norm v hv a).of_norm.hasSum
  change HasSum (fun n => a n • v n) (T a) at hs
  rwa [ha] at hs

end ExpandedFA.PartV.AbsoluteSynthesis

/- Mathlib proof attribution
Adapted portion near line 126:
The successive lifts and summation construction for absolute synthesis.

Upstream: Mathlib/Analysis/Normed/Operator/Banach.lean (around line 92)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
