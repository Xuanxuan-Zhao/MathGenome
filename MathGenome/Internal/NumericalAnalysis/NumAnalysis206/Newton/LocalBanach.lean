import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.LocalBanach
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.LocalBanachStep
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace NumAnalysis206.Newton

/-- Iterating the one-step estimate proves local applicability and convergence. -/
theorem local_banach : Specs.NumAnalysis206.Newton.LocalBanachStatement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U p A L R r hU hF hp hA hball hL hLip hr hrR
  dsimp only
  intro hsmall hratio x₀ hx₀
  let b := ‖A.symm.toContinuousLinearMap‖
  let c := b * L / (2 * (1 - b * L * r))
  let q := c * r
  let x := Specs.NumAnalysis206.Newton.operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (norm_nonneg _) hL)
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
  have hq0 : 0 ≤ q := mul_nonneg hc hr.le
  have hq1 : q < 1 := by
    calc
      q = b * L * r / (2 * (1 - b * L * r)) := by dsimp [q, c]; ring
      _ < 1 := hratio
  have hs := local_banach_step 𝕜 X Y F U p A L R r hU hF hp hA hball hL hLip hr hrR hsmall
  have hsucc (n : ℕ) : x (n + 1) = operatorNewton (𝕜 := 𝕜) F (x n) :=
    operatorNewtonIterates_succ F x₀ n
  have hlinear (z : X) (hz : z ∈ Metric.closedBall p r) :
      ‖operatorNewton (𝕜 := 𝕜) F z - p‖ ≤ q * ‖z - p‖ := by
    have he : ‖z - p‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    calc
      ‖operatorNewton (𝕜 := 𝕜) F z - p‖ ≤ c * ‖z - p‖ ^ 2 := (hs z hz).2.2.2
      _ ≤ c * (r * ‖z - p‖) := mul_le_mul_of_nonneg_left
        (by nlinarith [norm_nonneg (z - p)]) hc
      _ = q * ‖z - p‖ := by dsimp [q]; ring
  have hmem (n : ℕ) : x n ∈ Metric.closedBall p r := by
    induction n with
    | zero => exact hx₀
    | succ n ih =>
      rw [Metric.mem_closedBall, dist_eq_norm, hsucc]
      calc
        ‖operatorNewton (𝕜 := 𝕜) F (x n) - p‖ ≤ q * ‖x n - p‖ := hlinear _ ih
        _ ≤ 1 * ‖x n - p‖ := mul_le_mul_of_nonneg_right hq1.le (norm_nonneg _)
        _ ≤ r := by simpa only [one_mul, ← dist_eq_norm, ← Metric.mem_closedBall] using ih
  have hquad (n : ℕ) : ‖x (n + 1) - p‖ ≤ c * ‖x n - p‖ ^ 2 := by
    rw [hsucc]
    exact (hs (x n) (hmem n)).2.2.2
  have hgeom (n : ℕ) : ‖x n - p‖ ≤ q ^ n * ‖x₀ - p‖ := by
    induction n with
    | zero => simp [x, Specs.NumAnalysis206.Newton.operatorNewtonIteratesValue,
        Specs.NumAnalysis206.Newton.exactIteratesValue]
    | succ n ih =>
      rw [hsucc]
      calc
        ‖operatorNewton (𝕜 := 𝕜) F (x n) - p‖ ≤ q * ‖x n - p‖ := hlinear _ (hmem n)
        _ ≤ q * (q ^ n * ‖x₀ - p‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (n + 1) * ‖x₀ - p‖ := by rw [pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hmem n, (hs (x n) (hmem n)).1, (hs (x n) (hmem n)).2.1, hquad n⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [dist_eq_norm]
    apply squeeze_zero (fun n => norm_nonneg (x n - p)) hgeom
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖x₀ - p‖
  · intro hzero n
    have hz := hquad n
    simp only [c, hzero, mul_zero, zero_div, zero_mul] at hz
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))
  · intro N hN k
    change x N = p at hN
    have habs := exactIterates_absorbing_after_root F
      (Specs.NumAnalysis206.Newton.operatorNewtonValue (𝕜 := 𝕜) F) x₀ N
      (by change F (x N) = 0; rw [hN, hp]) k
    exact habs.trans hN

/-- An explicit small-radius choice avoids dividing by the Lipschitz constant. -/
theorem local_banach_radius : Specs.NumAnalysis206.Newton.LocalBanachRadiusStatement := by
  intro b L R hb hL hR
  let r := min R (1 / (4 * (b * L + 1)))
  have hbl : 0 ≤ b * L := mul_nonneg hb hL
  have hd : 0 < 4 * (b * L + 1) := by positivity
  have hr : 0 < r := lt_min hR (one_div_pos.mpr hd)
  have hbound : r * (4 * (b * L + 1)) ≤ 1 :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have ht : b * L * r < 1 / 4 := by nlinarith
  refine ⟨r, hr, min_le_left _ _, by linarith, ?_⟩
  apply (div_lt_one (by linarith : 0 < 2 * (1 - b * L * r))).mpr
  linarith

end NumAnalysis206.Newton
