import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MoserProfiles
import MathGenome.Internal.FourierSobolev.P102.Sobolev.TrudingerMoserBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev.TrudingerMoser
open P102.U4

lemma moserHeight_pos {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : 0 < L) :
    0 < moserHeight d L :=
  Real.rpow_pos_of_pos (div_pos hL (sharpCoefficient_pos hd)) _

lemma moserHeight_power {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : 0 ≤ L) :
    moserHeight d L ^ criticalPower d = L / sharpCoefficient d := by
  simpa only [moserHeight, one_div] using
    Real.rpow_inv_rpow (div_nonneg hL (sharpCoefficient_pos hd).le)
      (criticalPower_pos hd).ne'

/-- This checks the normalization against the source's w_L, rather than merely
naming the functions a Moser sequence. -/
lemma moserHeight_source {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : 0 ≤ L) :
    moserHeight d L = L ^ (((d : ℝ) - 1) / d) / profileScale d := by
  have hk : 1 / criticalPower d = ((d : ℝ) - 1) / d := by
    simp [criticalPower, one_div, inv_div]
  unfold moserHeight
  rw [Real.div_rpow hL (sharpCoefficient_pos hd).le]
  congr 1
  · rw [hk]
  · rw [← profileScale_criticalPower hd, one_div,
      Real.rpow_rpow_inv (profileScale_pos hd).le (criticalPower_pos hd).ne']

lemma moserFunction_nonneg {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    (R : ℝ) {L : ℝ} (hL : 0 < L) (x : Space d) :
    0 ≤ moserFunction c R L x := by
  unfold moserFunction
  apply mul_nonneg (moserHeight_pos hd hL).le
  split_ifs <;> positivity

lemma moserFunction_le_height {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    (R : ℝ) {L : ℝ} (hL : 0 < L) (x : Space d) :
    moserFunction c R L x ≤ moserHeight d L := by
  unfold moserFunction
  by_cases hx : x = c
  · simp [hx]
  · rw [ite_eq_right hx]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (moserHeight_pos hd hL).le).trans_eq
      (mul_one _)

/-- The central ball is a genuine plateau, including its center. -/
lemma moserFunction_core {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {x : Space d}
    (hx : ‖x - c‖ ≤ R * Real.exp (-L / d)) :
    moserFunction c R L x = moserHeight d L := by
  by_cases hxc : x = c
  · simp [moserFunction, hxc]
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have he : Real.exp (L / d) * ‖x - c‖ ≤ R := by
    calc
      _ ≤ Real.exp (L / d) * (R * Real.exp (-L / d)) :=
        mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = R := by
        rw [mul_left_comm, ← Real.exp_add,
          show L / (d : ℝ) + -L / d = 0 by ring, Real.exp_zero, mul_one]
  have hl : L / d ≤ Real.log (R / ‖x - c‖) :=
    (Real.le_log_iff_exp_le (div_pos hR hn)).mpr ((le_div_iff₀ hn).mpr he)
  have hlog : 1 ≤ (d : ℝ) * Real.log (R / ‖x - c‖) / L := by
    apply (le_div_iff₀ hL).mpr
    have := (div_le_iff₀ hd0).mp hl
    nlinarith
  simp only [moserFunction, ite_eq_right hxc]
  rw [min_eq_left (hlog.trans (le_max_right _ _)), mul_one]


/-- Continuity at the center follows from the plateau, and elsewhere from
continuity of the logarithm on the positive radial variable. -/
lemma continuous_moserFunction {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) : Continuous (moserFunction c R L) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hxc : x = c
  · subst x
    apply (continuousAt_const : ContinuousAt (fun _ : Space d => moserHeight d L) c).congr
    filter_upwards [Metric.ball_mem_nhds c (mul_pos hR (Real.exp_pos (-L / d)))] with y hy
    exact (moserFunction_core hd c hR hL
      (by simpa [Metric.mem_ball, dist_eq_norm] using hy.le)).symm
  · have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxc)
    have hq : R / ‖x - c‖ ≠ 0 := div_ne_zero hR.ne' hn
    have hcont : ContinuousAt (fun y : Space d => moserHeight d L *
        min 1 (max 0 ((d : ℝ) * Real.log (R / ‖y - c‖) / L))) x := by
      apply continuousAt_const.mul
      apply continuousAt_const.min
      apply continuousAt_const.max
      exact (continuousAt_const.mul
        ((continuousAt_const.div ((continuousAt_id.sub continuousAt_const).norm) hn).log hq)).div_const L
    apply hcont.congr
    filter_upwards [isOpen_ne.mem_nhds hxc] with y hy
    simp [moserFunction, hy]

/-- The plateau ball stays in any domain containing the original closed ball. -/
lemma moser_core_subset {d : ℕ} (hd : 2 ≤ d) (Ω : Opens (Space d)) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsub : Metric.closedBall c R ⊆ (Ω : Set (Space d))) :
    Metric.ball c (R * Real.exp (-L / d)) ⊆ (Ω : Set (Space d)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr : R * Real.exp (-L / d) ≤ R :=
    mul_le_of_le_one_right hR.le
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le))
  intro x hx
  apply hsub
  exact (Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hx).le.trans hr))

/-- Lebesgue volume of the central ball: its relative volume is exp(-L). -/
lemma moser_core_volume {d : ℕ} (hd : 0 < d) (c : Space d) (R L : ℝ) :
    volume (Metric.ball c (R * Real.exp (-L / d))) =
      ENNReal.ofReal (Real.exp (-L)) * volume (Metric.ball c R) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hexp : (Real.exp (-L / d)) ^ d = Real.exp (-L) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  simpa only [mul_comm R, Space, finrank_euclideanSpace, Fintype.card_fin, hexp,
    Measure.addHaar_ball_center volume c R] using
      Measure.addHaar_ball_mul_of_pos volume c (Real.exp_pos (-L / d)) R

/-- The plateau has positive measure, so the essential supremum sees its height. -/
lemma moserHeight_le_eLpNorm_top {d : ℕ} (hd : 2 ≤ d) (Ω : Opens (Space d))
    (c : Space d) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsub : Metric.closedBall c R ⊆ (Ω : Set (Space d))) :
    ENNReal.ofReal (moserHeight d L) ≤
      eLpNorm (moserFunction c R L) ⊤ (volume.restrict (Ω : Set (Space d))) := by
  let B := Metric.ball c (R * Real.exp (-L / d))
  have hB : volume B ≠ 0 :=
    (Metric.measure_ball_pos volume c (mul_pos hR (Real.exp_pos _))).ne'
  have hμ : volume.restrict B ≠ 0 := mt Measure.restrict_eq_zero.mp hB
  calc
    ENNReal.ofReal (moserHeight d L) =
        eLpNorm (fun _ : Space d => moserHeight d L) ⊤ (volume.restrict B) := by
      simp [eLpNorm_const _ (by simp : (⊤ : ℝ≥0∞) ≠ 0) hμ,
        ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (moserHeight_pos hd hL)]
    _ = eLpNorm (moserFunction c R L) ⊤ (volume.restrict B) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (moserFunction_core hd c hR hL
        (by simpa only [Metric.mem_ball, dist_eq_norm] using (Metric.mem_ball.mp hx).le)).symm
    _ ≤ _ := eLpNorm_mono_measure _
      (Measure.restrict_mono (moser_core_subset hd Ω c hR hL hsub) le_rfl)

lemma tendsto_moserHeight {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => moserHeight d ((n : ℝ) + 1)) atTop atTop := by
  exact (tendsto_rpow_atTop (one_div_pos.mpr (criticalPower_pos hd))).comp
    ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const (sharpCoefficient_pos hd))

lemma tendsto_moserFunction_eLpNorm_top {d : ℕ} (hd : 2 ≤ d) (Ω : Opens (Space d))
    (c : Space d) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall c R ⊆ (Ω : Set (Space d))) :
    Tendsto (fun n : ℕ => eLpNorm (moserFunction c R ((n : ℝ) + 1)) ⊤
      (volume.restrict (Ω : Set (Space d)))) atTop (𝓝 ⊤) := by
  exact tendsto_nhds_top_mono' (ENNReal.tendsto_ofReal_atTop.comp (tendsto_moserHeight hd))
    (fun n => moserHeight_le_eLpNorm_top hd Ω c hR (by positivity) hsub)

/-- Contribution of the constant central ball, with the sharp coefficient
and the original ball's volume kept exactly. -/
lemma moser_exponential_lower {d : ℕ} (hd : 2 ≤ d) (Ω : Opens (Space d))
    (c : Space d) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsub : Metric.closedBall c R ⊆ (Ω : Set (Space d))) (α : ℝ) :
    volume (Metric.ball c R) *
        ENNReal.ofReal (Real.exp ((α / sharpCoefficient d - 1) * L)) ≤
      exponentialIntegral Ω α (moserFunction c R L) := by
  let B := Metric.ball c (R * Real.exp (-L / d))
  calc
    _ = ENNReal.ofReal (Real.exp (α * (L / sharpCoefficient d))) * volume B := by
      dsimp only [B]
      rw [moser_core_volume (by omega) c R L, ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        show α * (L / sharpCoefficient d) + -L =
          (α / sharpCoefficient d - 1) * L by ring, mul_comm]
    _ = ∫⁻ x in B, ENNReal.ofReal
        (Real.exp (α * ‖moserFunction c R L x‖ ^ criticalPower d)) := by
      calc
        _ = ∫⁻ _ in B, ENNReal.ofReal (Real.exp (α * (L / sharpCoefficient d))) := by simp
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          rw [moserFunction_core hd c hR hL
            (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le),
            Real.norm_eq_abs, abs_of_pos (moserHeight_pos hd hL), moserHeight_power hd hL.le]
    _ ≤ _ := lintegral_mono_set (moser_core_subset hd Ω c hR hL hsub)

lemma tendsto_moserFunction_exponential {d : ℕ} (hd : 2 ≤ d) (Ω : Opens (Space d))
    (c : Space d) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall c R ⊆ (Ω : Set (Space d)))
    {α : ℝ} (hα : sharpCoefficient d < α) :
    Tendsto (fun n : ℕ => exponentialIntegral Ω α (moserFunction c R ((n : ℝ) + 1)))
      atTop (𝓝 ⊤) := by
  have ha := sharpCoefficient_pos hd
  have hr : 0 < α / sharpCoefficient d - 1 := by
    exact sub_pos.mpr ((lt_div_iff₀ ha).mpr (by simpa using hα))
  have hV : 0 < volume.real (Metric.ball c R) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume c hR).ne' measure_ball_lt_top.ne
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (volume.real (Metric.ball c R) * Real.exp ((α / sharpCoefficient d - 1) * ((n : ℝ) + 1))))
      atTop (𝓝 ⊤) := by
    apply ENNReal.tendsto_ofReal_atTop.comp
    exact (Real.tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hr)).const_mul_atTop hV
  apply tendsto_nhds_top_mono' hlim
  intro n
  dsimp only
  rw [ENNReal.ofReal_mul hV.le, ofReal_measureReal]
  exact moser_exponential_lower hd Ω c hR (by positivity) hsub α

end P102.Sobolev.TrudingerMoser

namespace P102.Sobolev
open P102.U4 TrudingerMoser

/-- Elementary concentration of the source's explicit continuous profiles. -/
theorem moser_profiles_divergence : MoserProfilesExpected.ProfileDivergence := by
  intro d hd Ω c R hR hsub
  exact ⟨fun L hL => continuous_moserFunction hd c hR hL,
    tendsto_moserFunction_eLpNorm_top hd Ω c hR hsub,
    fun _ hα => tendsto_moserFunction_exponential hd Ω c hR hsub hα⟩

end P102.Sobolev
