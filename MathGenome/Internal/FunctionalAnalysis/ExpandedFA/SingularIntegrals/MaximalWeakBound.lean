import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.MaximalWeakBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.SingularIntegrals

/-- The centered Hardy–Littlewood maximal function. Its extended range is
necessary: an integrable function can have infinite maximal value at a point. -/
def centeredMaximal : MaximalWeakBoundSpec.MaximalType.{u,v} :=
  fun μ f x => ⨆ r : ℝ, ⨆ (_ : 0 < r),
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r)

theorem centeredMaximal_congr : MaximalWeakBoundSpec.Congruence.{u,v} := by
  intro X F _ _ _ μ f g hfg
  funext x
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with y hy
  rw [hy]

/-- Strict superlevel sets are open: a ball witnessing a strict inequality
can be enlarged slightly, and then still witnesses it at every nearby center. -/
theorem centeredMaximal_lowerSemicontinuous
    {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → F) : LowerSemicontinuous (centeredMaximal μ f) := by
  intro x a hax
  change a < ⨆ r : ℝ, ⨆ (_ : 0 < r),
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r) at hax
  simp only [lt_iSup_iff] at hax
  obtain ⟨r, hr, har⟩ := hax
  have hat : a ≠ ∞ := (har.trans_le le_top).ne
  let A : ℝ → ℝ≥0∞ := fun R =>
    ENNReal.ofReal (a.toReal * R ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1))
  have hA (z : E) (R : ℝ) (hR : 0 < R) : A R = a * μ (ball z R) := by
    dsimp [A, Measure.real]
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hR.le _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hat, ENNReal.ofReal_pow hR.le,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne, μ.addHaar_ball_of_pos z hR]
    simp only [mul_assoc, ENNReal.ofReal_pow hR.le]
  have hAc : Continuous A := ENNReal.continuous_ofReal.comp
    ((continuous_const.mul (continuous_id.pow _)).mul continuous_const)
  have hAr : A r < ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
    rw [hA x r hr]
    exact ENNReal.mul_lt_of_lt_div har
  obtain ⟨R, hrR, hAR⟩ := (hAc.tendsto r |>.eventually_lt_const hAr).exists_gt
  have hR : 0 < R := hr.trans hrR
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrR)] with y hy
  have hsub : ball x r ⊆ ball y R := by
    apply ball_subset_ball'
    have hd := mem_ball.mp hy
    rw [dist_comm] at hd
    linarith
  have hgood : a < (∫⁻ z in ball y R, ‖f z‖ₑ ∂μ) / μ (ball y R) := by
    apply (ENNReal.lt_div_iff_mul_lt
      (Or.inl (measure_ball_pos μ y hR).ne') (Or.inl measure_ball_lt_top.ne)).mpr
    rw [← hA y R hR]
    exact hAR.trans_le (lintegral_mono_set hsub)
  exact hgood.trans_le (le_iSup_of_le R (le_iSup_of_le hR le_rfl))

theorem centeredMaximal_measurable : MaximalWeakBoundSpec.MeasurableMaximal.{v} := by
  intro d F _ f
  exact (centeredMaximal_lowerSemicontinuous volume f).measurable

/-- The geometric covering estimate, for any nonnegative integrand and any
additive Haar measure on a finite dimensional real normed space. -/
theorem measure_goodBall_centers_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (g : E → ℝ≥0∞)
    (a : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ∞) :
    μ {x | ∃ r : ℝ, 0 < r ∧ a < (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r)} ≤
      (5 : ℝ≥0∞) ^ Module.finrank ℝ E * (∫⁻ y, g y ∂μ) / a := by
  classical
  have hbounded (R : ℝ) :
      μ {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
        a < (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r)} ≤
      (5 : ℝ≥0∞) ^ Module.finrank ℝ E * (∫⁻ y, g y ∂μ) / a := by
    let t : Set (E × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ R ∧
      a < (∫⁻ y in ball p.1 p.2, g y ∂μ) / μ (ball p.1 p.2)}
    obtain ⟨u, hut, hdisj, hcover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_ball t Prod.fst Prod.snd R
        (fun p hp => hp.2.1) 5 (by norm_num)
    have hcount : u.Countable := hdisj.countable_of_nonempty_interior (by
      intro p hp
      rw [isOpen_ball.interior_eq]
      exact nonempty_ball.mpr (hut hp).1)
    have : Countable u := hcount.to_subtype
    have hsub : {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
        a < (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r)} ⊆
        ⋃ p : u, ball p.val.1 (5 * p.val.2) := by
      rintro x ⟨r, hr, hrR, har⟩
      obtain ⟨p, hp, hxp⟩ := hcover (x, r) ⟨hr, hrR, har⟩
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp (mem_ball_self hr)⟩
    have hball (p : u) : μ (ball p.val.1 p.val.2) ≤
        (∫⁻ y in ball p.val.1 p.val.2, g y ∂μ) / a := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).mpr
      exact (ENNReal.mul_lt_of_lt_div' (hut p.property).2.2).le
    calc
      μ _ ≤ μ (⋃ p : u, ball p.val.1 (5 * p.val.2)) := measure_mono hsub
      _ ≤ ∑' p : u, μ (ball p.val.1 (5 * p.val.2)) := measure_iUnion_le _
      _ = ∑' p : u, (5 : ℝ≥0∞) ^ Module.finrank ℝ E * μ (ball p.val.1 p.val.2) := by
        apply tsum_congr
        intro p
        rw [μ.addHaar_ball_mul_of_pos _ (by norm_num : (0 : ℝ) < 5),
          μ.addHaar_ball_center p.val.1 p.val.2,
          ENNReal.ofReal_pow (by norm_num)]
        norm_num
      _ = (5 : ℝ≥0∞) ^ Module.finrank ℝ E * ∑' p : u, μ (ball p.val.1 p.val.2) :=
        ENNReal.tsum_mul_left
      _ ≤ (5 : ℝ≥0∞) ^ Module.finrank ℝ E *
          ∑' p : u, (∫⁻ y in ball p.val.1 p.val.2, g y ∂μ) / a := by
        gcongr with p
        exact hball p
      _ = (5 : ℝ≥0∞) ^ Module.finrank ℝ E *
          (∫⁻ y in ⋃ p : u, ball p.val.1 p.val.2, g y ∂μ) / a := by
        have hlin : (∫⁻ y in ⋃ p : u, ball p.val.1 p.val.2, g y ∂μ) =
            ∑' p : u, ∫⁻ y in ball p.val.1 p.val.2, g y ∂μ := by
          apply lintegral_iUnion (fun _ => measurableSet_ball)
          intro p q hpq
          exact hdisj p.property q.property (Subtype.coe_ne_coe.mpr hpq)
        simp_rw [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, ← hlin, mul_assoc]
      _ ≤ (5 : ℝ≥0∞) ^ Module.finrank ℝ E * (∫⁻ y, g y ∂μ) / a := by
        gcongr
        exact Measure.restrict_le_self
  let s : ℕ → Set E := fun n => {x | ∃ r : ℝ, 0 < r ∧ r ≤ (n : ℝ) ∧
    a < (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r)}
  have hs : Monotone s := by
    intro m n hmn x hx
    obtain ⟨r, hr, hrm, har⟩ := hx
    exact ⟨r, hr, hrm.trans (Nat.cast_le.mpr hmn), har⟩
  have hset : {x | ∃ r : ℝ, 0 < r ∧
      a < (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r)} = ⋃ n, s n := by
    ext x
    constructor
    · rintro ⟨r, hr, har⟩
      obtain ⟨n, hn⟩ := exists_nat_ge r
      exact mem_iUnion.mpr ⟨n, r, hr, hn, har⟩
    · rintro ⟨_, ⟨n, rfl⟩, r, hr, _hrn, har⟩
      exact ⟨r, hr, har⟩
  rw [hset, hs.measure_iUnion]
  exact iSup_le fun n => hbounded n

theorem centeredMaximal_ballIntegral : MaximalWeakBoundSpec.BallIntegralFormula.{v} := by
  intro d F _ f hf x
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  have hi : IntegrableOn f (ball x r) volume :=
    (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  change (∫⁻ y in ball x r, ‖f y‖ₑ) / volume (ball x r) =
    ENNReal.ofReal ((volume (ball x r)).toReal⁻¹ * ∫ y in ball x r, ‖f y‖)
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ofReal_integral_norm_eq_lintegral_enorm hi]
  rw [ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  · exact ENNReal.div_eq_inv_mul
  · exact ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

theorem centeredMaximal_weak : MaximalWeakBoundSpec.WeakBound.{v} := by
  intro d F _ f hf a ha
  have hset : {x | ENNReal.ofReal a < MaximalWeakBoundSpec.MaximalValue volume f x} =
      {x | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal a <
        (∫⁻ y in ball x r, ‖f y‖ₑ) / volume (ball x r)} := by
    ext x
    simp only [MaximalWeakBoundSpec.MaximalValue, mem_ofPred_eq, lt_iSup_iff, exists_prop]
  rw [hset, ofReal_integral_norm_eq_lintegral_enorm hf]
  simpa using measure_goodBall_centers_le volume (fun x => ‖f x‖ₑ)
    (ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top

theorem centeredMaximal_infinity_pointwise :
    MaximalWeakBoundSpec.InfinityPointwiseBound.{v} := by
  intro d F _ f hf x
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply (ENNReal.div_le_iff (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne).mpr
  calc
    (∫⁻ y in ball x r, ‖f y‖ₑ) ≤ ∫⁻ _y in ball x r, eLpNorm f ∞ volume := by
      apply lintegral_mono_ae
      apply ae_restrict_of_ae
      simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using
        (ae_le_eLpNormEssSup (f := f) (μ := volume))
    _ = eLpNorm f ∞ volume * volume (ball x r) := by simp

theorem centeredMaximal_infinity : MaximalWeakBoundSpec.InfinityBound.{v} := by
  intro d F _ f hf
  exact essSup_le_of_ae_le _ (Filter.Eventually.of_forall
    (centeredMaximal_infinity_pointwise d f hf))

end ExpandedFA.SingularIntegrals
