import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.BMOQuotient
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Group.Completeness

/-!
BMO on Euclidean space for paper.tex:18406–18430. Canonical definitions live
in the independent Spec. The explicit quotient by a.e. constants is a normed
Banach space with the displayed mean-oscillation norm. The canonical map from
L∞ is continuous and has norm at most two. The logarithm is locally integrable,
has finite BMO seminorm, and is essentially unbounded in positive dimension.

Completeness follows from absolute series: normalize each representative on the
unit ball, bound its local L¹ norm by its BMO norm, and use L¹ completeness on
every ball for the ordinary pointwise sum. Local L¹ convergence preserves the
uniform oscillation bounds, giving BMO convergence of the partial sums.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.Hardy

abbrev Point := BMOQuotientSpec.Point

def ballMean {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜)
    (x : Point d) (r : ℝ) : 𝕜 := BMOQuotientSpec.MeanValue f x r

def meanOscillation {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜)
    (x : Point d) (r : ℝ) : ℝ≥0∞ := BMOQuotientSpec.MeanOscillationValue f x r

def bmoENorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜) : ℝ≥0∞ :=
  BMOQuotientSpec.BMOENormValue f

abbrev BMOFunction : BMOQuotientSpec.BMOFunctionType := BMOQuotientSpec.BMOFunctionValue

def ModConstants : BMOQuotientSpec.ModConstantsType := BMOQuotientSpec.ModConstantsValue

abbrev BMO : BMOQuotientSpec.BMOType := BMOQuotientSpec.BMOValue

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Local integrability includes integrability on every ball, by compact closure. -/
theorem integrableOn_ball_of_locallyIntegrable {f : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (x : Point d) (r : ℝ) :
    IntegrableOn f (Metric.ball x r) volume :=
  (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall

theorem ballMean_congr_ae {f g : Point d → 𝕜} (h : f =ᵐ[volume] g)
    (x : Point d) (r : ℝ) : ballMean f x r = ballMean g x r := by
  unfold ballMean BMOQuotientSpec.MeanValue
  rw [integral_congr_ae (ae_restrict_of_ae h)]

theorem meanOscillation_congr_ae {f g : Point d → 𝕜} (h : f =ᵐ[volume] g)
    (x : Point d) (r : ℝ) : meanOscillation f x r = meanOscillation g x r := by
  change (volume (Metric.ball x r))⁻¹ * (∫⁻ y in Metric.ball x r,
    ‖f y - ballMean f x r‖ₑ) =
      (volume (Metric.ball x r))⁻¹ * (∫⁻ y in Metric.ball x r, ‖g y - ballMean g x r‖ₑ)
  rw [ballMean_congr_ae h]
  congr 1
  apply lintegral_congr_ae
  exact (ae_restrict_of_ae h).mono fun _ hx =>
    congrArg (fun z : 𝕜 => ‖z - ballMean g x r‖ₑ) hx

theorem bmoENorm_congr_ae : BMOQuotientSpec.AeInvariance := by
  intro d 𝕜 _ f g h
  unfold BMOQuotientSpec.BMOENormValue
  congr 1
  funext x
  congr 1
  funext r
  congr 1
  funext _
  exact meanOscillation_congr_ae h x r

/-- Equality in the quotient is precisely a.e. equality up to a single constant. -/
theorem bmo_class_eq_iff (f g : BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf f = BMOQuotientSpec.classOf g ↔ ModConstants f g :=
  Quotient.eq

theorem ballMean_eq_average (f : Point d → 𝕜) (x : Point d) (r : ℝ) :
    ballMean f x r = ⨍ y in Metric.ball x r, f y :=
  (setAverage_eq volume f (Metric.ball x r)).symm

theorem ballMean_const (c : 𝕜) (x : Point d) {r : ℝ} (hr : 0 < r) :
    ballMean (fun _ : Point d => c) x r = c := by
  rw [ballMean_eq_average]
  exact setAverage_const (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne c

theorem ballMean_add_const {f : Point d → 𝕜} (hf : LocallyIntegrable f volume)
    (c : 𝕜) (x : Point d) {r : ℝ} (hr : 0 < r) :
    ballMean (fun y => f y + c) x r = ballMean f x r + c := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  rw [ballMean_eq_average, setAverage_fun_add
    (integrableOn_ball_of_locallyIntegrable hf x r) (integrable_const c),
    ← ballMean_eq_average, ← ballMean_eq_average, ballMean_const c x hr]

theorem meanOscillation_add_const {f : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (c : 𝕜) (x : Point d) {r : ℝ} (hr : 0 < r) :
    meanOscillation (fun y => f y + c) x r = meanOscillation f x r := by
  change (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ‖f y + c - ballMean (fun y => f y + c) x r‖ₑ) = _
  rw [ballMean_add_const hf c x hr]
  simp only [add_sub_add_right_eq_sub]
  rfl

theorem bmoENorm_add_const : BMOQuotientSpec.ConstantInvariance := by
  intro d 𝕜 _ f hf c
  unfold BMOQuotientSpec.BMOENormValue
  congr 1
  funext x
  congr 1
  funext r
  congr 1
  funext hr
  exact meanOscillation_add_const hf c x hr

@[simp] theorem bmoENorm_const (c : 𝕜) : bmoENorm (fun _ : Point d => c) = 0 := by
  change (⨆ x, ⨆ r : ℝ, ⨆ (_ : 0 < r), meanOscillation (fun _ => c) x r) = 0
  apply le_antisymm _ zero_le
  refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
  change (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ‖c - ballMean (fun _ : Point d => c) x r‖ₑ) ≤ 0
  simp [ballMean_const c x hr]

/-- Finite-ball oscillation agrees with the ordinary normalized Bochner integral. -/
theorem meanOscillation_formula : BMOQuotientSpec.OscillationFormula := by
  intro d 𝕜 _ f hf x r _hr
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  have hi : Integrable (fun y => ‖f y - ballMean f x r‖)
      (volume.restrict (Metric.ball x r)) :=
    ((integrableOn_ball_of_locallyIntegrable hf x r).sub (integrable_const _)).norm
  change (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ‖f y - ballMean f x r‖ₑ) = _
  simp_rw [← ofReal_norm]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => norm_nonneg _)]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (measureReal_nonneg : 0 ≤ volume.real (Metric.ball x r)))]
  congr 1
  rw [Measure.real, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal]
  exact (ENNReal.inv_ne_top.mpr (Metric.measure_ball_pos volume x _hr).ne')

/-- An a.e. bounded measurable function is locally integrable, including at
points where the chosen representative is changed on a null set. -/
theorem locallyIntegrable_of_ae_bound {f : Point d → 𝕜}
    (hf : AEStronglyMeasurable f volume) (C : ℝ)
    (hC : ∀ᵐ y ∂volume, ‖f y‖ ≤ C) : LocallyIntegrable f volume := by
  apply locallyIntegrable_iff.mpr
  intro k hk
  exact IntegrableOn.of_bound hk.measure_lt_top hf.restrict C (ae_restrict_of_ae hC)

theorem norm_ballMean_le_of_ae_bound {f : Point d → 𝕜} {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖f y‖ ≤ C) (x : Point d) {r : ℝ} (hr : 0 < r) :
    ‖ballMean f x r‖ ≤ C := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  have hμ : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  change ‖(volume.real (Metric.ball x r))⁻¹ • ∫ y in Metric.ball x r, f y‖ ≤ C
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hμ.le)]
  calc
    _ ≤ (volume.real (Metric.ball x r))⁻¹ *
        (C * volume.real (Metric.ball x r)) := by
      gcongr
      simpa only [Measure.restrict_apply_univ, Measure.real] using
        norm_integral_le_of_norm_le_const (ae_restrict_of_ae hC)
    _ = C := by field_simp

/-- The elementary bound is uniform in the centre and radius. -/
theorem bmoENorm_le_of_ae_bound {f : Point d → 𝕜}
    (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖f y‖ ≤ C) : bmoENorm f ≤ ENNReal.ofReal (2 * C) := by
  have hfLoc := locallyIntegrable_of_ae_bound hf C hC
  refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
  rw [meanOscillation_formula f hfLoc x r hr]
  apply ENNReal.ofReal_le_ofReal
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  have hμ : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hosc : ∀ᵐ y ∂volume.restrict (Metric.ball x r),
      ‖f y - ballMean f x r‖ ≤ 2 * C := by
    filter_upwards [ae_restrict_of_ae hC] with y hy
    calc
      _ ≤ ‖f y‖ + ‖ballMean f x r‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add hy (norm_ballMean_le_of_ae_bound hC x hr)
      _ = 2 * C := (two_mul C).symm
  calc
    _ ≤ (volume.real (Metric.ball x r))⁻¹ *
        ∫ _y in Metric.ball x r, (2 * C) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hμ.le)
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (integrable_const (2 * C)) hosc
    _ = 2 * C := by
      rw [integral_const]
      simp only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul]
      dsimp [Measure.real] at hμ
      field_simp [hμ.ne']

theorem bounded_inclusion : BMOQuotientSpec.BoundedInclusion := by
  intro d 𝕜 _ f hf
  have hC := ae_le_lpNorm_exponent_top hf
  refine ⟨locallyIntegrable_of_ae_bound hf.aestronglyMeasurable _ hC, ?_⟩
  calc
    _ ≤ ENNReal.ofReal (2 * lpNorm f ∞ volume) :=
      bmoENorm_le_of_ae_bound hf.aestronglyMeasurable hC
    _ = 2 * eLpNorm f ∞ volume := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_lpNorm hf]
      norm_num

theorem meanOscillation_le_bmoENorm (f : Point d → 𝕜) (x : Point d)
    {r : ℝ} (hr : 0 < r) : meanOscillation f x r ≤ bmoENorm f :=
  le_iSup_of_le x (le_iSup_of_le r (le_iSup_of_le hr le_rfl))

/-- Zero oscillation forces equality with the ball mean almost everywhere on
that ball; measurability follows from local integrability. -/
theorem ae_eq_ballMean_of_bmoENorm_zero {f : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (hzero : bmoENorm f = 0)
    (x : Point d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂volume, y ∈ Metric.ball x r → f y = ballMean f x r := by
  have hosc : meanOscillation f x r = 0 :=
    le_antisymm (hzero ▸ meanOscillation_le_bmoENorm f x hr) zero_le
  have hi : (∫⁻ y in Metric.ball x r, ‖f y - ballMean f x r‖ₑ) = 0 := by
    exact (mul_eq_zero.mp hosc).resolve_left
      (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
  have hm : AEMeasurable (fun y => ‖f y - ballMean f x r‖ₑ)
      (volume.restrict (Metric.ball x r)) :=
    (hf.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const).enorm
  have hz := (setLIntegral_eq_zero_iff' measurableSet_ball hm).mp hi
  filter_upwards [hz] with y hy hmem
  exact sub_eq_zero.mp (enorm_eq_zero.mp (hy hmem))

/-- The means on a countable exhaustion of balls agree on a common positive
measure ball, so the zero-seminorm condition gives a single global constant. -/
theorem bmoENorm_eq_zero_iff : BMOQuotientSpec.Definiteness := by
  intro d 𝕜 _ f hf
  constructor
  · intro hzero
    let c := ballMean f (0 : Point d) 1
    have hz1 := ae_eq_ballMean_of_bmoENorm_zero hf hzero (0 : Point d) zero_lt_one
    have hz (n : ℕ) : ∀ᵐ y ∂volume,
        y ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) → f y = c := by
      have hr : 0 < (n : ℝ) + 1 := by positivity
      have hzn := ae_eq_ballMean_of_bmoENorm_zero hf hzero (0 : Point d) hr
      have heq : ballMean f (0 : Point d) ((n : ℝ) + 1) = c := by
        obtain ⟨y, hy, hy1, hyn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
          (Metric.measure_ball_pos volume (0 : Point d) zero_lt_one).ne' (ae_restrict_of_ae (hz1.and hzn))
        have hsub : Metric.ball (0 : Point d) 1 ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
          Metric.ball_subset_ball (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
        exact (hyn (hsub hy)).symm.trans (hy1 hy)
      filter_upwards [hzn] with y hy hmem
      exact (hy hmem).trans heq
    refine ⟨c, ?_⟩
    filter_upwards [ae_all_iff.mpr hz] with y hy
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    apply hy n
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  · rintro ⟨c, hc⟩
    exact (bmoENorm_congr_ae f (fun _ => c) hc).trans (bmoENorm_const c)

/-- The singularity of `log ‖x‖` is locally integrable even in dimension one.
Near zero it is dominated by `2 * ‖x‖ ^ (-1/2)`; elsewhere it is continuous. -/
theorem log_norm_locallyIntegrable_real (hd : 0 < d) :
    LocallyIntegrable (fun x : Point d => Real.log ‖x‖) volume := by
  have hm : AEStronglyMeasurable (fun x : Point d => Real.log ‖x‖) volume :=
    (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  have hdim : 1 ≤ Module.finrank ℝ (Point d) := by
    simpa [Point, BMOQuotientSpec.Point] using (Nat.succ_le_iff.mpr hd)
  have hdecay : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Point d) 1),
      ‖Real.log ‖x‖‖ ≤ 2 * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
    apply ae_restrict_of_forall_mem measurableSet_ball
    intro x hx
    have hxnorm : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
    rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos (norm_nonneg x) hxnorm)]
    have hlog := Real.neg_rpow_div_le_log (norm_nonneg x) (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hint : IntegrableOn (fun x : Point d => Real.log ‖x‖) (Metric.ball 0 1) volume :=
    integrableOn_ball_of_norm_le_rpow hdim
      (lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 1) (by exact_mod_cast hdim)) hdecay hm
  have hcont : ContinuousOn (fun x : Point d => Real.log ‖x‖) ({0}ᶜ : Set (Point d)) := by
    intro x hx
    exact ((Real.continuousAt_log (norm_ne_zero_iff.mpr hx)).comp continuous_norm.continuousAt).continuousWithinAt
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨Metric.ball 0 1, Metric.ball_mem_nhds _ zero_lt_one, hint⟩
  · have hlocal := hcont.locallyIntegrableOn (μ := (volume : Measure (Point d)))
      (measurableSet_singleton (0 : Point d)).compl x hx
    rwa [nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds hx)] at hlocal

theorem log_norm_locallyIntegrable (hd : 0 < d) :
    LocallyIntegrable (fun x : Point d => (Real.log ‖x‖ : 𝕜)) volume := by
  intro x
  exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integrableAtFilter_comp
    (log_norm_locallyIntegrable_real hd x)

/-- Essential unboundedness, rather than just a large value on a null set. -/
theorem log_norm_not_memLp_top (hd : 0 < d) :
    ¬ MemLp (fun x : Point d => (Real.log ‖x‖ : 𝕜)) ∞ volume := by
  intro hf
  let C := lpNorm (fun x : Point d => (Real.log ‖x‖ : 𝕜)) ∞ volume
  let U : Set (Point d) := {y | Real.exp (C + 1) < ‖y‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hUne : U.Nonempty := by
    use PiLp.single 2 (⟨0, hd⟩ : Fin d) (Real.exp (C + 1) + 1)
    change Real.exp (C + 1) < ‖(PiLp.single 2 (⟨0, hd⟩ : Fin d) (Real.exp (C + 1) + 1) : Point d)‖
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  obtain ⟨y, hy, hbound⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_pos volume hUne).ne' (ae_restrict_of_ae (ae_le_lpNorm_exponent_top hf))
  have hlog : C + 1 < Real.log ‖y‖ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos (C + 1)) hy
  have hle : Real.log ‖y‖ ≤ C := by
    simp only [RCLike.norm_ofReal] at hbound
    exact (le_abs_self _).trans hbound
  linarith

/-- Comparing the mean with any constant loses at most a factor of two. -/
theorem meanOscillation_le_twice_integral {f : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (c : 𝕜) (x : Point d) {r : ℝ} (hr : 0 < r) :
    meanOscillation f x r ≤ ENNReal.ofReal
      (2 * ((volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - c‖)) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  have hμ : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hi := (integrableOn_ball_of_locallyIntegrable hf x r).sub (integrable_const c)
  change Integrable (fun y => f y - c) (volume.restrict (Metric.ball x r)) at hi
  have hmean : ballMean (fun y => f y - c) x r = ballMean f x r - c := by
    rw [ballMean_eq_average, setAverage_fun_sub
      (integrableOn_ball_of_locallyIntegrable hf x r) (integrable_const c),
      ← ballMean_eq_average, ← ballMean_eq_average, ballMean_const c x hr]
  have hnorm : ‖ballMean f x r - c‖ ≤
      (volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - c‖ := by
    rw [← hmean]
    change ‖(volume.real (Metric.ball x r))⁻¹ • ∫ y in Metric.ball x r, (f y - c)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hμ.le)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hμ.le)
  change BMOQuotientSpec.MeanOscillationValue f x r ≤ _
  rw [meanOscillation_formula f hf x r hr]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (volume.real (Metric.ball x r))⁻¹ *
        ∫ y in Metric.ball x r, (‖f y - c‖ + ‖ballMean f x r - c‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hμ.le)
      apply integral_mono ((integrableOn_ball_of_locallyIntegrable hf x r).sub
        (integrable_const _)).norm (hi.norm.add (integrable_const _))
      intro y
      change ‖f y - ballMean f x r‖ ≤ ‖f y - c‖ + ‖ballMean f x r - c‖
      simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f y - c) (ballMean f x r - c)
    _ = (volume.real (Metric.ball x r))⁻¹ * (∫ y in Metric.ball x r, ‖f y - c‖) +
        ‖ballMean f x r - c‖ := by
      rw [integral_add hi.norm (integrable_const _), integral_const]
      simp only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul]
      dsimp [Measure.real] at hμ
      field_simp
    _ ≤ 2 * ((volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - c‖) := by
      linarith

/-- Exact scaling of real ball volume, with no restriction on dimension. -/
theorem volume_real_ball (x : Point d) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ d * volume.real (Metric.ball (0 : Point d) 1) := by
  unfold Measure.real
  rw [Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  simp [Point, BMOQuotientSpec.Point]

/-- Dilation removes the logarithm's scale constant; the identity is a.e.,
since the total logarithm convention assigns a separate value at zero. -/
theorem integral_log_sub_log_scale (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball (0 : Point d) (r * 3), |Real.log ‖y‖ - Real.log r|) =
      r ^ d * ∫ y in Metric.ball (0 : Point d) 3, |Real.log ‖y‖| := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have heq : (∫ y in Metric.ball (0 : Point d) 3,
      |Real.log ‖r • y‖ - Real.log r|) =
      ∫ y in Metric.ball (0 : Point d) 3, |Real.log ‖y‖| := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Point d))] with y hy
    rw [norm_smul, Real.norm_of_nonneg hr.le,
      Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hy)]
    simp
  have hscale := Measure.setIntegral_comp_smul_of_pos volume
    (fun y : Point d => |Real.log ‖y‖ - Real.log r|) (Metric.ball (0 : Point d) 3) hr
  rw [heq, _root_.smul_ball hr.ne', smul_zero, Real.norm_of_nonneg hr.le] at hscale
  have hdim : Module.finrank ℝ (Point d) = d := by simp [Point, BMOQuotientSpec.Point]
  rw [hdim, smul_eq_mul] at hscale
  rw [hscale]
  field_simp

/-- Away from the origin, no derivative estimate is needed: the norm ratio
lies between one half and three halves, so its logarithm has absolute value ≤ 1. -/
theorem abs_log_norm_sub_le {x y : Point d} {r : ℝ}
    (hr : 0 < r) (hfar : 2 * r ≤ ‖x‖) (hy : y ∈ Metric.ball x r) :
    |Real.log ‖y‖ - Real.log ‖x‖| ≤ 1 := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hdist : ‖y - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hdiff := abs_norm_sub_norm_le y x
  have hlo : ‖x‖ / 2 ≤ ‖y‖ := by
    have := neg_abs_le (‖y‖ - ‖x‖)
    linarith
  have hhi : ‖y‖ ≤ 3 / 2 * ‖x‖ := by
    have := le_abs_self (‖y‖ - ‖x‖)
    linarith
  have hypos : 0 < ‖y‖ := by linarith
  rw [← Real.log_div (ne_of_gt hypos) hxpos.ne']
  apply abs_le.mpr
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hypos hxpos)
    have hinv : (‖y‖ / ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_div, div_le_iff₀ hypos]
      linarith
    linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
    have hdiv : ‖y‖ / ‖x‖ ≤ 3 / 2 := (div_le_iff₀ hxpos).mpr hhi
    linarith

/-- The logarithm has finite BMO seminorm in every positive dimension. -/
theorem log_norm_bmoENorm_lt_top_real (hd : 0 < d) :
    bmoENorm (fun y : Point d => Real.log ‖y‖) < ∞ := by
  let f : Point d → ℝ := fun y => Real.log ‖y‖
  have hf : LocallyIntegrable f volume := log_norm_locallyIntegrable_real hd
  let C : ℝ := (volume.real (Metric.ball (0 : Point d) 1))⁻¹ *
    ∫ y in Metric.ball (0 : Point d) 3, |Real.log ‖y‖|
  apply lt_of_le_of_lt (b := ENNReal.ofReal (max 2 (2 * C))) _ ENNReal.ofReal_lt_top
  refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  have hμ : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  by_cases hfar : 2 * r ≤ ‖x‖
  · apply (meanOscillation_le_twice_integral hf (Real.log ‖x‖) x hr).trans
    apply ENNReal.ofReal_le_ofReal
    have hbound : (volume.real (Metric.ball x r))⁻¹ *
        ∫ y in Metric.ball x r, ‖f y - Real.log ‖x‖‖ ≤ 1 := by
      calc
        _ ≤ (volume.real (Metric.ball x r))⁻¹ * ∫ _y in Metric.ball x r, (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hμ.le)
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const 1)
          apply ae_restrict_of_forall_mem measurableSet_ball
          intro y hy
          exact abs_log_norm_sub_le hr hfar hy
        _ = 1 := by
          rw [integral_const]
          simp only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul, mul_one]
          exact inv_mul_cancel₀ hμ.ne'
    exact (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)).trans
      (by simpa using le_max_left (2 : ℝ) (2 * C))
  · apply (meanOscillation_le_twice_integral hf (Real.log r) x hr).trans
    apply ENNReal.ofReal_le_ofReal
    have hsub : Metric.ball x r ⊆ Metric.ball (0 : Point d) (r * 3) := by
      intro y hy
      rw [mem_ball_zero_iff]
      have hy' : ‖y - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have hn := norm_add_le (y - x) x
      rw [sub_add_cancel] at hn
      push_neg at hfar
      linarith
    haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point d) (r * 3))) :=
      ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d)))
        (x := (0 : Point d)) (r := r * 3))⟩
    have hi : IntegrableOn (fun y : Point d => |Real.log ‖y‖ - Real.log r|)
        (Metric.ball 0 (r * 3)) volume := by
      change Integrable (fun y : Point d => |Real.log ‖y‖ - Real.log r|)
        (volume.restrict (Metric.ball (0 : Point d) (r * 3)))
      exact ((integrableOn_ball_of_locallyIntegrable hf 0 (r * 3)).sub
        (integrable_const (Real.log r))).norm
    have hbound : (volume.real (Metric.ball x r))⁻¹ *
        ∫ y in Metric.ball x r, ‖f y - Real.log r‖ ≤ C := by
      calc
        _ ≤ (volume.real (Metric.ball x r))⁻¹ *
            ∫ y in Metric.ball (0 : Point d) (r * 3), |Real.log ‖y‖ - Real.log r| := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hμ.le)
          exact setIntegral_mono_set hi (Eventually.of_forall fun _ => abs_nonneg _)
            (Eventually.of_forall fun _ hy => hsub hy)
        _ = C := by
          rw [integral_log_sub_log_scale hd hr, volume_real_ball x hr]
          dsimp [C]
          field_simp
    exact (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)).trans (le_max_right _ _)

theorem ballMean_ofReal (f : Point d → ℝ) (x : Point d) (r : ℝ) :
    ballMean (fun y => (f y : 𝕜)) x r = ((ballMean (𝕜 := ℝ) f x r : ℝ) : 𝕜) := by
  change (volume.real (Metric.ball x r))⁻¹ • (∫ y in Metric.ball x r, (f y : 𝕜)) =
    (((volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, f y : ℝ) : 𝕜)
  rw [integral_ofReal, RCLike.ofReal_mul]
  simp [RCLike.real_smul_eq_coe_mul]

theorem bmoENorm_ofReal (f : Point d → ℝ) :
    bmoENorm (fun y => (f y : 𝕜)) = bmoENorm f := by
  change (⨆ x, ⨆ r : ℝ, ⨆ (_ : 0 < r), meanOscillation (fun y => (f y : 𝕜)) x r) =
    ⨆ x, ⨆ r : ℝ, ⨆ (_ : 0 < r), meanOscillation f x r
  congr 1
  funext x
  congr 1
  funext r
  congr 1
  funext _hr
  change (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ‖(f y : 𝕜) - ballMean (fun y => (f y : 𝕜)) x r‖ₑ) = _
  rw [ballMean_ofReal]
  change _ = (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ‖f y - ballMean f x r‖ₑ)
  simp only [← RCLike.ofReal_sub, ← ofReal_norm, RCLike.norm_ofReal, Real.norm_eq_abs]

/-- The source's complete unbounded BMO example, for real and complex scalars. -/
theorem log_norm_bmo : BMOQuotientSpec.LogExample := by
  intro d hd 𝕜 _
  refine ⟨log_norm_locallyIntegrable hd, ?_, log_norm_not_memLp_top hd⟩
  change bmoENorm (fun y : Point d => (Real.log ‖y‖ : 𝕜)) < ∞
  rw [bmoENorm_ofReal]
  exact log_norm_bmoENorm_lt_top_real hd

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

theorem ballMean_add {f g : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (x : Point d) (r : ℝ) :
    ballMean (f + g) x r = ballMean f x r + ballMean g x r := by
  unfold ballMean BMOQuotientSpec.MeanValue
  simp only [Pi.add_apply]
  rw [integral_add (integrableOn_ball_of_locallyIntegrable hf x r)
    (integrableOn_ball_of_locallyIntegrable hg x r), smul_add]

theorem ballMean_smul (c : 𝕜) (f : Point d → 𝕜) (x : Point d) (r : ℝ) :
    ballMean (c • f) x r = c • ballMean f x r := by
  unfold ballMean BMOQuotientSpec.MeanValue
  simp only [Pi.smul_apply]
  rw [integral_smul]
  exact smul_comm _ _ _

theorem meanOscillation_add_le {f g : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (x : Point d) {r : ℝ} (hr : 0 < r) :
    meanOscillation (f + g) x r ≤ meanOscillation f x r + meanOscillation g x r := by
  change BMOQuotientSpec.MeanOscillationValue (f + g) x r ≤
    BMOQuotientSpec.MeanOscillationValue f x r + BMOQuotientSpec.MeanOscillationValue g x r
  rw [meanOscillation_formula _ (hf.add hg) x r hr,
    meanOscillation_formula _ hf x r hr, meanOscillation_formula _ hg x r hr,
    ← ENNReal.ofReal_add (mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun _ => norm_nonneg _))
      (mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun _ => norm_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  change (volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r,
      ‖(f + g) y - ballMean (f + g) x r‖ ≤
    (volume.real (Metric.ball x r))⁻¹ * (∫ y in Metric.ball x r, ‖f y - ballMean f x r‖) +
    (volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖g y - ballMean g x r‖
  rw [← mul_add, ← integral_add (f := fun y => ‖f y - ballMean f x r‖)
    (g := fun y => ‖g y - ballMean g x r‖)
    ((integrableOn_ball_of_locallyIntegrable hf x r).sub (integrable_const _)).norm
    ((integrableOn_ball_of_locallyIntegrable hg x r).sub (integrable_const _)).norm]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr measureReal_nonneg)
  apply integral_mono
    (((integrableOn_ball_of_locallyIntegrable (hf.add hg) x r).sub (integrable_const _)).norm)
    ((((integrableOn_ball_of_locallyIntegrable hf x r).sub (integrable_const _)).norm).add
      (((integrableOn_ball_of_locallyIntegrable hg x r).sub (integrable_const _)).norm))
  intro y
  change ‖f y + g y - ballMean (f + g) x r‖ ≤ _
  rw [ballMean_add hf hg]
  convert norm_add_le (f y - ballMean f x r) (g y - ballMean g x r) using 1 <;> abel

theorem bmoENorm_add_le {f g : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    bmoENorm (f + g) ≤ bmoENorm f + bmoENorm g := by
  refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
  exact (meanOscillation_add_le hf hg x hr).trans
    (add_le_add (meanOscillation_le_bmoENorm f x hr) (meanOscillation_le_bmoENorm g x hr))

theorem meanOscillation_smul (c : 𝕜) (f : Point d → 𝕜) (x : Point d) (r : ℝ) :
    meanOscillation (c • f) x r = ‖c‖ₑ * meanOscillation f x r := by
  change (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ‖c • f y - ballMean (c • f) x r‖ₑ) = _
  rw [ballMean_smul]
  simp_rw [← smul_sub, enorm_smul]
  rw [lintegral_const_mul' _ _ (by simp : ‖c‖ₑ ≠ ∞)]
  change _ = ‖c‖ₑ * ((volume (Metric.ball x r))⁻¹ * _)
  exact mul_left_comm _ _ _

theorem bmoENorm_smul (c : 𝕜) (f : Point d → 𝕜) :
    bmoENorm (c • f) = ‖c‖ₑ * bmoENorm f := by
  change (⨆ x, ⨆ r : ℝ, ⨆ (_ : 0 < r), meanOscillation (c • f) x r) =
    ‖c‖ₑ * (⨆ x, ⨆ r : ℝ, ⨆ (_ : 0 < r), meanOscillation f x r)
  simp_rw [meanOscillation_smul, ENNReal.mul_iSup]

/-- Locally integrable functions with finite BMO seminorm form a vector space. -/
def bmoFunctionSubmodule (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    Submodule 𝕜 (Point d → 𝕜) where
  carrier := {f | LocallyIntegrable f volume ∧ bmoENorm f < ∞}
  zero_mem' := ⟨locallyIntegrable_const _, by
    change bmoENorm (fun _ : Point d => (0 : 𝕜)) < ∞
    rw [bmoENorm_const]
    exact ENNReal.zero_lt_top⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, (bmoENorm_add_le hf.1 hg.1).trans_lt (ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩)⟩
  smul_mem' := by
    intro c f hf
    exact ⟨hf.1.smul c, by rw [bmoENorm_smul]; exact ENNReal.mul_lt_top (by simp) hf.2⟩

instance bmoFunctionAddCommGroup : AddCommGroup (BMOFunction d 𝕜) :=
  inferInstanceAs (AddCommGroup (bmoFunctionSubmodule d 𝕜))

instance bmoFunctionModule : Module 𝕜 (BMOFunction d 𝕜) :=
  inferInstanceAs (Module 𝕜 (bmoFunctionSubmodule d 𝕜))

/-- Additive congruence of equality almost everywhere up to constants. -/
def bmoAddCon (d : ℕ) (𝕜 : Type) [RCLike 𝕜] : AddCon (BMOFunction d 𝕜) where
  toSetoid := BMOQuotientSpec.modConstantsSetoid d 𝕜
  add' := by
    rintro f g u v ⟨c, hc⟩ ⟨e, he⟩
    refine ⟨c + e, ?_⟩
    filter_upwards [hc, he] with x hx hxx
    change f.val x + u.val x = g.val x + v.val x + (c + e)
    rw [hx, hxx]
    abel

instance bmoAddCommGroup : AddCommGroup (BMO d 𝕜) :=
  inferInstanceAs (AddCommGroup (bmoAddCon d 𝕜).Quotient)

instance bmoSMul : SMul 𝕜 (BMO d 𝕜) where
  smul c q := Quotient.liftOn q (fun f => BMOQuotientSpec.classOf (c • f)) (by
    rintro f g ⟨e, he⟩
    apply Quotient.sound
    refine ⟨c * e, ?_⟩
    filter_upwards [he] with x hx
    change c • f.val x = c • g.val x + c * e
    rw [hx, smul_add]
    rfl)

@[simp] theorem bmo_class_add (f g : BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf (f + g) = BMOQuotientSpec.classOf f + BMOQuotientSpec.classOf g := rfl

@[simp] theorem bmo_class_smul (c : 𝕜) (f : BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf (c • f) = c • BMOQuotientSpec.classOf f := rfl

instance bmoModule : Module 𝕜 (BMO d 𝕜) :=
  Function.Surjective.module 𝕜 {toFun := BMOQuotientSpec.classOf, map_zero' := rfl, map_add' := bmo_class_add}
    Quotient.mk_surjective bmo_class_smul

/-- The seminorm is constant on each prescribed equivalence class. -/
theorem bmoENorm_eq_of_modConstants {f g : BMOFunction d 𝕜} (h : ModConstants f g) :
    bmoENorm f.val = bmoENorm g.val := by
  rcases h with ⟨c, hc⟩
  exact (bmoENorm_congr_ae f.val (fun x => g.val x + c) hc).trans
    (bmoENorm_add_const g.val g.property.1 c)

instance bmoNorm : Norm (BMO d 𝕜) where
  norm q := Quotient.liftOn q (fun f => (bmoENorm f.val).toReal) (by
    intro f g h
    exact congrArg ENNReal.toReal (bmoENorm_eq_of_modConstants h))

@[simp] theorem norm_bmo_class (f : BMOFunction d 𝕜) :
    ‖BMOQuotientSpec.classOf f‖ = (bmoENorm f.val).toReal := rfl

theorem bmoNormedSpaceCore : NormedSpace.Core 𝕜 (BMO d 𝕜) where
  norm_nonneg q := Quotient.inductionOn q fun f => ENNReal.toReal_nonneg
  norm_smul c q := by
    induction q using Quotient.inductionOn with | _ f =>
    change (bmoENorm (c • f.val)).toReal = ‖c‖ * (bmoENorm f.val).toReal
    rw [bmoENorm_smul, ENNReal.toReal_mul, toReal_enorm]
  norm_triangle q u := by
    induction q using Quotient.inductionOn with | _ f =>
    induction u using Quotient.inductionOn with | _ g =>
    change (bmoENorm (f.val + g.val)).toReal ≤ (bmoENorm f.val).toReal + (bmoENorm g.val).toReal
    have hfn : bmoENorm f.val ≠ ∞ := f.property.2.ne
    have hgn : bmoENorm g.val ≠ ∞ := g.property.2.ne
    rw [← ENNReal.toReal_add hfn hgn]
    exact ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨f.property.2, g.property.2⟩).ne
      (bmoENorm_add_le f.property.1 g.property.1)
  norm_eq_zero_iff q := by
    induction q using Quotient.inductionOn with | _ f =>
    constructor
    · intro h
      have hz : bmoENorm f.val = 0 := (ENNReal.toReal_eq_zero_iff (bmoENorm f.val)).mp h |>.resolve_right f.property.2.ne
      rcases (bmoENorm_eq_zero_iff f.val f.property.1).mp hz with ⟨c, hc⟩
      apply Quotient.sound
      refine ⟨c, ?_⟩
      change ∀ᵐ x ∂volume, f.val x = (0 : 𝕜) + c
      filter_upwards [hc] with x hx
      simpa only [zero_add] using hx
    · intro h
      have hz : ‖(0 : BMO d 𝕜)‖ = 0 := by
        change (bmoENorm (fun _ : Point d => (0 : 𝕜))).toReal = 0
        rw [bmoENorm_const, ENNReal.toReal_zero]
      exact h ▸ hz

instance bmoNormedAddCommGroup : NormedAddCommGroup (BMO d 𝕜) :=
  NormedAddCommGroup.ofCore bmoNormedSpaceCore

instance bmoNormedSpace : NormedSpace 𝕜 (BMO d 𝕜) :=
  NormedSpace.ofCore bmoNormedSpaceCore

/-- The canonical inclusion of an essentially bounded representative into BMO. -/
def boundedBMOFunction (f : Lp 𝕜 ∞ (volume : Measure (Point d))) : BMOFunction d 𝕜 :=
  ⟨f, (bounded_inclusion f (Lp.memLp f)).1,
    (bounded_inclusion f (Lp.memLp f)).2.trans_lt
      (ENNReal.mul_lt_top (by norm_num) (Lp.memLp f).eLpNorm_lt_top)⟩

/-- The natural linear map from L∞ to the quotient by constants. -/
def boundedToBMOLinear : Lp 𝕜 ∞ (volume : Measure (Point d)) →ₗ[𝕜] BMO d 𝕜 where
  toFun f := BMOQuotientSpec.classOf (boundedBMOFunction f)
  map_add' f g := by
    rw [← bmo_class_add]
    apply Quotient.sound
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_add f g] with x hx
    change (f + g) x = f x + g x + 0
    simpa only [Pi.add_apply, Pi.smul_apply, add_zero] using hx
  map_smul' c f := by
    rw [← bmo_class_smul]
    apply Quotient.sound
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_smul c f] with x hx
    change (c • f) x = c • f x + 0
    simpa only [Pi.add_apply, Pi.smul_apply, add_zero] using hx

theorem norm_boundedToBMOLinear_le (f : Lp 𝕜 ∞ (volume : Measure (Point d))) :
    ‖boundedToBMOLinear f‖ ≤ 2 * ‖f‖ := by
  change (bmoENorm (f : Point d → 𝕜)).toReal ≤ 2 * ‖f‖
  have hb : bmoENorm (f : Point d → 𝕜) ≤ 2 * eLpNorm f ∞ volume :=
    (bounded_inclusion f (Lp.memLp f)).2
  have ht : 2 * eLpNorm f ∞ volume ≠ ∞ :=
    (ENNReal.mul_lt_top (by norm_num) (Lp.memLp f).eLpNorm_lt_top).ne
  calc
    _ ≤ (2 * eLpNorm f ∞ volume).toReal := ENNReal.toReal_mono ht hb
    _ = 2 * ‖f‖ := by rw [ENNReal.toReal_mul, Lp.norm_def]; norm_num

/-- Bounded functions enter BMO continuously, with operator norm at most two. -/
def boundedToBMO : Lp 𝕜 ∞ (volume : Measure (Point d)) →L[𝕜] BMO d 𝕜 :=
  boundedToBMOLinear.mkContinuous 2 norm_boundedToBMOLinear_le

theorem norm_boundedToBMO_le : ‖(boundedToBMO :
    Lp 𝕜 ∞ (volume : Measure (Point d)) →L[𝕜] BMO d 𝕜)‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) norm_boundedToBMOLinear_le

theorem boundedToBMO_representative (f : Lp 𝕜 ∞ (volume : Measure (Point d))) :
    boundedToBMO f = BMOQuotientSpec.classOf (boundedBMOFunction f) := rfl

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy

/-- An absolutely summable series of L¹ functions has the ordinary pointwise
sum as an integrable representative, and its finite partial sums converge in L¹. -/
theorem integrable_tsum_of_summable_integral_norm
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [CompleteSpace E]
    {μ : Measure X} (f : ℕ → X → E) (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable fun n => ∫ x, ‖f n x‖ ∂μ) :
    Integrable (fun x => ∑' n, f n x) μ ∧
      Tendsto (fun N => ∫ x, ‖(∑ n ∈ Finset.range N, f n x) - ∑' n, f n x‖ ∂μ)
        atTop (𝓝 0) := by
  let F : ℕ → Lp E 1 μ := fun n => (hf n).toL1 (f n)
  have hnorm : ∀ n, ‖F n‖ = ∫ x, ‖f n x‖ ∂μ := fun n =>
    L1.norm_of_fun_eq_integral_norm (hf n)
  have hFs : Summable (fun n => ‖F n‖) := by simpa only [hnorm] using hs
  have hFe : ∑' n, ‖F n‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hFs
  have heq : (fun x => (∑' n, F n) x) =ᵐ[μ] fun x => ∑' n, f n x := by
    filter_upwards [Lp.coeFn_tsum hFe, ae_all_iff.mpr (fun n => (hf n).coeFn_toL1)]
      with x hx hxx
    exact hx.trans (tsum_congr fun n => hxx n)
  refine ⟨(L1.integrable_coeFn (∑' n, F n)).congr heq, ?_⟩
  have ht : Tendsto (fun N => ‖(∑ n ∈ Finset.range N, F n) - ∑' n, F n‖)
      atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hFs.of_norm.tendsto_sum_tsum_nat)
  convert ht using 1
  funext N
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.range N, F n) (∑' n, F n),
    Lp.coeFn_fun_finsetSum (Finset.range N) F, heq,
    ae_all_iff.mpr (fun n => (hf n).coeFn_toL1)] with x hx hsum hlim hxx
  dsimp only [Pi.sub_apply] at hx
  rw [hx, hsum, hlim]
  congr 2
  exact Finset.sum_congr rfl fun n _ => (hxx n).symm

/-- Local absolute summability constructs a single global representative, so
there is no choice of incompatible local L¹ limits. -/
theorem locallyIntegrable_tsum_of_summable_ball_integrals
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : ℕ → Point d → 𝕜)
    (hf : ∀ n, LocallyIntegrable (f n) volume)
    (hs : ∀ x r, Summable fun n => ∫ y in Metric.ball x r, ‖f n y‖) :
    LocallyIntegrable (fun y => ∑' n, f n y) volume ∧
      ∀ x r, Tendsto
        (fun N => ∫ y in Metric.ball x r,
          ‖(∑ n ∈ Finset.range N, f n y) - ∑' n, f n y‖) atTop (𝓝 0) := by
  have hlocal x r := integrable_tsum_of_summable_integral_norm f
    (fun n => integrableOn_ball_of_locallyIntegrable (hf n) x r) (hs x r)
  refine ⟨?_, fun x r => (hlocal x r).2⟩
  intro x
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, (hlocal x 1).1⟩

/-- Summability on an exhaustion by concentric balls suffices for all balls. -/
theorem summable_ball_integrals_of_centered
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : ℕ → Point d → 𝕜)
    (hf : ∀ n, LocallyIntegrable (f n) volume)
    (hs : ∀ R : ℝ, 1 ≤ R → Summable fun n =>
      ∫ y in Metric.ball (0 : Point d) R, ‖f n y‖) :
    ∀ x r, Summable fun n => ∫ y in Metric.ball x r, ‖f n y‖ := by
  intro x r
  let R := ‖x‖ + |r| + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg x, abs_nonneg r]
  have hsub : Metric.ball x r ⊆ Metric.ball (0 : Point d) R := by
    intro y hy
    rw [mem_ball_zero_iff]
    have hy' : ‖y - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hnorm := norm_add_le (y - x) x
    rw [sub_add_cancel] at hnorm
    dsimp [R]
    linarith [le_abs_self r]
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) _ (hs R hR)
  intro n
  exact setIntegral_mono_set
    (integrableOn_ball_of_locallyIntegrable (hf n) 0 R).norm
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ hy => hsub hy)

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

theorem integral_norm_sub_ballMean_le {f : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (hfin : bmoENorm f < ∞)
    (x : Point d) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball x r, ‖f y - ballMean f x r‖) ≤
      volume.real (Metric.ball x r) * (bmoENorm f).toReal := by
  have hμ : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hi : 0 ≤ (volume.real (Metric.ball x r))⁻¹ *
      ∫ y in Metric.ball x r, ‖f y - ballMean f x r‖ :=
    mul_nonneg (inv_nonneg.mpr hμ.le) (integral_nonneg fun _ => norm_nonneg _)
  have h := ENNReal.toReal_mono hfin.ne (meanOscillation_le_bmoENorm f x hr)
  have heq : meanOscillation f x r = ENNReal.ofReal
      ((volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - ballMean f x r‖) :=
    meanOscillation_formula f hf x r hr
  rw [heq, ENNReal.toReal_ofReal hi] at h
  exact (inv_mul_le_iff₀ hμ).mp h

theorem integral_norm_le_of_ballMean_zero {f : Point d → 𝕜}
    (hf : LocallyIntegrable f volume) (hfin : bmoENorm f < ∞)
    (hzero : ballMean f (0 : Point d) 1 = 0) {r : ℝ} (hr : 1 ≤ r) :
    (∫ y in Metric.ball (0 : Point d) r, ‖f y‖) ≤
      (1 + volume.real (Metric.ball (0 : Point d) r) *
        (volume.real (Metric.ball (0 : Point d) 1))⁻¹) *
      volume.real (Metric.ball (0 : Point d) r) * (bmoENorm f).toReal := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let D := Metric.ball (0 : Point d) r
  let B := Metric.ball (0 : Point d) 1
  let m := ballMean f (0 : Point d) r
  have hμ : 0 < volume.real B :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Point d) zero_lt_one).ne'
      measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by simpa [D] using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := 0) (r := r))⟩
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by simpa [B] using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := 0) (r := 1))⟩
  have hiD : IntegrableOn f D volume := integrableOn_ball_of_locallyIntegrable hf _ _
  have hiB : IntegrableOn f B volume := integrableOn_ball_of_locallyIntegrable hf _ _
  have hmean : ballMean (fun y => f y - m) (0 : Point d) 1 = -m := by
    simpa [sub_eq_add_neg, hzero] using ballMean_add_const hf (-m) (0 : Point d) zero_lt_one
  have hm : ‖m‖ ≤ (volume.real B)⁻¹ * ∫ y in D, ‖f y - m‖ := by
    calc
      ‖m‖ = ‖ballMean (fun y => f y - m) (0 : Point d) 1‖ := by rw [hmean, norm_neg]
      _ ≤ (volume.real B)⁻¹ * ∫ y in B, ‖f y - m‖ := by
        change ‖(volume.real B)⁻¹ • ∫ y in B, f y - m‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hμ.le)]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (inv_nonneg.mpr hμ.le)
      _ ≤ (volume.real B)⁻¹ * ∫ y in D, ‖f y - m‖ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hμ.le)
        exact setIntegral_mono_set ((hiD.sub (integrable_const m)).norm)
          (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall (Metric.ball_subset_ball hr))
  have hcD : Integrable (fun y => ‖f y - m‖) (volume.restrict D) :=
    (hiD.sub (integrable_const m)).norm
  have hosc := integral_norm_sub_ballMean_le hf hfin (0 : Point d) hrpos
  change (∫ y in D, ‖f y - m‖) ≤ volume.real D * (bmoENorm f).toReal at hosc
  calc
    (∫ y in D, ‖f y‖) ≤ ∫ y in D, (‖f y - m‖ + ‖m‖) := by
      apply integral_mono hiD.norm (hcD.add (integrable_const ‖m‖))
      intro y
      change ‖f y‖ ≤ ‖f y - m‖ + ‖m‖
      simpa only [sub_add_cancel] using norm_add_le (f y - m) m
    _ = (∫ y in D, ‖f y - m‖) + volume.real D * ‖m‖ := by
      rw [integral_add hcD (integrable_const ‖m‖), integral_const]
      simp [Measure.real, smul_eq_mul]
    _ ≤ (∫ y in D, ‖f y - m‖) + volume.real D *
        ((volume.real B)⁻¹ * ∫ y in D, ‖f y - m‖) := by
      gcongr
    _ = (1 + volume.real D * (volume.real B)⁻¹) * ∫ y in D, ‖f y - m‖ := by ring
    _ ≤ (1 + volume.real D * (volume.real B)⁻¹) *
        (volume.real D * (bmoENorm f).toReal) := by
      apply mul_le_mul_of_nonneg_left hosc
      positivity
    _ = _ := by dsimp [D, B]; ring

theorem summable_integral_norm_ball_of_summable_bmo {u : ℕ → Point d → 𝕜}
    (hu : ∀ n, LocallyIntegrable (u n) volume) (hfin : ∀ n, bmoENorm (u n) < ∞)
    (hzero : ∀ n, ballMean (u n) (0 : Point d) 1 = 0)
    (hsum : Summable (fun n => (bmoENorm (u n)).toReal)) {r : ℝ} (hr : 1 ≤ r) :
    Summable (fun n => ∫ y in Metric.ball (0 : Point d) r, ‖u n y‖) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) _
    (hsum.mul_left ((1 + volume.real (Metric.ball (0 : Point d) r) *
        (volume.real (Metric.ball (0 : Point d) 1))⁻¹) *
      volume.real (Metric.ball (0 : Point d) r)))
  intro n
  exact integral_norm_le_of_ballMean_zero (hu n) (hfin n) (hzero n) hr

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy

/-- Local L1 convergence implies convergence of both the integrals and the
integrals of the norms. -/
theorem tendsto_integral_and_norm_of_L1
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {F : ℕ → X → E} {f : X → E}
    (hF : ∀ n, Integrable (F n) μ) (hf : Integrable f μ)
    (hL1 : Tendsto (fun n => ∫ y, ‖F n y - f y‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, F n y ∂μ) atTop (𝓝 (∫ y, f y ∂μ)) ∧
    Tendsto (fun n => ∫ y, ‖F n y‖ ∂μ) atTop (𝓝 (∫ y, ‖f y‖ ∂μ)) := by
  let U : ℕ → Lp E 1 μ := fun n => (hF n).toL1 (F n)
  let v : Lp E 1 μ := hf.toL1 f
  have hU (n : ℕ) : (U n : X → E) =ᵐ[μ] F n := (hF n).coeFn_toL1
  have hv : (v : X → E) =ᵐ[μ] f := hf.coeFn_toL1
  have hdist (n : ℕ) : ‖U n - v‖ = ∫ y, ‖F n y - f y‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U n) v, hU n, hv] with y hy hUy hvy
    simp only [Pi.sub_apply] at hy
    rw [hy, hUy, hvy]
  have ht : Tendsto U atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simpa only [hdist] using hL1)
  constructor
  · have h := continuous_integral.tendsto v |>.comp ht
    convert h using 1
    · ext n
      exact (integral_congr_ae (hU n)).symm
    · exact congrArg nhds (integral_congr_ae hv).symm
  · have h := ht.norm
    convert h using 1
    · ext n
      exact (L1.norm_of_fun_eq_integral_norm (hF n)).symm
    · exact congrArg nhds (L1.norm_of_fun_eq_integral_norm hf).symm

/-- Taking the mean and centering is continuous for local L1 convergence. -/
theorem tendsto_meanOscillation_of_L1
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {F : ℕ → Point d → 𝕜} {f : Point d → 𝕜}
    (hF : ∀ n, LocallyIntegrable (F n) volume) (hf : LocallyIntegrable f volume)
    (x : Point d) {r : ℝ} (hr : 0 < r)
    (hL1 : Tendsto (fun n => ∫ y in Metric.ball x r, ‖F n y - f y‖) atTop (𝓝 0)) :
    Tendsto (fun n => meanOscillation (F n) x r) atTop (𝓝 (meanOscillation f x r)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Point d))) (x := x) (r := r))⟩
  have hiF (n : ℕ) := integrableOn_ball_of_locallyIntegrable (hF n) x r
  have hif := integrableOn_ball_of_locallyIntegrable hf x r
  have hmean : Tendsto (fun n => ballMean (F n) x r) atTop (𝓝 (ballMean f x r)) := by
    have ht := (tendsto_integral_and_norm_of_L1 hiF hif hL1).1
    exact ht.const_smul _
  have hcenter (n : ℕ) : Integrable (fun y => F n y - ballMean (F n) x r)
      (volume.restrict (Metric.ball x r)) := (hiF n).sub (integrable_const _)
  have hcenterf : Integrable (fun y => f y - ballMean f x r)
      (volume.restrict (Metric.ball x r)) := hif.sub (integrable_const _)
  have hnormmean : Tendsto (fun n => ‖ballMean (F n) x r - ballMean f x r‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hmean
  have hcenterL1 : Tendsto (fun n => ∫ y in Metric.ball x r,
      ‖(F n y - ballMean (F n) x r) - (f y - ballMean f x r)‖) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => (∫ y in Metric.ball x r, ‖F n y - f y‖) +
        volume.real (Metric.ball x r) * ‖ballMean (F n) x r - ballMean f x r‖)
        atTop (𝓝 0) := by simpa only [mul_zero, add_zero] using hL1.add (hnormmean.const_mul _)
    apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) _ hupper
    intro n
    calc
      _ ≤ ∫ y in Metric.ball x r,
          (‖F n y - f y‖ + ‖ballMean (F n) x r - ballMean f x r‖) := by
        apply integral_mono ((hcenter n).sub hcenterf).norm
          (((hiF n).sub hif).norm.add (integrable_const _))
        intro y
        have heq : (F n y - ballMean (F n) x r) - (f y - ballMean f x r) =
            (F n y - f y) - (ballMean (F n) x r - ballMean f x r) := by abel
        change ‖(F n y - ballMean (F n) x r) - (f y - ballMean f x r)‖ ≤
          ‖F n y - f y‖ + ‖ballMean (F n) x r - ballMean f x r‖
        rw [heq]
        exact norm_sub_le _ _
      _ = _ := by
        have hin : Integrable (fun y => ‖F n y - f y‖)
            (volume.restrict (Metric.ball x r)) := ((hiF n).sub hif).norm
        rw [integral_add hin (integrable_const _), integral_const]
        simp only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul]
  have hosc := (tendsto_integral_and_norm_of_L1 hcenter hcenterf hcenterL1).2
  have ht := ENNReal.continuous_ofReal.tendsto
    ((volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, ‖f y - ballMean f x r‖)
    |>.comp (hosc.const_mul (volume.real (Metric.ball x r))⁻¹)
  convert ht using 1
  · ext n
    exact meanOscillation_formula (F n) (hF n) x r hr
  · exact congrArg nhds (meanOscillation_formula f hf x r hr)

/-- Uniform BMO bounds survive convergence on every ball in L1. -/
theorem bmoENorm_le_of_local_L1_limit
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {F : ℕ → Point d → 𝕜} {f : Point d → 𝕜}
    {C : ℝ≥0∞}
    (hF : ∀ n, LocallyIntegrable (F n) volume) (hf : LocallyIntegrable f volume)
    (hL1 : ∀ x r, Tendsto (fun n => ∫ y in Metric.ball x r, ‖F n y - f y‖) atTop (𝓝 0))
    (hbound : ∀ n, bmoENorm (F n) ≤ C) : bmoENorm f ≤ C := by
  refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
  exact le_of_tendsto (tendsto_meanOscillation_of_L1 hF hf x hr (hL1 x r))
    (Eventually.of_forall fun n => (meanOscillation_le_bmoENorm (F n) x hr).trans (hbound n))

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

theorem sum_range_add_sub_prefix {E : Type*} [AddCommGroup E]
    (u : ℕ → E) (n k : ℕ) :
    (∑ i ∈ Finset.range (n + k), u i) - (∑ i ∈ Finset.range k, u i) =
      ∑ i ∈ Finset.range n, u (k + i) := by
  rw [Nat.add_comm n k, Finset.sum_range_add]
  exact add_sub_cancel_left _ _

private theorem bmoENorm_sum_bound {ι : Type} (s : Finset ι) (u : ι → Point d → 𝕜)
    (hu : ∀ i, LocallyIntegrable (u i) volume) :
    bmoENorm (∑ i ∈ s, u i) ≤ ∑ i ∈ s, bmoENorm (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change bmoENorm (fun _ : Point d => (0 : 𝕜)) ≤ 0
    rw [bmoENorm_const]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (bmoENorm_add_le (hu i) (locallyIntegrable_finsetSum' s (fun n _ => hu n))).trans
      (add_le_add le_rfl ih)

theorem bmoENorm_range_shift_sub_le (u : ℕ → Point d → 𝕜)
    (hu : ∀ n, LocallyIntegrable (u n) volume)
    (hfin : ∀ n, bmoENorm (u n) < ∞)
    (hsum : Summable (fun n => (bmoENorm (u n)).toReal)) (n k : ℕ) :
    bmoENorm ((∑ i ∈ Finset.range (n + k), u i) - (∑ i ∈ Finset.range k, u i)) ≤
      ENNReal.ofReal (∑' i, (bmoENorm (u (k + i))).toReal) := by
  rw [sum_range_add_sub_prefix]
  apply le_trans (bmoENorm_sum_bound (Finset.range n) (fun i => u (k + i)) (fun i => hu _))
  have heq : (∑ i ∈ Finset.range n, bmoENorm (u (k + i))) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, (bmoENorm (u (k + i))).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hfin _).ne).symm
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  exact Summable.sum_le_tsum _ (fun _ _ => ENNReal.toReal_nonneg)
    (by simpa only [Nat.add_comm] using (summable_nat_add_iff k).mpr hsum)

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

theorem bmoENorm_finsetSum_le {ι : Type} (s : Finset ι) (u : ι → Point d → 𝕜)
    (hu : ∀ i, LocallyIntegrable (u i) volume) :
    bmoENorm (∑ i ∈ s, u i) ≤ ∑ i ∈ s, bmoENorm (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change bmoENorm (fun _ : Point d => (0 : 𝕜)) ≤ 0
    exact (bmoENorm_const 0).le
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (bmoENorm_add_le (hu i) (locallyIntegrable_finsetSum' s (fun n _ => hu n))).trans
      (add_le_add le_rfl ih)

theorem bmoENorm_finsetSum_le_ofReal {ι : Type} (s : Finset ι) (u : ι → Point d → 𝕜)
    (hu : ∀ i, LocallyIntegrable (u i) volume) (hfin : ∀ i, bmoENorm (u i) < ∞) :
    bmoENorm (∑ i ∈ s, u i) ≤ ENNReal.ofReal (∑ i ∈ s, (bmoENorm (u i)).toReal) := by
  convert bmoENorm_finsetSum_le s u hu using 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
  exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (hfin i).ne

theorem locallyIntegrable_tsum_of_summable_bmo (u : ℕ → Point d → 𝕜)
    (hu : ∀ n, LocallyIntegrable (u n) volume) (hfin : ∀ n, bmoENorm (u n) < ∞)
    (hzero : ∀ n, ballMean (u n) (0 : Point d) 1 = 0)
    (hsum : Summable (fun n => (bmoENorm (u n)).toReal)) :
    LocallyIntegrable (fun y => ∑' n, u n y) volume ∧
      ∀ x r, Tendsto
        (fun N => ∫ y in Metric.ball x r,
          ‖(∑ n ∈ Finset.range N, u n y) - ∑' n, u n y‖) atTop (𝓝 0) := by
  apply locallyIntegrable_tsum_of_summable_ball_integrals u hu
  apply summable_ball_integrals_of_centered u hu
  intro R hR
  exact summable_integral_norm_ball_of_summable_bmo hu hfin hzero hsum hR

theorem normalized_bmo_series_converges (u : ℕ → Point d → 𝕜)
    (hu : ∀ n, LocallyIntegrable (u n) volume) (hfin : ∀ n, bmoENorm (u n) < ∞)
    (hzero : ∀ n, ballMean (u n) (0 : Point d) 1 = 0)
    (hsum : Summable (fun n => (bmoENorm (u n)).toReal)) :
    LocallyIntegrable (fun y => ∑' n, u n y) volume ∧
      bmoENorm (fun y => ∑' n, u n y) < ∞ ∧
      Tendsto (fun N => (bmoENorm (fun y =>
        (∑ n ∈ Finset.range N, u n y) - ∑' n, u n y)).toReal) atTop (𝓝 0) := by
  let f : Point d → 𝕜 := fun y => ∑' n, u n y
  let P : ℕ → Point d → 𝕜 := fun N y => ∑ n ∈ Finset.range N, u n y
  have hPeq (N : ℕ) : P N = ∑ n ∈ Finset.range N, u n := by
    ext y
    simp [P]
  obtain ⟨hf, hL1⟩ := locallyIntegrable_tsum_of_summable_bmo u hu hfin hzero hsum
  have hP (N : ℕ) : LocallyIntegrable (P N) volume :=
    locallyIntegrable_finsetSum (Finset.range N) (fun n _ => hu n)
  have htotal : ∀ N, bmoENorm (P N) ≤ ENNReal.ofReal (∑' n, (bmoENorm (u n)).toReal) := by
    intro N
    calc
      _ ≤ ENNReal.ofReal (∑ n ∈ Finset.range N, (bmoENorm (u n)).toReal) := by
        rw [hPeq N]
        exact bmoENorm_finsetSum_le_ofReal (Finset.range N) u hu hfin
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hsum.sum_le_tsum (Finset.range N)
        (fun n _ => ENNReal.toReal_nonneg))
  have hffinite : bmoENorm f < ∞ :=
    lt_of_le_of_lt (bmoENorm_le_of_local_L1_limit hP hf hL1 htotal) ENNReal.ofReal_lt_top
  have htail (N : ℕ) : bmoENorm (P N - f) ≤
      ENNReal.ofReal (∑' i, (bmoENorm (u (i + N))).toReal) := by
    apply bmoENorm_le_of_local_L1_limit
      (F := fun M => P N - P (M + N))
      (fun M => (hP N).sub (hP (M + N))) ((hP N).sub hf)
    · intro x r
      have hnat : Tendsto (fun M : ℕ => M + N) atTop atTop := by
        apply tendsto_atTop.2
        intro b
        exact (eventually_ge_atTop b).mono fun M hM => hM.trans (Nat.le_add_right M N)
      have hh := (hL1 x r).comp hnat
      convert hh using 1
      funext M
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change ‖(P N y - P (M + N) y) - (P N y - f y)‖ = ‖P (M + N) y - f y‖
        rw [sub_sub_sub_cancel_left, norm_sub_rev]
    · intro M
      have hneg : bmoENorm (P N - P (M + N)) = bmoENorm (P (M + N) - P N) := by
        have heq : P N - P (M + N) = (-1 : 𝕜) • (P (M + N) - P N) := by
          ext y
          simp
        rw [heq, bmoENorm_smul]
        simp
      rw [hneg]
      rw [hPeq (M + N), hPeq N]
      simpa only [Nat.add_comm] using
        bmoENorm_range_shift_sub_le u hu hfin hsum M N
  refine ⟨hf, hffinite, ?_⟩
  have htail0 : Tendsto (fun N => ∑' i, (bmoENorm (u (i + N))).toReal) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun n => (bmoENorm (u n)).toReal)
  apply squeeze_zero (fun N => ENNReal.toReal_nonneg) _ htail0
  intro N
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail N)
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun i => ENNReal.toReal_nonneg)] at ht
  exact ht

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- The representative whose mean on the unit ball is zero. -/
def normalizeBMOFunction (f : BMOFunction d 𝕜) : BMOFunction d 𝕜 :=
  ⟨fun x => f.val x + -ballMean f.val (0 : Point d) 1,
    ⟨f.property.1.add (locallyIntegrable_const _), by
      change bmoENorm (fun x => f.val x + -ballMean f.val 0 1) < ∞
      exact lt_of_eq_of_lt (bmoENorm_add_const f.val f.property.1 _) f.property.2⟩⟩

theorem normalizeBMOFunction_mean (f : BMOFunction d 𝕜) :
    ballMean (normalizeBMOFunction f).val (0 : Point d) 1 = 0 := by
  change ballMean (fun x => f.val x + -ballMean f.val 0 1) 0 1 = 0
  rw [ballMean_add_const f.property.1 _ _ zero_lt_one, add_neg_cancel]

@[simp] theorem class_normalizeBMOFunction (f : BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf (normalizeBMOFunction f) = BMOQuotientSpec.classOf f := by
  apply Quotient.sound
  exact ⟨-ballMean f.val 0 1, Eventually.of_forall fun _ => rfl⟩

@[simp] theorem bmoENorm_normalizeBMOFunction (f : BMOFunction d 𝕜) :
    bmoENorm (normalizeBMOFunction f).val = bmoENorm f.val :=
  bmoENorm_add_const f.val f.property.1 _

theorem bmo_class_zero : BMOQuotientSpec.classOf (0 : BMOFunction d 𝕜) = 0 := rfl

theorem bmo_class_neg (f : BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf (-f) = -BMOQuotientSpec.classOf f := rfl

theorem bmo_class_sub (f g : BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf (f - g) = BMOQuotientSpec.classOf f - BMOQuotientSpec.classOf g := rfl

def bmoClassLinearMap : BMOFunction d 𝕜 →ₗ[𝕜] BMO d 𝕜 where
  toFun := BMOQuotientSpec.classOf
  map_add' := bmo_class_add
  map_smul' := bmo_class_smul

theorem bmo_class_sum {ι : Type} (s : Finset ι) (f : ι → BMOFunction d 𝕜) :
    BMOQuotientSpec.classOf (∑ n ∈ s, f n) = ∑ n ∈ s, BMOQuotientSpec.classOf (f n) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact bmo_class_zero
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, Finset.sum_insert hn, bmo_class_add, ih]

theorem bmoFunction_sum_apply {ι : Type} (s : Finset ι) (f : ι → BMOFunction d 𝕜)
    (x : Point d) : (∑ n ∈ s, f n).val x = ∑ n ∈ s, (f n).val x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, Finset.sum_insert hn]
    change (f n).val x + (∑ n ∈ s, f n).val x = _
    rw [ih]

/-- Choice of a representative, normalized by its actual unit-ball mean. -/
def normalizedBMORepresentative (q : BMO d 𝕜) : BMOFunction d 𝕜 :=
  normalizeBMOFunction (Quotient.out q)

@[simp] theorem class_normalizedBMORepresentative (q : BMO d 𝕜) :
    BMOQuotientSpec.classOf (normalizedBMORepresentative q) = q :=
  (class_normalizeBMOFunction (Quotient.out q)).trans (Quotient.out_eq q)

theorem summable_bmo_normalizedBMORepresentative (u : ℕ → BMO d 𝕜)
    (hu : Summable (fun n => ‖u n‖)) :
    Summable (fun n => (bmoENorm (normalizedBMORepresentative (u n)).val).toReal) := by
  have heq (n : ℕ) : (bmoENorm (normalizedBMORepresentative (u n)).val).toReal = ‖u n‖ := by
    rw [← norm_bmo_class, class_normalizedBMORepresentative]
  simpa only [heq] using hu

theorem bmo_complete_of_normalized_series
    (hseries : ∀ (v : ℕ → Point d → 𝕜),
      (∀ n, LocallyIntegrable (v n) volume) →
      (∀ n, bmoENorm (v n) < ∞) →
      (∀ n, ballMean (v n) (0 : Point d) 1 = 0) →
      Summable (fun n => (bmoENorm (v n)).toReal) →
      LocallyIntegrable (fun y => ∑' n, v n y) volume ∧
      bmoENorm (fun y => ∑' n, v n y) < ∞ ∧
      Tendsto (fun N => (bmoENorm (fun y =>
        (∑ n ∈ Finset.range N, v n y) - ∑' n, v n y)).toReal) atTop (𝓝 0)) :
    CompleteSpace (BMO d 𝕜) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro u hu
  let v : ℕ → BMOFunction d 𝕜 := fun n => normalizedBMORepresentative (u n)
  have hv (n : ℕ) : BMOQuotientSpec.classOf (v n) = u n :=
    class_normalizedBMORepresentative (u n)
  obtain ⟨hf, hfin, hconv⟩ := hseries (fun n => (v n).val)
    (fun n => (v n).property.1) (fun n => (v n).property.2)
    (fun n => normalizeBMOFunction_mean _) (summable_bmo_normalizedBMORepresentative u hu)
  let f : BMOFunction d 𝕜 := ⟨fun y => ∑' n, (v n).val y, hf, hfin⟩
  refine ⟨BMOQuotientSpec.classOf f, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hnorm (N : ℕ) : ‖(∑ n ∈ Finset.range N, u n) - BMOQuotientSpec.classOf f‖ =
      (bmoENorm (fun y => (∑ n ∈ Finset.range N, (v n).val y) - ∑' n, (v n).val y)).toReal := by
    have hsum : (∑ n ∈ Finset.range N, u n) =
        BMOQuotientSpec.classOf (∑ n ∈ Finset.range N, v n) := by
      rw [bmo_class_sum]
      exact Finset.sum_congr rfl fun n _ => (hv n).symm
    rw [hsum, ← bmo_class_sub, norm_bmo_class]
    congr 2
    funext y
    change (∑ n ∈ Finset.range N, v n).val y - f.val y = _
    rw [bmoFunction_sum_apply]
  simpa only [hnorm] using hconv

end ExpandedFA.Hardy

namespace ExpandedFA.Hardy

/-- Completeness for the prescribed norm and the prescribed quotient. -/
instance bmoCompleteSpace {d : ℕ} {𝕜 : Type} [RCLike 𝕜] : CompleteSpace (BMO d 𝕜) :=
  bmo_complete_of_normalized_series normalized_bmo_series_converges

/-- The full Banach quotient and continuous bounded-function inclusion. -/
theorem bmo_banach_quotient : BMOQuotientSpec.BanachQuotient := by
  intro d 𝕜 _
  refine ⟨bmoNormedAddCommGroup, bmoNormedSpace, inferInstance, ?_, ?_, ?_,
    boundedToBMO, norm_boundedToBMO_le, ?_⟩
  · intro f
    exact norm_bmo_class f
  · intro f g
    exact ⟨(f + g).property, rfl⟩
  · intro c f
    exact ⟨(c • f).property, rfl⟩
  · intro f
    exact ⟨(boundedBMOFunction f).property, rfl⟩

end ExpandedFA.Hardy
