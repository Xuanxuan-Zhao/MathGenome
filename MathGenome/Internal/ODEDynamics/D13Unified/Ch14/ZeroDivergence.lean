import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.ZeroDivergence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Annulus
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.OrbitalInstability

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace D13Unified.Ch14.ZeroDivergence
open Ch06.StateDerivative Ch11.Orbits Ch13.Annulus
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch14.OrbitalDefinitions
open Specs.D13Unified.Ch14.OrbitalInstability
open Specs.D13Unified.Ch14.Multipliers

private def domain : Set ℂ := {z | |‖z‖ - 1| < 1 / 2}

private lemma domain_open : IsOpen domain :=
  isOpen_lt (continuous_norm.sub continuous_const).abs continuous_const

private lemma domain_ne_zero {z : ℂ} (hz : z ∈ domain) : z ≠ 0 := by
  intro he
  subst z
  norm_num [domain] at hz

private def field (a : ℝ) (z : ℂ) : ℂ :=
  Complex.I * z + ((a * (‖z‖ - 1)^3 / ‖z‖ : ℝ) : ℂ) * z

private lemma field_smooth (a : ℝ) : ContDiffOn ℝ 1 (field a) domain := by
  have hn : ContDiffOn ℝ 1 (norm : ℂ → ℝ) domain :=
    fun z hz => (contDiffAt_norm ℝ (domain_ne_zero hz)).contDiffWithinAt
  have hc : ContDiffOn ℝ 1 (fun z : ℂ => a * (‖z‖ - 1)^3 / ‖z‖) domain :=
    (contDiffOn_const.mul ((hn.sub contDiffOn_const).pow 3)).div hn
    (fun z hz => norm_ne_zero_iff.mpr (domain_ne_zero hz))
  exact (contDiffOn_const.mul contDiffOn_id).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hc).mul contDiffOn_id)

private def oscillator (a : ℝ) : AutonomousODE ℂ where
  domain := domain
  isOpen_domain := domain_open
  field z := field a z
  continuous_field := (continuousOn_iff_continuous_domRestrict.mp (field_smooth a).continuousOn)

private lemma eval_eqOn (a : ℝ) : EqOn (autonomousEvalValue (oscillator a)) (field a) domain := by
  intro z hz
  simp [autonomousEvalValue, oscillator, hz]

private lemma oscillator_c1 (a : ℝ) : ContDiffOn ℝ 1 (oscillator a).eval (oscillator a).domain :=
  (field_smooth a).congr (eval_eqOn a)

private lemma one_mem : (1 : ℂ) ∈ domain := by norm_num [domain]

private def denominator (a s t : ℝ) : ℝ := 1 - 2 * a * s^2 * t

private def displacement (a s t : ℝ) : ℝ := s / Real.sqrt (denominator a s t)

private def timeInterval (a : ℝ) {z : ℂ} (hz : z ∈ domain) : OpenTimeInterval where
  carrier := {t | 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) t}
  nonempty := ⟨0, by
    change 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) 0
    rw [show denominator a (‖z‖ - 1) 0 = 1 by simp [denominator]]
    have hz' : |‖z‖ - 1| < 1 / 2 := hz
    have h := (sq_lt_sq).mpr (by simpa using hz' : |‖z‖ - 1| < |(1 / 2 : ℝ)|)
    nlinarith⟩
  isOpen := by
    apply isOpen_lt continuous_const
    unfold denominator
    fun_prop
  ordConnected := by
    constructor
    intro x hx y hy t ht
    change 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) x at hx
    change 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) y at hy
    change 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) t
    unfold denominator at *
    rcases le_total 0 (2 * a * (‖z‖ - 1)^2) with hc | hc
    · linarith [mul_le_mul_of_nonneg_left ht.2 hc]
    · linarith [mul_le_mul_of_nonpos_left ht.1 hc]

private lemma denominator_pos {a s t : ℝ} (h : 4 * s^2 < denominator a s t) :
    0 < denominator a s t := (by positivity : 0 ≤ 4 * s^2).trans_lt h

private lemma displacement_lt {a s t : ℝ} (h : 4 * s^2 < denominator a s t) :
    |displacement a s t| < 1 / 2 := by
  have hd := Real.sqrt_pos.mpr (denominator_pos h)
  have hsq := Real.sq_sqrt (denominator_pos h).le
  have hsq' : |s|^2 < (Real.sqrt (denominator a s t) / 2)^2 := by
    rw [sq_abs, div_pow, hsq]
    linarith
  rw [displacement, abs_div, abs_of_pos hd, div_lt_iff₀ hd]
  have hlt := (sq_lt_sq.mp hsq')
  simpa [abs_of_nonneg hd.le, mul_comm,
    div_eq_mul_inv] using hlt

private lemma displacement_deriv (a s t : ℝ) (hd : 0 < denominator a s t) :
    HasDerivAt (displacement a s) (a * (displacement a s t)^3) t := by
  have hden : HasDerivAt (denominator a s) (-(2*a*s^2)) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul (2 * a * s^2))
    change HasDerivAt (denominator a s) _ t at h
    simpa using h
  have hs := Real.sqrt_pos.mpr hd
  have h := (hasDerivAt_const t s).div (hden.sqrt hd.ne') hs.ne'
  convert h using 1
  · rfl
  · unfold displacement
    field_simp [hs.ne']
    ring

private def trajectory (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  polar (1 + displacement a (‖z‖ - 1) t) (t + z.arg)

private lemma trajectory_zero (a : ℝ) (z : ℂ) : trajectory a z 0 = z := by
  have hr : 1 + displacement a (‖z‖ - 1) 0 = ‖z‖ := by simp [displacement, denominator]
  rw [trajectory, hr, zero_add, polar, Complex.norm_mul_exp_arg_mul_I]

private lemma trajectory_radius {a : ℝ} {z : ℂ} {t : ℝ}
    (h : 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) t) :
    ‖trajectory a z t‖ = 1 + displacement a (‖z‖ - 1) t := by
  have hp := (abs_lt.mp (displacement_lt h)).1
  exact (polar_norm _ _).trans (abs_of_pos (by linarith))

private lemma trajectory_mem {a : ℝ} {z : ℂ} {t : ℝ}
    (h : 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) t) : trajectory a z t ∈ domain := by
  change |‖trajectory a z t‖ - 1| < 1 / 2
  rw [trajectory_radius h, add_sub_cancel_left]
  exact displacement_lt h

private lemma trajectory_deriv {a : ℝ} {z : ℂ} {t : ℝ}
    (h : 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) t) :
    HasDerivAt (trajectory a z) (field a (trajectory a z t)) t := by
  let s := displacement a (‖z‖ - 1) t
  have hr := (displacement_deriv a (‖z‖ - 1) t (denominator_pos h)).const_add 1
  have ht : HasDerivAt (fun u : ℝ => u + z.arg) 1 t := (hasDerivAt_id t).add_const z.arg
  have hrot := (Complex.hasDerivAt_exp (((t + z.arg : ℝ) : ℂ) * Complex.I)).comp t
    (ht.ofReal_comp.mul_const Complex.I)
  have hs : 0 < 1 + s := by
    dsimp [s]
    linarith [(abs_lt.mp (displacement_lt h)).1]
  have htraj := hr.ofReal_comp.mul hrot
  convert htraj using 1
  · rfl
  · unfold field
    rw [trajectory_radius h, add_sub_cancel_left]
    simp only [trajectory, polar, Function.comp_def, Complex.ofReal_one, one_mul]
    change Complex.I * ((↑(1 + s) : ℂ) * _) +
      ((a * s^3 / (1 + s) : ℝ) : ℂ) * (↑(1 + s) * _) = _
    push_cast
    field_simp [show (1 : ℂ) + (s : ℂ) ≠ 0 by exact_mod_cast hs.ne']
    ring

private lemma trajectory_solution (a : ℝ) {z : ℂ} (hz : z ∈ domain) :
    classicalIVPOnValue (oscillator a).toODE (timeInterval a hz) (trajectory a z) 0 z := by
  let J := timeInterval a hz
  have hd (t : ℝ) (ht : t ∈ J.carrier) := trajectory_deriv ht
  refine ⟨⟨?_, fun t ht => trajectory_mem ht, ?_⟩, ?_, trajectory_zero a z⟩
  · have hdiff : DifferentiableOn ℝ (trajectory a z) J.carrier :=
      fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    rw [show (1 : ℕ∞ω) = 0+1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen J.isOpen]
    refine ⟨hdiff, by simp, ?_⟩
    rw [contDiffOn_zero]
    have he : EqOn (deriv (trajectory a z)) (fun t => field a (trajectory a z t)) J.carrier :=
      fun t ht => (hd t ht).deriv
    exact ((field_smooth a).continuousOn.comp hdiff.continuousOn
      (fun t ht => trajectory_mem ht)).congr he
  · intro t ht
    have h := hd t ht
    rwa [← eval_eqOn a (trajectory_mem ht)] at h
  · change 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) 0
    have hz' : |‖z‖ - 1| < 1 / 2 := hz
    have h := (sq_lt_sq).mpr (by simpa using hz' : |‖z‖ - 1| < |(1 / 2 : ℝ)|)
    simp [denominator]
    nlinarith

private lemma canonical_trajectory (a : ℝ) {z : ℂ} (hz : z ∈ domain) :
    (timeInterval a hz).carrier ⊆ (flowInterval (oscillator a) z).carrier ∧
      EqOn (fun t => flow (oscillator a) t z) (trajectory a z) (timeInterval a hz).carrier := by
  have hc := ODE.canonical_solution (oscillator a).toODE
    ((oscillator a).locallyLipschitzInState_of_contDiffOn (oscillator_c1 a)) 0 z hz
  exact hc.2.2.2.2.2.1 _ _ (trajectory_solution a hz)

private lemma circle_flow (a t : ℝ) :
    t ∈ (flowInterval (oscillator a) (1 : ℂ)).carrier ∧
      flow (oscillator a) t 1 = circleCurve t := by
  have ht : t ∈ (timeInterval a one_mem).carrier := by
    change 4 * (‖(1 : ℂ)‖ - 1)^2 < denominator a (‖(1 : ℂ)‖ - 1) t
    simp [denominator]
  exact ⟨(canonical_trajectory a one_mem).1 ht, (canonical_trajectory a one_mem).2 ht |>.trans
    (by simp [trajectory, displacement, denominator, circleCurve])⟩

private lemma circle_orbit (a : ℝ) : orbit (oscillator a) (1 : ℂ) = unitCircle := by
  rw [← (periodic_circle : Specs.D13Unified.Ch13.Annulus.PeriodicCircle).2.2.1]
  ext z
  constructor
  · rintro ⟨t, _, rfl⟩
    exact ⟨t, (circle_flow a t).2.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, (circle_flow a t).1, (circle_flow a t).2⟩

private lemma circle_dist (z : ℂ) : Metric.infDist z unitCircle = |‖z‖ - 1| := by
  apply le_antisymm (distance_to_circle_le z)
  apply (Metric.le_infDist ⟨(1 : ℂ), by simp [unitCircle]⟩).mpr
  intro w hw
  have hw' : ‖w‖ = 1 := hw
  rw [← hw', dist_eq_norm]
  exact abs_norm_sub_norm_le z w

private lemma canonical_dist {a : ℝ} {z : ℂ} (hz : z ∈ domain) {t : ℝ}
    (ht : 4 * (‖z‖ - 1)^2 < denominator a (‖z‖ - 1) t) :
    Metric.infDist (flow (oscillator a) t z) unitCircle = |displacement a (‖z‖ - 1) t| := by
  have he : flow (oscillator a) t z = trajectory a z t := (canonical_trajectory a hz).2 ht
  rw [he, circle_dist, trajectory_radius ht, add_sub_cancel_left]

private lemma stable_trajectory {z : ℂ} (hz : z ∈ domain) {t : ℝ} (ht : 0 ≤ t) :
    4 * (‖z‖ - 1)^2 < denominator (-1) (‖z‖ - 1) t := by
  have hz' : |‖z‖ - 1| < 1 / 2 := hz
  have hs := sq_lt_sq.mpr (by simpa using hz' : |‖z‖ - 1| < |(1 / 2 : ℝ)|)
  have he := mul_nonneg (sq_nonneg (‖z‖ - 1)) ht
  unfold denominator
  nlinarith

private lemma attracting : orbitalAsymptoticallyStableValue (oscillator (-1)) unitCircle := by
  have complete {z : ℂ} (hz : z ∈ domain) : forwardCompleteValue (oscillator (-1)) z :=
    ⟨hz, fun _ ht => (canonical_trajectory (-1) hz).1 (stable_trajectory hz ht)⟩
  constructor
  · intro ε hε
    refine ⟨ε, hε, fun z hz hnear => ⟨complete hz, fun t ht => ?_⟩⟩
    rw [canonical_dist hz (stable_trajectory hz ht), displacement, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [circle_dist] at hnear
    have hD : 1 ≤ denominator (-1) (‖z‖ - 1) t := by
      unfold denominator
      nlinarith [mul_nonneg (sq_nonneg (‖z‖ - 1)) ht]
    exact (div_le_self (abs_nonneg _) (by simpa using Real.sqrt_le_sqrt hD)).trans_lt hnear
  · refine ⟨1 / 2, by norm_num, fun z hz _ => ⟨complete hz, ?_⟩⟩
    have hlimit : Tendsto (fun t : ℝ => |displacement (-1) (‖z‖ - 1) t|) atTop (𝓝 0) := by
      let s := ‖z‖ - 1
      change Tendsto (fun t : ℝ => |displacement (-1) s t|) atTop (𝓝 0)
      by_cases hs : s = 0
      · simp [hs, displacement]
      · have hden : Tendsto (denominator (-1) s) atTop atTop := by
          have hp : 0 < 2 * s^2 := by positivity
          have he : (fun t => 1 + (2*s^2)*t) = denominator (-1) s := by
            funext t
            unfold denominator
            ring
          rw [← he]
          exact tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop hp)
        have hdiv : Tendsto (displacement (-1) s) atTop (𝓝 0) :=
          (Real.tendsto_sqrt_atTop.comp hden).const_div_atTop s
        simpa using hdiv.abs
    apply hlimit.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (canonical_dist hz (stable_trajectory hz ht)).symm

private lemma repelling : distanceEscapeValue (oscillator 1) (1 : ℂ) := by
  refine ⟨1 / 4, by norm_num, fun δ hδ => ?_⟩
  let s := min (δ / 2) (1 / 8)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hsδ : s < δ := (min_le_left _ _).trans_lt (by linarith)
  have hss : s ≤ 1 / 8 := min_le_right _ _
  let z : ℂ := (1 + s : ℝ)
  have hzrad : ‖z‖ - 1 = s := by
    change ‖((1 + s : ℝ) : ℂ)‖ - 1 = s
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < 1 + s by linarith)]
    ring
  have hz : z ∈ domain := by
    change |‖z‖ - 1| < 1 / 2
    rw [hzrad, abs_of_pos hs]
    linarith
  let t := (1 - 16*s^2) / (2*s^2)
  have hsq := sq_pos_of_pos hs
  have ht : 0 < t := div_pos (by nlinarith) (by positivity)
  have hD : denominator 1 s t = 16*s^2 := by
    unfold t denominator
    field_simp
    ring
  have hdom : 4 * (‖z‖ - 1)^2 < denominator 1 (‖z‖ - 1) t := by
    rw [hzrad, hD]
    linarith
  refine ⟨z, hz, ?_, t, ht, ⟨hz, (canonical_trajectory 1 hz).1 hdom⟩, ?_⟩
  · rw [show z - 1 = (s : ℂ) by simp [z], Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact hsδ
  · rw [circle_orbit, canonical_dist hz hdom, hzrad, displacement, hD]
    rw [show 16*s^2 = (4*s)^2 by ring, Real.sqrt_sq (by positivity),
      abs_of_pos (div_pos hs (by positivity))]
    apply (le_div_iff₀ (by positivity : 0 < 4 * s)).mpr
    linarith

private lemma divergence_zero (a : ℝ) {z : ℂ} (hz : z ∈ unitCircle) :
    divergence (oscillator a) z = 0 := by
  have hr : ‖z‖ = 1 := hz
  have hz' : z ∈ domain := by simp [domain, hr]
  have hdiff : ContDiffAt ℝ 1 norm z := contDiffAt_norm ℝ (domain_ne_zero hz')
  have hd := (hdiff.differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasFDerivAt (fun w : ℂ => (‖w‖ - 1)^3) (0 : ℂ →L[ℝ] ℝ) z := by
    simpa [hr] using (hd.sub_const (1 : ℝ)).pow 3
  have hf : HasFDerivAt (fun w : ℂ => ((a*(‖w‖-1)^3/‖w‖ : ℝ) : ℂ)*w)
      (0 : ℂ →L[ℝ] ℂ) z := by
    have hn : DifferentiableAt ℝ (fun w : ℂ => a / ‖w‖) z := by
      simp only [div_eq_mul_inv]
      exact (hd.differentiableAt.inv (show ‖z‖ ≠ 0 by simp [hr])).const_mul a
    have hcoef : HasFDerivAt (fun w : ℂ => (a / ‖w‖) * (‖w‖ - 1)^3)
        (0 : ℂ →L[ℝ] ℝ) z := by
      have h := hn.hasFDerivAt.mul hc
      change HasFDerivAt (fun w : ℂ => (a / ‖w‖) * (‖w‖ - 1)^3) _ z at h
      simpa [hr] using h
    have h := (Complex.ofRealCLM.hasFDerivAt.comp z hcoef).mul (hasFDerivAt_id z)
    have he : (fun w : ℂ => (a / ‖w‖) * (‖w‖ - 1)^3) =
        (fun w : ℂ => a * (‖w‖ - 1)^3 / ‖w‖) := by
      funext w
      ring
    rw [he] at h
    change HasFDerivAt (fun w : ℂ => ((a*(‖w‖-1)^3/‖w‖ : ℝ) : ℂ)*w) _ z at h
    simpa [hr, Function.comp_def] using h
  let J : ℂ →L[ℝ] ℂ := Complex.I • ContinuousLinearMap.id ℝ ℂ
  have hj : HasFDerivAt (fun w : ℂ => Complex.I*w) J z := by
    exact J.hasFDerivAt
  have hfield : HasFDerivAt (field a) J z := by
    exact (hj.add hf).congr_fderiv (add_zero J)
  have heval : HasFDerivAt (autonomousEvalValue (oscillator a)) J z :=
    hfield.congr_of_eventuallyEq (Filter.mem_of_superset (domain_open.mem_nhds hz') (eval_eqOn a))
  rw [divergence, heval.fderiv, LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, LinearMap.toMatrix_apply]
  norm_num [J, Complex.coe_basisOneI, Complex.coe_basisOneI_repr, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private lemma circle_properties (a : ℝ) :
    IsComplete (oscillator a) (1 : ℂ) ∧
      Function.Periodic (fun t => flow (oscillator a) t 1) (2 * Real.pi) ∧
      (∀ T > 0, Function.Periodic (fun t => flow (oscillator a) t 1) T → 2 * Real.pi ≤ T) ∧
      ¬ IsConstant (oscillator a) (1 : ℂ) ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi), divergence (oscillator a) (flow (oscillator a) t 1)) = 0 := by
  have hflow : (fun t => flow (oscillator a) t 1) = circleCurve :=
    funext fun t => (circle_flow a t).2
  refine ⟨Subset.antisymm (subset_univ _) (fun t _ => (circle_flow a t).1),
    by rw [hflow]; exact circle_periodic, ?_, ?_, ?_⟩
  · intro T hT hper
    rw [hflow] at hper
    exact circle_least_period hT hper
  · intro hc
    have h := hc Real.pi (circle_flow a Real.pi).1
    rw [(circle_flow a Real.pi).2, circleCurve_eq] at h
    norm_num [Complex.exp_pi_mul_I] at h
  · have h (t : ℝ) : divergence (oscillator a) (flow (oscillator a) t 1) = 0 := by
      rw [(circle_flow a t).2]
      apply divergence_zero
      simp [unitCircle, circleCurve_eq]
    simp [h]

private lemma zeroDivergencePeriodicOrbit (a : ℝ) :
    Specs.D13Unified.Ch14.ZeroDivergence.ZeroDivergencePeriodicOrbit
      (oscillator a) 1 (2 * Real.pi) :=
  ⟨oscillator_c1 a, one_mem, Real.two_pi_pos, circle_properties a⟩

/-- The strict planar criteria cannot be extended to equality in either direction. -/
theorem zero_divergence_both_outcomes : Specs.D13Unified.Ch14.ZeroDivergence.ZeroDivergenceBothOutcomes := by
  constructor
  · refine ⟨oscillator (-1), 1, 2 * Real.pi, zeroDivergencePeriodicOrbit (-1), ?_⟩
    rw [circle_orbit]
    exact attracting
  · exact ⟨oscillator 1, 1, 2 * Real.pi, zeroDivergencePeriodicOrbit 1, repelling,
      D13Unified.Ch14.OrbitalInstability.unstable_of_distanceEscape (oscillator_c1 1) one_mem repelling⟩

end D13Unified.Ch14.ZeroDivergence
