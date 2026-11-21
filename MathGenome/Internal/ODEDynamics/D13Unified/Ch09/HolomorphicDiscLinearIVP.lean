import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.HolomorphicDiscLinearIVP
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.HolomorphicDependence
/-! Picard's series on a centered complex disc. The integral is radial, but
its complex derivative is justified using a holomorphic primitive on a disc.
No complex continuation or path-independence certificate is assumed. -/
namespace D13Unified.Ch09.HolomorphicDiscLinearIVP

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Integration on the straight segment from zero to `z`. -/
noncomputable def radialIntegral (f : ℂ → E) (z : ℂ) : E :=
  z • ∫ t : ℝ in 0..1, f ((t : ℂ) * z)

lemma radial_mem_closedBall {r : ℝ} {z : ℂ} (hz : z ∈ closedBall 0 r)
    {t : ℝ} (ht : t ∈ Icc 0 1) : (t : ℂ) * z ∈ closedBall 0 r := by
  simp only [mem_closedBall, dist_zero_right] at hz ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans hz

lemma radial_mem_ball {r : ℝ} {z : ℂ} (_hr : 0 < r) (hz : z ∈ ball 0 r)
    {t : ℝ} (ht : t ∈ Icc 0 1) : (t : ℂ) * z ∈ ball 0 r := by
  simp only [mem_ball, dist_zero_right] at hz ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz

lemma radial_continuousOn {r : ℝ} {f : ℂ → E} (hf : ContinuousOn f (ball 0 r))
    (hr : 0 < r) {z : ℂ} (hz : z ∈ ball 0 r) :
    ContinuousOn (fun t : ℝ => f ((t : ℂ) * z)) (Icc 0 1) :=
  hf.comp (by fun_prop) (fun _ ht => radial_mem_ball hr hz ht)

lemma radialIntegral_eq_sub {r : ℝ} {f g : ℂ → E}
    (hr : 0 < r) (hf : ContinuousOn f (ball 0 r))
    (hg : ∀ z ∈ ball 0 r, HasDerivAt g (f z) z) {z : ℂ} (hz : z ∈ ball 0 r) :
    radialIntegral f z = g z - g 0 := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun s : ℝ => g ((s : ℂ) * z)) (z • f ((t : ℂ) * z)) t := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using! (hg _ (radial_mem_ball hr hz ht)).scomp t
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z)
  have hi : IntervalIntegrable (fun t : ℝ => z • f ((t : ℂ) * z)) volume 0 1 :=
    (show ContinuousOn (fun t : ℝ => z • f ((t : ℂ) * z)) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.smul_apply] using!
        (radial_continuousOn hf hr hz).const_smul z).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht)) hi
  simpa [radialIntegral, intervalIntegral.integral_smul] using h

lemma hasDerivAt_radialIntegral {r : ℝ} {f : ℂ → E}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball 0 r))
    {z : ℂ} (hz : z ∈ ball 0 r) :
    HasDerivAt (radialIntegral f) (f z) z := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  have he : radialIntegral f =ᶠ[𝓝 z] fun w => g w - g 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact radialIntegral_eq_sub hr hf.continuousOn hg hw
  exact ((hg z hz).sub_const (g 0)).congr_of_eventuallyEq he

/-- Homogeneous Picard terms; their sum, rather than one term, solves the IVP. -/
noncomputable def picardTerm (A : ℂ → E →L[ℂ] E) (η : E) : ℕ → ℂ → E
  | 0 => fun _ => η
  | j + 1 => radialIntegral (fun z => A z (picardTerm A η j z))

@[simp] lemma picardTerm_zero (A : ℂ → E →L[ℂ] E) (η : E) (z : ℂ) :
    picardTerm A η 0 z = η := rfl

@[simp] lemma picardTerm_succ_at_zero (A : ℂ → E →L[ℂ] E) (η : E) (j : ℕ) :
    picardTerm A η (j+1) 0 = 0 := by simp [picardTerm, radialIntegral]

lemma picardTerm_differentiableOn {A : ℂ → E →L[ℂ] E} {r : ℝ}
    (hr : 0 < r) (hA : DifferentiableOn ℂ A (ball 0 r)) (η : E) (j : ℕ) :
    DifferentiableOn ℂ (picardTerm A η j) (ball 0 r) := by
  induction j with
  | zero => exact differentiableOn_const _
  | succ j ih =>
    exact fun z hz =>
      (hasDerivAt_radialIntegral hr (hA.clm_apply ih) hz).differentiableAt.differentiableWithinAt

lemma hasDerivAt_picardTerm_succ {A : ℂ → E →L[ℂ] E} {r : ℝ}
    (hr : 0 < r) (hA : DifferentiableOn ℂ A (ball 0 r)) (η : E) (j : ℕ)
    {z : ℂ} (hz : z ∈ ball 0 r) :
    HasDerivAt (picardTerm A η (j+1)) (A z (picardTerm A η j z)) z :=
  hasDerivAt_radialIntegral hr (hA.clm_apply (picardTerm_differentiableOn hr hA η j)) hz

/-- The elementary monomial estimate for integration along a radius. -/
lemma norm_radialIntegral_le {r C : ℝ} {f : ℂ → E} (j : ℕ)
    (hf : ∀ w ∈ closedBall 0 r, ‖f w‖ ≤ C * ‖w‖ ^ j)
    {z : ℂ} (hz : z ∈ closedBall 0 r) :
    ‖radialIntegral f z‖ ≤ C * ‖z‖ ^ (j+1) / (j+1) := by
  have hb (t : ℝ) (ht : t ∈ Icc 0 1) :
      ‖f ((t : ℂ) * z)‖ ≤ (C * ‖z‖ ^ j) * t ^ j := by
    calc
      _ ≤ C * ‖(t : ℂ) * z‖ ^ j := hf _ (radial_mem_closedBall hz ht)
      _ = _ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_pow]
        ring
  calc
    ‖radialIntegral f z‖ = ‖z‖ * ‖∫ t : ℝ in 0..1, f ((t : ℂ) * z)‖ := norm_smul _ _
    _ ≤ ‖z‖ * (∫ t : ℝ in 0..1, (C * ‖z‖ ^ j) * t ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (Filter.Eventually.of_forall (fun t ht => hb t ⟨ht.1.le, ht.2⟩))
      exact (continuous_const.mul (continuous_id.pow j)).intervalIntegrable _ _
    _ = C * ‖z‖ ^ (j+1) / (j+1) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, zero_pow (Nat.succ_ne_zero j), sub_zero]
      ring

/-- The factorial bound holds simultaneously at all points of a closed disc.
Only a bound on the coefficient on that disc is needed for this estimate. -/
lemma picardTerm_norm_le {A : ℂ → E →L[ℂ] E} {r M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ z ∈ closedBall 0 r, ‖A z‖ ≤ M)
    (η : E) (j : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 r) :
    ‖picardTerm A η j z‖ ≤ ‖η‖ * M ^ j * ‖z‖ ^ j / j.factorial := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    calc
      _ ≤ (‖η‖ * M ^ (j+1) / j.factorial) * ‖z‖ ^ (j+1) / (j+1) := by
        apply norm_radialIntegral_le j _ hz
        intro w hw
        calc
          _ ≤ ‖A w‖ * ‖picardTerm A η j w‖ := (A w).le_opNorm _
          _ ≤ M * (‖η‖ * M ^ j * ‖w‖ ^ j / j.factorial) := by
            exact mul_le_mul (hA w hw) (ih hw) (norm_nonneg _) hM
          _ = _ := by rw [pow_succ]; ring
      _ = ‖η‖ * M ^ (j+1) * ‖z‖ ^ (j+1) / (j+1).factorial := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp

lemma picardTerm_uniform_bound {A : ℂ → E →L[ℂ] E} {r M : ℝ}
    (_hr : 0 ≤ r) (hM : 0 ≤ M) (hA : ∀ z ∈ closedBall 0 r, ‖A z‖ ≤ M)
    (η : E) (j : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 r) :
    ‖picardTerm A η j z‖ ≤ ‖η‖ * ((M*r) ^ j / j.factorial) := by
  calc
    _ ≤ ‖η‖ * M ^ j * ‖z‖ ^ j / j.factorial := picardTerm_norm_le hM hA η j hz
    _ ≤ ‖η‖ * M ^ j * r ^ j / j.factorial := by
      gcongr
      simpa using hz
    _ = _ := by rw [mul_pow]; ring

/-- The global candidate uses one and the same series at every point. -/
noncomputable def picardSum (A : ℂ → E →L[ℂ] E) (η : E) (z : ℂ) : E :=
  ∑' j : ℕ, picardTerm A η j z

lemma tendstoUniformlyOn_picardSum {A : ℂ → E →L[ℂ] E} {r M : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hA : ∀ z ∈ closedBall 0 r, ‖A z‖ ≤ M) (η : E) :
    TendstoUniformlyOn
      (fun N z => ∑ j ∈ Finset.range N, picardTerm A η j z)
      (picardSum A η) atTop (closedBall 0 r) := by
  apply tendstoUniformlyOn_tsum_nat ((Real.summable_pow_div_factorial (M*r)).mul_left ‖η‖)
  exact fun j z hz => picardTerm_uniform_bound hr hM hA η j hz

lemma summable_picardTerm {A : ℂ → E →L[ℂ] E} {r M : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hA : ∀ z ∈ closedBall 0 r, ‖A z‖ ≤ M)
    (η : E) {z : ℂ} (hz : z ∈ closedBall 0 r) :
    Summable (fun j => picardTerm A η j z) := by
  exact Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (M*r)).mul_left ‖η‖)
    (fun j => picardTerm_uniform_bound hr hM hA η j hz)

@[simp] lemma picardSum_initial (A : ℂ → E →L[ℂ] E) (η : E) :
    picardSum A η 0 = η := by
  rw [picardSum, tsum_eq_single 0]
  · rfl
  · intro j hj
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact picardTerm_succ_at_zero A η j

/-- Passing the complex derivative through the Picard series is justified by
uniform convergence of the derivative series on the closed disc. -/
lemma hasDerivAt_picardSum_on_ball {A : ℂ → E →L[ℂ] E} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hA : DifferentiableOn ℂ A (ball 0 r))
    (hAb : ∀ z ∈ closedBall 0 r, ‖A z‖ ≤ M) (η : E)
    {z : ℂ} (hz : z ∈ ball 0 r) :
    HasDerivAt (picardSum A η) (A z (picardSum A η z)) z := by
  let F : ℕ → ℂ → E := fun N w => η + ∑ j ∈ Finset.range N, picardTerm A η (j+1) w
  let F' : ℕ → ℂ → E := fun N w => ∑ j ∈ Finset.range N, A w (picardTerm A η j w)
  have hF (N : ℕ) (w : ℂ) (hw : w ∈ ball 0 r) : HasDerivAt (F N) (F' N w) w := by
    have h := (HasDerivAt.fun_sum (u := Finset.range N)
      (fun j _ => hasDerivAt_picardTerm_succ hr hA η j hw)).const_add η
    simpa only [F, F'] using h
  have hbound (j : ℕ) (w : ℂ) (hw : w ∈ closedBall 0 r) :
      ‖A w (picardTerm A η j w)‖ ≤ (M * ‖η‖) * ((M*r)^j / j.factorial) := by
    calc
      _ ≤ ‖A w‖ * ‖picardTerm A η j w‖ := (A w).le_opNorm _
      _ ≤ M * (‖η‖ * ((M*r)^j / j.factorial)) :=
        mul_le_mul (hAb w hw) (picardTerm_uniform_bound hr.le hM hAb η j hw)
          (norm_nonneg _) hM
      _ = _ := by ring
  have hF' : TendstoUniformlyOn F' (fun w => A w (picardSum A η w)) atTop (ball 0 r) := by
    have ht := tendstoUniformlyOn_tsum_nat
      ((Real.summable_pow_div_factorial (M*r)).mul_left (M * ‖η‖)) hbound
    apply (ht.congr_right ?_).mono ball_subset_closedBall
    intro w hw
    exact ((A w).map_tsum (summable_picardTerm hr.le hM hAb η hw)).symm
  have hlim (w : ℂ) (hw : w ∈ ball 0 r) :
      Tendsto (fun N => F N w) atTop (𝓝 (picardSum A η w)) := by
    have hs := summable_picardTerm hr.le hM hAb η (ball_subset_closedBall hw)
    have hs' := (summable_nat_add_iff 1).mpr hs
    have he : η + ∑' j : ℕ, picardTerm A η (j+1) w = picardSum A η w := by
      simpa only [Finset.sum_range_one, picardTerm_zero, picardSum] using hs.sum_add_tsum_nat_add 1
    rw [← he]
    exact tendsto_const_nhds.add hs'.hasSum.tendsto_sum_nat
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_ball hF'
    (Filter.Eventually.of_forall hF) hlim hz

/-- Every point of the extended-radius disc lies in a finite centered disc
whose closure is still contained in the original domain. -/
lemma exists_closedBall_sub_disc {R : ℝ≥0∞} {z : ℂ} (hz : z ∈ disc R) :
    ∃ r : ℝ, 0 < r ∧ z ∈ ball 0 r ∧ closedBall 0 r ⊆ disc R := by
  change edist z 0 < R at hz
  obtain ⟨r, hr0, hzr, hrR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hz
  have hr : 0 < r := by
    have hpos : 0 < ENNReal.ofReal r := (bot_le : 0 ≤ edist z 0).trans_lt hzr
    exact ENNReal.ofReal_pos.mp hpos
  refine ⟨r, hr, ?_, ?_⟩
  · rw [edist_dist] at hzr
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hzr
  · intro w hw
    change edist w 0 < R
    rw [edist_dist]
    exact (ENNReal.ofReal_le_ofReal (mem_closedBall.mp hw)).trans_lt hrR

lemma coefficient_bound_on_closedBall {A : ℂ → E →L[ℂ] E} {r : ℝ}
    (hA : ContinuousOn A (closedBall 0 r)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedBall 0 r, ‖A z‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hA
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

lemma hasDerivAt_picardSum_on_disc {A : ℂ → E →L[ℂ] E} {R : ℝ≥0∞}
    (hA : DifferentiableOn ℂ A (disc R)) (η : E) {z : ℂ} (hz : z ∈ disc R) :
    HasDerivAt (picardSum A η) (A z (picardSum A η z)) z := by
  obtain ⟨r, hr, hzr, hrR⟩ := exists_closedBall_sub_disc hz
  obtain ⟨M, hM, hAb⟩ := coefficient_bound_on_closedBall (hA.continuousOn.mono hrR)
  exact hasDerivAt_picardSum_on_ball hr hM
    (hA.mono (ball_subset_closedBall.trans hrR)) hAb η hzr

/-- Uniqueness is proved along the segment from zero to each point using the
real Grönwall inequality. The functions being compared still have complex
derivatives everywhere on the full complex domain. -/
lemma linear_solution_unique_on_disc {A : ℂ → E →L[ℂ] E} {R : ℝ≥0∞}
    (hA : ContinuousOn A (disc R)) {Y Z : ℂ → E}
    (hY : ∀ z ∈ disc R, HasDerivAt Y (A z (Y z)) z)
    (hZ : ∀ z ∈ disc R, HasDerivAt Z (A z (Z z)) z)
    (hinit : Y 0 = Z 0) : EqOn Y Z (disc R) := by
  intro z hz
  obtain ⟨r, hr, hzr, hrR⟩ := exists_closedBall_sub_disc hz
  obtain ⟨M, hM, hAb⟩ := coefficient_bound_on_closedBall (hA.mono hrR)
  let d : ℝ → E := fun t => Y ((t : ℂ) * z) - Z ((t : ℂ) * z)
  let d' : ℝ → E := fun t => z • A ((t : ℂ) * z) (d t)
  have hm (t : ℝ) (ht : t ∈ Icc 0 1) : (t : ℂ) * z ∈ disc R :=
    hrR (radial_mem_closedBall (ball_subset_closedBall hzr) ht)
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivAt d (d' t) t := by
    simpa only [d, d', Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_mul, map_sub] using!
      ((hY _ (hm t ht)).sub (hZ _ (hm t ht))).scomp t
        ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z)
  have hd0 : d 0 = 0 := by simpa [d, sub_eq_zero] using hinit
  have hb (t : ℝ) (ht : t ∈ Ico 0 1) : ‖d' t‖ ≤ (‖z‖ * M) * ‖d t‖ := by
    calc
      ‖d' t‖ = ‖z‖ * ‖A ((t : ℂ) * z) (d t)‖ := norm_smul _ _
      _ ≤ ‖z‖ * (‖A ((t : ℂ) * z)‖ * ‖d t‖) :=
        mul_le_mul_of_nonneg_left ((A _).le_opNorm _) (norm_nonneg z)
      _ ≤ ‖z‖ * (M * ‖d t‖) := by
        gcongr
        exact hAb _ (radial_mem_closedBall (ball_subset_closedBall hzr) ⟨ht.1, ht.2.le⟩)
      _ = _ := by ring
  have hu := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hd0 hb
  simpa only [d, Complex.ofReal_one, one_mul, sub_eq_zero] using hu 1 ⟨by norm_num, le_rfl⟩

/-- The requested conditional draft. Both frozen premise types occur in the
required order. The Picard-series derivation above is independent of them. -/
theorem holomorphic_disc_linear_ivp_conditional
    (_holomorphic_dependence :
      Specs.D13Unified.Ch06.HolomorphicDependence.holomorphic_dependence_type)
    (_solution_germ_unique :
      Specs.D13Unified.Ch06.HolomorphicDependence.solution_germ_unique_type) :
    Specs.D13Unified.Ch09.HolomorphicDiscLinearIVP.holomorphic_disc_linear_ivp_type := by
  intro n R _hR A hA η
  refine ⟨picardSum A η, ⟨picardSum_initial A η, ?_, ?_⟩, ?_⟩
  · exact fun z hz =>
      (hasDerivAt_picardSum_on_disc hA η hz).differentiableAt.differentiableWithinAt
  · exact fun z hz => hasDerivAt_picardSum_on_disc hA η hz
  · intro Z hZ
    exact linear_solution_unique_on_disc hA.continuousOn hZ.2.2
      (fun z hz => hasDerivAt_picardSum_on_disc hA η hz)
      (hZ.1.trans (picardSum_initial A η).symm)

/-- The usual matrix/operator correspondence is complex linear and continuous
in finite dimension. It does not alter the state space or the equation. -/
noncomputable def matrixOperatorEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃L[ℂ]
      (D13Unified.Ch06.HolomorphicDependence.State n →L[ℂ]
        D13Unified.Ch06.HolomorphicDependence.State n) :=
  ((Matrix.toLin' : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ]
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

@[simp] lemma matrixOperatorEquiv_apply (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) : matrixOperatorEquiv n B v = B.mulVec v :=
  Matrix.toLin'_apply B v

/-- The explicit specialization to a holomorphic matrix coefficient. -/
theorem holomorphic_disc_matrix_ivp_conditional
    (holomorphic_dependence :
      Specs.D13Unified.Ch06.HolomorphicDependence.holomorphic_dependence_type)
    (solution_germ_unique :
      Specs.D13Unified.Ch06.HolomorphicDependence.solution_germ_unique_type) :
    Specs.D13Unified.Ch09.HolomorphicDiscLinearIVP.holomorphic_disc_matrix_ivp_type := by
  intro n R hR A hA η
  have hB : DifferentiableOn ℂ (fun z => matrixOperatorEquiv n (A z)) (disc R) :=
    (matrixOperatorEquiv n).differentiable.comp_differentiableOn hA
  obtain ⟨Y, hY, hu⟩ := holomorphic_disc_linear_ivp_conditional holomorphic_dependence
    solution_germ_unique n R hR (fun z => matrixOperatorEquiv n (A z)) hB η
  refine ⟨Y, ⟨hY.1, hY.2.1, ?_⟩, ?_⟩
  · simpa only [matrixOperatorEquiv_apply] using hY.2.2
  · intro Z hZ0 hZ
    apply hu Z
    refine ⟨hZ0, ?_, ?_⟩
    · exact fun z hz => (hZ z hz).differentiableAt.differentiableWithinAt
    · simpa only [matrixOperatorEquiv_apply] using hZ

end D13Unified.Ch09.HolomorphicDiscLinearIVP

theorem _root_.«D13Unified».«Ch09».«HolomorphicDiscLinearIVP».«holomorphic_disc_linear_ivp» : _root_.«Specs».«D13Unified».«Ch09».«HolomorphicDiscLinearIVP».«holomorphic_disc_linear_ivp_type» :=
  @_root_.«D13Unified».«Ch09».«HolomorphicDiscLinearIVP».«holomorphic_disc_linear_ivp_conditional» (@_root_.«D13Unified».«Ch06».«HolomorphicDependence».«holomorphic_dependence») (@_root_.«D13Unified».«Ch06».«HolomorphicDependence».«solution_germ_unique»)
theorem _root_.«D13Unified».«Ch09».«HolomorphicDiscLinearIVP».«holomorphic_disc_matrix_ivp» : _root_.«Specs».«D13Unified».«Ch09».«HolomorphicDiscLinearIVP».«holomorphic_disc_matrix_ivp_type» :=
  @_root_.«D13Unified».«Ch09».«HolomorphicDiscLinearIVP».«holomorphic_disc_matrix_ivp_conditional» (@_root_.«D13Unified».«Ch06».«HolomorphicDependence».«holomorphic_dependence») (@_root_.«D13Unified».«Ch06».«HolomorphicDependence».«solution_germ_unique»)
