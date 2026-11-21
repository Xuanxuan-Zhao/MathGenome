import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.PoissonSynthesis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.AbsoluteSynthesis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PositiveHarmonic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! Absolute Poisson synthesis (`fa2:p5:poisson-synthesis`).
Lebesgue differentiation and quantitative kernel estimates give convergence
at every Lebesgue point within each fixed Stolz cone. Exact dual norming
then gives an absolutely convergent expansion with the strict norm budget. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal lp

namespace ExpandedFA.PartV.PoissonSynthesis
open PartIV.PositiveHarmonic FunctionSpaces

variable {𝕜 : Type} [RCLike 𝕜]

/-- The circle inherits the covering property through its isometric inclusion
in the two-dimensional real normed space ℂ. -/
lemma circle_hasBesicovitchCovering : HasBesicovitchCovering Circle := by
  obtain ⟨N, τ, hτ, hno⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℂ)
  refine ⟨N, τ, hτ, ⟨fun a => ?_⟩⟩
  let b : Besicovitch.SatelliteConfig ℂ N τ :=
    { c := fun i => (a.c i : ℂ)
      r := a.r
      rpos := a.rpos
      h := a.h
      hlast := a.hlast
      inter := a.inter }
  exact hno.false b

/-- Lebesgue differentiation applies to this very Haar measure on the circle;
no assertion about ambient planar Lebesgue measure is used. -/
theorem ae_lebesgue_points : Spec.AeLebesguePoints := by
  intro 𝕜 _ g hg
  have := circle_hasBesicovitchCovering
  have hi : Integrable g circleHaar := hg.integrable le_top
  filter_upwards [(Besicovitch.vitaliFamily circleHaar).ae_tendsto_average_norm_sub
    hi.locallyIntegrable] with ζ hζ
  have h := hζ.comp (Besicovitch.tendsto_filterAt circleHaar ζ)
  simpa only [IsLebesguePoint, Function.comp_def, setAverage_eq, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- A quantitative Poisson-kernel bound on each fixed Stolz region. The
circle distance is chord distance, so no angular-coordinate convention enters. -/
lemma poissonKernel_stolz_bound {ζ : Circle} {M : ℝ} (hM : 0 < M)
    {z : ℂ} (hz : z ∈ stolzRegion ζ M) (η : Circle) :
    circlePoissonKernel z η ≤
      2 * (1 + (M + 1) ^ 2) * (1 - ‖z‖) /
        ((1 - ‖z‖) ^ 2 + ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2) := by
  have hcone := hz.2
  have hlt : ‖z‖ < 1 := hz.1
  have hh : 0 < 1 - ‖z‖ := sub_pos.mpr hlt
  have hD : 1 - ‖z‖ ≤ ‖(η : ℂ) - z‖ := by
    simpa using norm_sub_norm_le (η : ℂ) z
  have hDpos : 0 < ‖(η : ℂ) - z‖ := hh.trans_le hD
  have hd : ‖(η : ℂ) - (ζ : ℂ)‖ ≤ (M + 1) * ‖(η : ℂ) - z‖ := by
    calc
      ‖(η : ℂ) - (ζ : ℂ)‖ ≤ ‖(η : ℂ) - z‖ + ‖z - (ζ : ℂ)‖ :=
        by simpa only [dist_eq_norm] using dist_triangle (η : ℂ) z (ζ : ℂ)
      _ ≤ ‖(η : ℂ) - z‖ + M * (1 - ‖z‖) := add_le_add le_rfl hcone
      _ ≤ (M + 1) * ‖(η : ℂ) - z‖ := by nlinarith
  have hh2 : (1 - ‖z‖) ^ 2 ≤ ‖(η : ℂ) - z‖ ^ 2 :=
    (sq_le_sq₀ hh.le (norm_nonneg _)).mpr hD
  have hd2 : ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 ≤
      (M + 1) ^ 2 * ‖(η : ℂ) - z‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (M + 1) * ‖(η : ℂ) - z‖)).mpr hd
  have hden : 0 < (1 - ‖z‖) ^ 2 + ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 := by positivity
  have hn : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by nlinarith
  have hs : (1 - ‖z‖) ^ 2 + ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 ≤
      (1 + (M + 1) ^ 2) * ‖(η : ℂ) - z‖ ^ 2 := by nlinarith
  unfold circlePoissonKernel
  apply (div_le_div_iff₀ (sq_pos_of_pos hDpos) hden).mpr
  calc
    (1 - ‖z‖ ^ 2) * ((1 - ‖z‖) ^ 2 + ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2) ≤
        (2 * (1 - ‖z‖)) * ((1 - ‖z‖) ^ 2 + ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hn hden.le
    _ ≤ (2 * (1 - ‖z‖)) *
        ((1 + (M + 1) ^ 2) * ‖(η : ℂ) - z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (2 * (1 + (M + 1) ^ 2) * (1 - ‖z‖)) * ‖(η : ℂ) - z‖ ^ 2 := by ring

/-- A linear cap-mass bound obtained solely from Poisson normalization.
This avoids a separate angular parametrization of Haar measure. -/
lemma circleHaar_closedBall_le (ζ : Circle) {r : ℝ} (hr : 0 < r) :
    circleHaar.real (Metric.closedBall ζ r) ≤ 4 * r := by
  have := circleHaar_probability
  by_cases hr1 : r ≤ 1
  · let w : ℂ := (1 - r : ℝ) * (ζ : ℂ)
    have hwn : ‖w‖ = 1 - r := by
      change ‖((1 - r : ℝ) : ℂ) * (ζ : ℂ)‖ = 1 - r
      rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)]
    have hw : w ∈ unitDisk := by
      change ‖w‖ < 1
      rw [hwn]
      linarith
    have hwζ : ‖(ζ : ℂ) - w‖ = r := by
      have heq : (ζ : ℂ) - w = (r : ℂ) * (ζ : ℂ) := by dsimp [w]; push_cast; ring
      rw [heq]
      simp [abs_of_pos hr]
    have hlower (η : Circle) (hη : η ∈ Metric.closedBall ζ r) :
        1 / (4 * r) ≤ circlePoissonKernel w η := by
      have hη' : ‖(η : ℂ) - (ζ : ℂ)‖ ≤ r := by
        change dist (η : ℂ) (ζ : ℂ) ≤ r at hη
        simpa only [dist_eq_norm] using hη
      have hD : ‖(η : ℂ) - w‖ ≤ 2 * r := by
        calc
          ‖(η : ℂ) - w‖ ≤ ‖(η : ℂ) - (ζ : ℂ)‖ + ‖(ζ : ℂ) - w‖ :=
            by simpa only [dist_eq_norm] using dist_triangle (η : ℂ) (ζ : ℂ) w
          _ ≤ 2 * r := by rw [hwζ]; linarith
      have hD2 : ‖(η : ℂ) - w‖ ^ 2 ≤ 4 * r ^ 2 := by
        nlinarith [(sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * r)).mpr hD]
      have hnum : r ≤ 1 - ‖w‖ ^ 2 := by rw [hwn]; nlinarith
      unfold circlePoissonKernel
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * r)
        (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (circle_sub_ne_zero hw η)))).mpr
      nlinarith
    have hI := setIntegral_mono_on (integrable_const (1 / (4 * r))).integrableOn
      (integrable_circlePoissonKernel circleHaar hw).integrableOn
      measurableSet_closedBall hlower
    have hJ := setIntegral_le_integral (s := Metric.closedBall ζ r)
      (integrable_circlePoissonKernel circleHaar hw)
      (Eventually.of_forall (fun η => (circlePoissonKernel_pos hw η).le))
    rw [show (∫ η, circlePoissonKernel w η ∂circleHaar) = 1 from
      haar_normalization.2.2 w hw] at hJ
    simp only [setIntegral_const, smul_eq_mul, one_div] at hI
    have hmul : circleHaar.real (Metric.closedBall ζ r) * (4 * r)⁻¹ ≤ 1 := hI.trans hJ
    exact (mul_inv_le_iff₀ (by positivity : 0 < 4 * r)).mp hmul |>.trans_eq (one_mul _)
  · have hmass : circleHaar.real (Metric.closedBall ζ r) ≤ 1 := by
      simp
    linarith

lemma radial_point_mem {ζ : Circle} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ((1-r : ℝ) * (ζ : ℂ)) ∈ unitDisk := by
  change ‖((1-r : ℝ) : ℂ) * (ζ : ℂ)‖ < 1
  rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)]
  linarith

lemma radial_kernel_lower {ζ : Circle} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (η : Circle) (hη : r ≤ ‖(η : ℂ) - (ζ : ℂ)‖) :
    r / (4 * ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2) ≤
      circlePoissonKernel ((1-r : ℝ) * (ζ : ℂ)) η := by
  let w : ℂ := (1-r : ℝ) * (ζ : ℂ)
  have hw : w ∈ unitDisk := radial_point_mem hr hr1
  have hwn : ‖w‖ = 1-r := by
    change ‖((1-r : ℝ) : ℂ) * (ζ : ℂ)‖ = 1-r
    rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)]
  have hwζ : ‖(ζ : ℂ) - w‖ = r := by
    have heq : (ζ : ℂ) - w = (r : ℂ) * (ζ : ℂ) := by dsimp [w]; push_cast; ring
    rw [heq]
    simp [abs_of_pos hr]
  have hd : 0 < ‖(η : ℂ) - (ζ : ℂ)‖ := hr.trans_le hη
  have hD : ‖(η : ℂ) - w‖ ≤ 2 * ‖(η : ℂ) - (ζ : ℂ)‖ := by
    calc
      ‖(η : ℂ) - w‖ ≤ ‖(η : ℂ) - (ζ : ℂ)‖ + ‖(ζ : ℂ) - w‖ :=
        by simpa only [dist_eq_norm] using dist_triangle (η : ℂ) (ζ : ℂ) w
      _ ≤ 2 * ‖(η : ℂ) - (ζ : ℂ)‖ := by rw [hwζ]; linarith
  have hD2 : ‖(η : ℂ) - w‖ ^ 2 ≤ 4 * ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2 := by
    nlinarith [(sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖(η : ℂ) - (ζ : ℂ)‖)).mpr hD]
  have hnum : r ≤ 1 - ‖w‖ ^ 2 := by rw [hwn]; nlinarith
  change r / (4 * ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2) ≤ circlePoissonKernel w η
  unfold circlePoissonKernel
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (circle_sub_ne_zero hw η)))).mpr
  nlinarith

lemma poissonKernel_stolz_tail_bound {ζ : Circle} {M : ℝ} (hM : 0 < M)
    {z : ℂ} (hz : z ∈ stolzRegion ζ M) {R : ℝ} (hR : 0 < R)
    (hsmall : R * (1-‖z‖) ≤ 1) (η : Circle)
    (hη : R * (1-‖z‖) ≤ ‖(η : ℂ) - (ζ : ℂ)‖) :
    circlePoissonKernel z η ≤
      (4 * (2 * (1 + (M+1)^2)) / R) *
        circlePoissonKernel ((1-R * (1-‖z‖) : ℝ) * (ζ : ℂ)) η := by
  let C : ℝ := 2 * (1 + (M+1)^2)
  let h : ℝ := 1-‖z‖
  let d : ℝ := ‖(η : ℂ) - (ζ : ℂ)‖
  have hh : 0 < h := sub_pos.mpr hz.1
  have hC : 0 < C := by dsimp [C]; positivity
  have hd : 0 < d := (mul_pos hR hh).trans_le hη
  have hlower := radial_kernel_lower (mul_pos hR hh) hsmall η hη
  have hbound : circlePoissonKernel z η ≤ C * h / (h^2+d^2) :=
    poissonKernel_stolz_bound hM hz η
  calc
    circlePoissonKernel z η ≤ C * h / (h^2+d^2) := hbound
    _ ≤ C * h / d^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg h])
    _ = (4*C/R) * ((R*h) / (4*d^2)) := by field_simp
    _ ≤ (4*C/R) * circlePoissonKernel ((1-R*h : ℝ) * (ζ : ℂ)) η :=
      mul_le_mul_of_nonneg_left hlower (by positivity)

lemma cap_integral_le (f : Circle → ℝ)
    (hn : ∀ η, 0 ≤ f η) (ζ : Circle) {s : ℝ} (hs : 0 < s) :
    (∫ η in Metric.closedBall ζ s, f η ∂circleHaar) ≤
      4 * s * ((∫ η in Metric.closedBall ζ s, f η ∂circleHaar) /
        circleHaar.real (Metric.closedBall ζ s)) := by
  have havg : 0 ≤ (∫ η in Metric.closedBall ζ s, f η ∂circleHaar) /
        circleHaar.real (Metric.closedBall ζ s) :=
    div_nonneg (integral_nonneg hn) ENNReal.toReal_nonneg
  have heq := measure_smul_setAverage (μ := circleHaar) f
    (s := Metric.closedBall ζ s) (by simp)
  simp only [smul_eq_mul, setAverage_eq] at heq
  calc
    _ = circleHaar.real (Metric.closedBall ζ s) *
      ((∫ η in Metric.closedBall ζ s, f η ∂circleHaar) /
        circleHaar.real (Metric.closedBall ζ s)) := by
          simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (circleHaar_closedBall_le ζ hs) havg

lemma kernel_split_integral (f : Circle → ℝ) (hf : Integrable f circleHaar)
    (hn : ∀ η, 0 ≤ f η) {B : ℝ} (hB : ∀ᵐ η ∂circleHaar, f η ≤ B)
    (ζ : Circle) {z w : ℂ} (hz : z ∈ unitDisk) (hw : w ∈ unitDisk)
    {C h R : ℝ} (hC : 0 ≤ C) (hh : 0 < h) (hR : 0 < R)
    (hlocal : ∀ η, circlePoissonKernel z η ≤ C / h)
    (htail : ∀ η : Circle, R * h ≤ ‖(η : ℂ) - (ζ : ℂ)‖ →
      circlePoissonKernel z η ≤ (4*C/R) * circlePoissonKernel w η) :
    (∫ η, circlePoissonKernel z η * f η ∂circleHaar) ≤
      4*C*R*((∫ η in Metric.closedBall ζ (R*h), f η ∂circleHaar) /
        circleHaar.real (Metric.closedBall ζ (R*h))) + 4*C*B/R := by
  let S := Metric.closedBall ζ (R*h)
  have hi₁ : Integrable (fun η => (C/h) * S.indicator f η) circleHaar :=
    (hf.indicator measurableSet_closedBall).const_mul _
  have hi₂ : Integrable (fun η => (4*C/R) * B * circlePoissonKernel w η) circleHaar :=
    (integrable_circlePoissonKernel circleHaar hw).const_mul _
  have hle : ∀ᵐ η ∂circleHaar, circlePoissonKernel z η * f η ≤
      (C/h) * S.indicator f η + (4*C/R) * B * circlePoissonKernel w η := by
    filter_upwards [hB] with η hηB
    have hp := (circlePoissonKernel_pos hw η).le
    by_cases hη : η ∈ S
    · rw [indicator_of_mem hη]
      exact (mul_le_mul_of_nonneg_right (hlocal η) (hn η)).trans
        (le_add_of_nonneg_right (by have := (hn η).trans hηB; positivity))
    · rw [indicator_of_notMem hη, mul_zero, zero_add]
      have hd : R*h ≤ ‖(η : ℂ) - (ζ : ℂ)‖ := by
        have hdist : ¬dist η ζ ≤ R*h := hη
        change ¬dist (η : ℂ) (ζ : ℂ) ≤ R*h at hdist
        exact (lt_of_not_ge (by simpa only [dist_eq_norm] using hdist)).le
      calc
        _ ≤ ((4*C/R) * circlePoissonKernel w η) * f η :=
          mul_le_mul_of_nonneg_right (htail η hd) (hn η)
        _ ≤ ((4*C/R) * circlePoissonKernel w η) * B :=
          mul_le_mul_of_nonneg_left hηB (by positivity)
        _ = _ := by ring
  have hI := integral_mono_of_nonneg
    (Eventually.of_forall (fun η => mul_nonneg (circlePoissonKernel_pos hz η).le (hn η)))
    (hi₁.add hi₂) hle
  simp only [Pi.add_apply] at hI
  rw [integral_add hi₁ hi₂, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_closedBall,
    show (∫ η, circlePoissonKernel w η ∂circleHaar) = 1 from
      haar_normalization.2.2 w hw, mul_one] at hI
  refine hI.trans ?_
  have hcap := mul_le_mul_of_nonneg_left (cap_integral_le f hn ζ (mul_pos hR hh))
    (by positivity : 0 ≤ C/h)
  calc
    _ ≤ (C/h) * (4*(R*h)*((∫ η in S, f η ∂circleHaar)/circleHaar.real S)) + (4*C/R)*B :=
      add_le_add hcap le_rfl
    _ = _ := by dsimp [S]; field_simp

lemma integrable_poisson_mul {g : Circle → 𝕜} (hg : MemLp g ∞ circleHaar)
    {z : ℂ} (hz : z ∈ unitDisk) :
    Integrable (fun η => (circlePoissonKernel z η : 𝕜) * g η) circleHaar := by
  have hK : Integrable (fun η => (circlePoissonKernel z η : 𝕜)) circleHaar :=
    by
      simpa only [RCLike.ofRealCLM_apply] using
        (RCLike.ofRealCLM (K := 𝕜)).integrable_comp (integrable_circlePoissonKernel circleHaar hz)
  exact hK.mul_of_top_left hg

lemma integrable_poisson_oscillation {g : Circle → 𝕜} (hg : MemLp g ∞ circleHaar)
    (ζ : Circle) {z : ℂ} (hz : z ∈ unitDisk) :
    Integrable (fun η => circlePoissonKernel z η * ‖g η - g ζ‖) circleHaar := by
  exact (integrable_circlePoissonKernel circleHaar hz).mul_of_top_left
    (hg.sub (memLp_top_const (g ζ))).norm

lemma poissonTest_sub_identity {g : Circle → 𝕜} (hg : MemLp g ∞ circleHaar)
    (ζ : Circle) {z : ℂ} (hz : z ∈ unitDisk) :
    poissonTest g z - g ζ =
      ∫ η, (circlePoissonKernel z η : 𝕜) * (g η - g ζ) ∂circleHaar := by
  have hK : Integrable (fun η => (circlePoissonKernel z η : 𝕜)) circleHaar :=
    by
      simpa only [RCLike.ofRealCLM_apply] using
        (RCLike.ofRealCLM (K := 𝕜)).integrable_comp (integrable_circlePoissonKernel circleHaar hz)
  simp_rw [mul_sub]
  rw [integral_sub (integrable_poisson_mul hg hz) (hK.mul_const (g ζ)),
    integral_mul_const, integral_ofReal,
    show (∫ η, circlePoissonKernel z η ∂circleHaar) = 1 from haar_normalization.2.2 z hz]
  simp [poissonTest]

lemma norm_poissonTest_sub_le {g : Circle → 𝕜} (hg : MemLp g ∞ circleHaar)
    (ζ : Circle) {z : ℂ} (hz : z ∈ unitDisk) :
    ‖poissonTest g z - g ζ‖ ≤
      ∫ η, circlePoissonKernel z η * ‖g η - g ζ‖ ∂circleHaar := by
  rw [poissonTest_sub_identity hg ζ hz]
  calc
    _ ≤ ∫ η, ‖(circlePoissonKernel z η : 𝕜) * (g η - g ζ)‖ ∂circleHaar :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by
        dsimp only
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (circlePoissonKernel_pos hz η).le]

lemma ae_oscillation_bound {g : Circle → 𝕜} (hg : MemLp g ∞ circleHaar)
    (ζ : Circle) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ η ∂circleHaar, ‖g η - g ζ‖ ≤ B := by
  refine ⟨lpNorm (fun η => g η - g ζ) ∞ circleHaar, lpNorm_nonneg, ?_⟩
  exact ae_le_lpNorm_exponent_top
    (show MemLp (fun η => g η - g ζ) ∞ circleHaar from hg.sub (memLp_top_const (g ζ)))

lemma tendsto_zero_of_cap_average_bound {ζ : Circle} {M : ℝ}
    {f : Circle → ℝ} {F : ℂ → ℝ} {C B : ℝ}
    (hC : 0 < C) (hB : 0 ≤ B)
    (hmean : Tendsto (fun r : ℝ =>
      (∫ η in Metric.closedBall ζ r, f η ∂circleHaar) /
        circleHaar.real (Metric.closedBall ζ r)) (𝓝[>] 0) (𝓝 0))
    (hn : ∀ z ∈ stolzRegion ζ M, 0 ≤ F z)
    (hquant : ∀ R : ℝ, 0 < R → ∀ z ∈ stolzRegion ζ M,
      R * (1-‖z‖) ≤ 1 → F z ≤
        4*C*R * ((∫ η in Metric.closedBall ζ (R*(1-‖z‖)), f η ∂circleHaar) /
          circleHaar.real (Metric.closedBall ζ (R*(1-‖z‖)))) + 4*C*B/R) :
    Tendsto F (𝓝[stolzRegion ζ M] (ζ : ℂ)) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ha.trans_le (hn z hz)
  · intro ε hε
    let R : ℝ := (8*C*B+1)/ε
    have hR : 0 < R := by dsimp [R]; positivity
    have htail : 4*C*B/R < ε/2 := by
      apply (div_lt_iff₀ hR).mpr
      dsimp [R]
      field_simp
      nlinarith
    have hdepth : Tendsto (fun z : ℂ => R*(1-‖z‖))
        (𝓝[stolzRegion ζ M] (ζ : ℂ)) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Continuous (fun z : ℂ => R*(1-‖z‖)) := by fun_prop
        simpa only [Circle.norm_coe, sub_self, mul_zero] using
          (hc.continuousAt (x := (ζ : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_pos hR (sub_pos.mpr hz.1)
    have hlocal := (hmean.comp hdepth).const_mul (4*C*R)
    simp only [mul_zero, Function.comp_def] at hlocal
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_order.1 hlocal).2 (ε/2) (half_pos hε),
      (tendsto_order.1 (hdepth.mono_right nhdsWithin_le_nhds)).2 1 zero_lt_one] with z hz hloc hsmall
    exact (hquant R hR z hz hsmall.le).trans_lt (by linarith)

lemma poissonKernel_stolz_uniform_bound {ζ : Circle} {M : ℝ} (hM : 0 < M)
    {z : ℂ} (hz : z ∈ stolzRegion ζ M) (η : Circle) :
    circlePoissonKernel z η ≤ 2*(1+(M+1)^2) / (1-‖z‖) := by
  have hh : 0 < 1-‖z‖ := sub_pos.mpr hz.1
  refine (poissonKernel_stolz_bound hM hz η).trans ?_
  apply (div_le_div_iff₀ (by positivity) hh).mpr
  nlinarith [sq_nonneg ‖(η : ℂ) - (ζ : ℂ)‖]

theorem boundary_convergence : Spec.BoundaryConvergence := by
  intro 𝕜 _ g hg ζ hζ M hM
  obtain ⟨B, hB, hb⟩ := ae_oscillation_bound hg ζ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_zero_of_cap_average_bound
    (f := fun η => ‖g η-g ζ‖) (C := 2*(1+(M+1)^2)) (B := B)
    (by positivity) hB hζ
    (fun z hz => norm_nonneg _)
  intro R hR z hz hsmall
  refine (norm_poissonTest_sub_le hg ζ hz.1).trans ?_
  exact kernel_split_integral (fun η => ‖g η-g ζ‖)
    ((hg.integrable le_top).sub (integrable_const (g ζ))).norm
    (fun η => norm_nonneg _) hb ζ hz.1
    (radial_point_mem (mul_pos hR (sub_pos.mpr hz.1)) hsmall)
    (by positivity) (sub_pos.mpr hz.1) hR
    (poissonKernel_stolz_uniform_bound hM hz)
    (poissonKernel_stolz_tail_bound hM hz hR hsmall)

/-- The native L¹ atom has precisely the original pointwise representative. -/
lemma poissonAtom_coe (z : ℂ) (hz : z ∈ unitDisk) :
    (poissonAtom (𝕜 := 𝕜) z hz : Circle → 𝕜) =ᵐ[circleHaar]
      (fun ζ => (circlePoissonKernel z ζ : 𝕜)) :=
  AEEqFun.coeFn_mk _ _

/-- Normalization is with respect to the accepted probability Haar measure. -/
theorem kernel_norm : Spec.KernelNorm := by
  intro 𝕜 _ z hz
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ ζ, ‖poissonAtom (𝕜 := 𝕜) z hz ζ‖ ∂circleHaar) =
        ∫ ζ, circlePoissonKernel z ζ ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [poissonAtom_coe (𝕜 := 𝕜) z hz] with ζ hζ
      rw [hζ, RCLike.norm_ofReal, abs_of_nonneg (circlePoissonKernel_pos hz ζ).le]
    _ = 1 := haar_normalization.2.2 z hz

/-- The integral formula for the fixed scalar-linear L¹–L∞ pairing. -/
lemma pairing_poissonAtom (g : Lp 𝕜 ∞ circleHaar) (z : ℂ) (hz : z ∈ unitDisk) :
    ScalarLpIntegralPairingSpec.IntegralPairingValue circleHaar 1 ∞ g (poissonAtom z hz) =
      poissonTest (g : Circle → 𝕜) z := by
  rw [(lp_pairing_integral circleHaar 1 ∞ g (poissonAtom z hz)).2]
  apply integral_congr_ae
  filter_upwards [poissonAtom_coe (𝕜 := 𝕜) z hz] with ζ hζ
  rw [hζ]

/-- Positivity and unit mass give the upper half of the norming equality. -/
lemma norm_poissonTest_le (g : Lp 𝕜 ∞ circleHaar) (z : ℂ) (hz : z ∈ unitDisk) :
    ‖poissonTest (g : Circle → 𝕜) z‖ ≤ ‖g‖ := by
  rw [← pairing_poissonAtom g z hz]
  simpa only [kernel_norm 𝕜 z hz, mul_one] using
    lp_pairing_apply_bound circleHaar 1 ∞ g (poissonAtom z hz)

/-- Boundary limits on the actual nontangential subsequences yield the sharp
lower bound for each L∞ test; the kernel estimate gives the reverse bound. -/
theorem exact_norming_of_boundary_convergence : Spec.ExactNormingOfBoundaryConvergence := by
  intro hboundary hae 𝕜 _ z hz hd g
  have hb : BddAbove (range (fun n => ‖poissonTest (g : Circle → 𝕜) (z n)‖)) :=
    ⟨‖g‖, by rintro _ ⟨n, rfl⟩; exact norm_poissonTest_le g (z n) (hz n)⟩
  apply le_antisymm
  · exact ciSup_le (fun n => norm_poissonTest_le g (z n) (hz n))
  · have hnonneg : 0 ≤ ⨆ n : ℕ, ‖poissonTest (g : Circle → 𝕜) (z n)‖ :=
      (norm_nonneg _).trans (le_ciSup hb 0)
    have hle : ∀ᵐ (ζ : Circle) ∂circleHaar,
        ‖g ζ‖ ≤ ⨆ n : ℕ, ‖poissonTest (g : Circle → 𝕜) (z n)‖ := by
      filter_upwards [hd, hae 𝕜 (g : Circle → 𝕜) (Lp.memLp g)] with ζ hζ hleb
      obtain ⟨M, hM, k, _hk, hlim, hcone⟩ := hζ
      have hwithin : Tendsto (fun j => z (k j)) atTop
          (𝓝[stolzRegion ζ M] (ζ : ℂ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hcone⟩
      have htest := (hboundary 𝕜 (g : Circle → 𝕜) (Lp.memLp g) ζ hleb M hM).comp hwithin
      exact le_of_tendsto htest.norm (Eventually.of_forall (fun j => le_ciSup hb (k j)))
    simpa using Lp.norm_le_of_ae_bound hnonneg hle

/-- L¹ duality identifies all continuous scalar-linear tests with L∞ tests,
with equality of their native norms. -/
theorem dual_norming_of_exact_norming : Spec.DualNormingOfExactNorming := by
  intro hnorm 𝕜 _ z hz hd L
  obtain ⟨g, hg, _⟩ := lp_one_infinity_duality_sigmaFinite circleHaar L
  have heq (n : ℕ) : L (poissonAtom (z n) (hz n)) =
      poissonTest (g : Circle → 𝕜) (z n) := by
    rw [(hg.1 (poissonAtom (z n) (hz n))).2]
    apply integral_congr_ae
    filter_upwards [poissonAtom_coe (𝕜 := 𝕜) (z n) (hz n)] with ζ hζ
    rw [hζ]
  simp_rw [heq]
  exact (hnorm 𝕜 z hz hd g).trans hg.2

/-- Applying quantitative synthesis at β=1 gives an exact absolutely
convergent expansion and the source's strict sum of coefficient moduli. -/
theorem synthesis_of_dual_norming : Spec.SynthesisOfDualNorming := by
  intro hnorm 𝕜 _ z hz hd f ε hε
  obtain ⟨a, ha, habs, hbudget⟩ :=
    AbsoluteSynthesis.quantitative_absolute_synthesis 𝕜 (Lp 𝕜 1 circleHaar)
      (fun n => poissonAtom (z n) (hz n)) 1
      (fun n => (kernel_norm 𝕜 (z n) (hz n)).le) zero_lt_one
      (fun L => by rw [hnorm 𝕜 z hz hd L, one_mul]) f ε hε
  refine ⟨a, ha, habs, ?_⟩
  have hanorm : (∑' n, ‖a n‖) = ‖a‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num) a]
    norm_num
  simpa only [hanorm, inv_one, one_mul] using hbudget

/-- The Banach-space assembly from the harmonic boundary limit. -/
theorem synthesis_of_boundary_convergence : Spec.SynthesisOfBoundaryConvergence := by
  intro hboundary
  exact synthesis_of_dual_norming
    (dual_norming_of_exact_norming
      (exact_norming_of_boundary_convergence hboundary ae_lebesgue_points))


/-- The nontangentially dense sequence exactly norms every L∞ test. -/
theorem exact_norming : Spec.ExactNorming :=
  exact_norming_of_boundary_convergence boundary_convergence ae_lebesgue_points

/-- The Poisson atoms exactly norm every continuous scalar-linear L¹ functional. -/
theorem dual_norming : Spec.DualNorming :=
  dual_norming_of_exact_norming exact_norming

/-- Every real or complex L¹ class has the source's exact absolutely convergent
Poisson-kernel expansion, with coefficient sum strictly below ‖f‖ + ε. -/
theorem absolute_poisson_synthesis : Spec.AbsolutePoissonSynthesis :=
  synthesis_of_dual_norming dual_norming

end ExpandedFA.PartV.PoissonSynthesis
