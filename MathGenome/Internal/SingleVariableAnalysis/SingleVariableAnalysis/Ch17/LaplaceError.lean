import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.LaplaceError
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.LaplaceLocalization
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.UniformBound
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Substitution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
namespace SingleVariableAnalysis.LaplaceError
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
namespace S
export Specs.SingleVariableAnalysis.Ch17.LaplaceError
  (normalizedError cubicRemainder gaussianMomentIntegrable omittedGaussianTail)
end S

/-- A damped exponential is Lipschitz on every lower-bounded half-line,
with the sharp derivative bound. -/
theorem exp_neg_difference_le (u v m : ℝ) (hu : m ≤ u) (hv : m ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u-v| * Real.exp (-m) := by
  wlog huv : u ≤ v generalizing u v
  · simpa only [abs_sub_comm] using this v u hv hu (le_of_not_ge huv)
  have hsign : 0 ≤ Real.exp (-u) - Real.exp (-v) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg huv))
  rw [abs_of_nonneg hsign, abs_of_nonpos (sub_nonpos.mpr huv)]
  have hexp := Real.add_one_le_exp (u-v)
  have he : Real.exp (-u) * Real.exp (u-v) = Real.exp (-v) := by
    rw [← Real.exp_add]; congr 1; ring
  have hh : Real.exp (-u) - Real.exp (-v) ≤ (v-u) * Real.exp (-u) := by
    have ht := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-u)).le
    rw [he] at ht
    nlinarith
  calc
    _ ≤ (v-u) * Real.exp (-u) := hh
    _ ≤ (v-u) * Real.exp (-m) := by gcongr
    _ = -(u-v) * Real.exp (-m) := by ring

/-- This version uses norm powers, so it covers both half-lines and the
origin. Mathlib proves its moment-integrability theorem by a one-dimensional
power substitution into a positive Gamma integral. -/
theorem gaussian_moment_integrable : S.gaussianMomentIntegrable := by
  intro c hc
  have h1 := integrable_rpow_mul_exp_neg_mul_sq hc (s := 1) (by norm_num)
  have h3 := integrable_rpow_mul_exp_neg_mul_sq hc (s := 3) (by norm_num)
  convert h1.norm.add h3.norm using 1
  ext y
  simp [Real.rpow_ofNat, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), add_mul]


/-- A compact subinterval of the local C³ neighborhood gives a uniform
third-derivative bound, hence a cubic remainder at the stationary point. -/
theorem cubic_remainder : S.cubicRemainder := by
  intro φ a b x₀ hφ hx hmin hφ3
  obtain ⟨U, hU, hxU, h3⟩ := hφ3
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let r := min (δ/2) (min ((x₀-a)/2) ((b-x₀)/2))
  have hr : 0 < r := lt_min (half_pos hδ)
    (lt_min (half_pos (sub_pos.mpr hx.1)) (half_pos (sub_pos.mpr hx.2)))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hra : r ≤ (x₀-a)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ (b-x₀)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Icc (x₀-r) (x₀+r) ⊆ U := by
    intro x hxi
    apply hδU
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [hxi.1], by linarith [hxi.2]⟩).trans_lt hrδ
  have ho := (ckOn_iff_contDiffOn 3 φ U hU).mpr h3
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((ho.2 3 le_rfl).mono hsub)
  have hD : ClosedDerivativeFamily 2 φ (x₀-r) (x₀+r)
      (fun j => RealIteratedDerivative j φ) := by
    refine ⟨fun _ _ => rfl, fun j hj => (ho.2 j (by omega)).mono hsub, ?_⟩
    intro j hj x hxi
    simpa only [realIteratedDerivative_succ] using
      (ho.1 j (by omega) x (hsub hxi)).hasDerivAt.hasDerivWithinAt
  refine ⟨r, max M 0 / 6, hr, by positivity, by linarith, by linarith, ?_⟩
  intro h hh
  have hxJ : x₀ ∈ Icc (x₀-r) (x₀+r) := ⟨by linarith, by linarith⟩
  have hxJh : x₀+h ∈ Icc (x₀-r) (x₀+r) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hh
    constructor <;> linarith
  have ht := uniform_taylor_bound φ 2 (x₀-r) (x₀+r) (max M 0)
    (fun j => RealIteratedDerivative j φ) hD
    (fun x hxi => ho.1 2 (by norm_num) x (hsub (Ioo_subset_Icc_self hxi)))
    (fun x hxi => (hM x (Ioo_subset_Icc_self hxi)).trans (le_max_left _ _))
    x₀ hxJ (x₀+h) hxJh
  have hs := LaplaceLocalization.stationary φ a b x₀ hφ hx hmin
  norm_num [Finset.sum_range_succ, RealIteratedDerivative, iteratedDeriv_succ, hs] at ht
  convert ht using 1 <;> ring_nf

/-- Factor half the Gaussian exponent out of its tail. The remaining
Gaussian is integrable, so the bound is uniform for all nonnegative t. -/
theorem omitted_gaussian_tail : S.omittedGaussianTail := by
  intro c r hc hr
  have hc2 : 0 < c/2 := half_pos hc
  have hi := integrable_exp_neg_mul_sq hc2
  refine ⟨∫ y : ℝ, Real.exp (-(c/2)*y^2),
    integral_nonneg (fun _ => (Real.exp_pos _).le), ?_⟩
  intro t ht
  let E := {y : ℝ | r * Real.sqrt t ≤ |y|}
  have hE : MeasurableSet E := measurableSet_le measurable_const (continuous_abs.measurable)
  have hp (y : ℝ) (hy : y ∈ E) :
      Real.exp (-c*y^2) ≤
        Real.exp (-(c*r^2/2)*t) * Real.exp (-(c/2)*y^2) := by
    have hs : r^2*t ≤ y^2 := by
      have hh := sq_le_sq₀ (mul_nonneg hr.le (Real.sqrt_nonneg t)) (abs_nonneg y) |>.mpr hy
      simpa only [mul_pow, Real.sq_sqrt ht, sq_abs] using hh
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (∫ y in E, Real.exp (-c*y^2)) ≤
        ∫ y in E, Real.exp (-(c*r^2/2)*t) * Real.exp (-(c/2)*y^2) :=
      setIntegral_mono_on (integrable_exp_neg_mul_sq hc).integrableOn
        ((hi.const_mul _).integrableOn) hE hp
    _ = Real.exp (-(c*r^2/2)*t) * ∫ y in E, Real.exp (-(c/2)*y^2) :=
      integral_const_mul _ _
    _ ≤ Real.exp (-(c*r^2/2)*t) * ∫ y : ℝ, Real.exp (-(c/2)*y^2) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hi (ae_of_all _ (fun _ => (Real.exp_pos _).le)))
        (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- The difference estimate separates the amplitude error and phase error.
It requires no division by the limiting amplitude. -/
theorem damped_amplitude_difference_le {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] (z z₀ : K) (u v m A B : ℝ)
    (hu : m ≤ u) (hv : m ≤ v) (hA : ‖z-z₀‖ ≤ A) (hB : |u-v| ≤ B) :
    ‖Real.exp (-u) • z - Real.exp (-v) • z₀‖ ≤
      (A + ‖z₀‖ * B) * Real.exp (-m) := by
  have he : Real.exp (-u) ≤ Real.exp (-m) := Real.exp_le_exp.mpr (neg_le_neg hu)
  have hd := exp_neg_difference_le u v m hu hv
  have hid : Real.exp (-u) • z - Real.exp (-v) • z₀ =
      Real.exp (-u) • (z-z₀) + (Real.exp (-u)-Real.exp (-v)) • z₀ := by
    simp only [smul_sub, sub_smul]; abel
  rw [hid]
  calc
    _ ≤ ‖Real.exp (-u) • (z-z₀)‖ +
        ‖(Real.exp (-u)-Real.exp (-v)) • z₀‖ := norm_add_le _ _
    _ = Real.exp (-u) * ‖z-z₀‖ + |Real.exp (-u)-Real.exp (-v)| * ‖z₀‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-m) * A + (B * Real.exp (-m)) * ‖z₀‖ := by
      gcongr
      exact hd.trans (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le)
    _ = _ := by ring

/-- The local estimate before the substitution y = sqrt(t) h. -/
theorem local_error_le {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (q d h t c C L : ℝ) (z z₀ : K) (ht : 0 ≤ t)
    (hlow : c * h^2 ≤ q) (hd : c ≤ d/2)
    (hcub : |q - d*h^2/2| ≤ C * |h|^3)
    (hlip : ‖z-z₀‖ ≤ L * |h|) :
    ‖Real.exp (-t*q) • z - Real.exp (-d*(Real.sqrt t*h)^2/2) • z₀‖ ≤
      (L*|h| + ‖z₀‖*C*t*|h|^3) * Real.exp (-c*(Real.sqrt t*h)^2) := by
  have hs : (Real.sqrt t*h)^2 = t*h^2 := by rw [mul_pow, Real.sq_sqrt ht]
  have hB : |t*q - t*(d*h^2/2)| ≤ t*C*|h|^3 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg ht]
    nlinarith [mul_le_mul_of_nonneg_left hcub ht]
  have hh := damped_amplitude_difference_le z z₀ (t*q) (t*(d*h^2/2))
    (c*t*h^2) (L*|h|) (t*C*|h|^3)
    (by nlinarith [mul_le_mul_of_nonneg_left hlow ht])
    (by nlinarith [mul_le_mul_of_nonneg_right hd (mul_nonneg ht (sq_nonneg h))])
    hlip hB
  rw [hs]
  convert hh using 1 <;> congr 1 <;> ring

/-- The integrable scaled bound, with its explicit inverse-square-root factor. -/
theorem scaled_local_error_le {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (q d y t c C L : ℝ) (z z₀ : K) (ht : 0 < t)
    (hlow : c * (y/Real.sqrt t)^2 ≤ q) (hd : c ≤ d/2)
    (hcub : |q - d*(y/Real.sqrt t)^2/2| ≤ C * |y/Real.sqrt t|^3)
    (hlip : ‖z-z₀‖ ≤ L * |y/Real.sqrt t|) :
    ‖Real.exp (-t*q) • z - Real.exp (-d*y^2/2) • z₀‖ ≤
      (Real.sqrt t)⁻¹ * (L*|y| + ‖z₀‖*C*|y|^3) * Real.exp (-c*y^2) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hh := local_error_le q d (y/Real.sqrt t) t c C L z z₀ ht.le hlow hd hcub hlip
  have hy : Real.sqrt t * (y/Real.sqrt t) = y := by field_simp
  rw [hy] at hh
  convert hh using 1
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr ht)]
  have hsq := Real.sq_sqrt ht.le
  field_simp
  rw [hsq]
  ring

/-- The source assumptions imply a single integrable scaled local bound. -/
theorem local_control_aux {K : Type*} [RCLike K] :
  ∀ (φ : ℝ → ℝ) (g : ℝ → K) (a b x₀ : ℝ),
      ContDiffOn ℝ 2 φ (Icc a b) → ContinuousOn g (Icc a b) →
      x₀ ∈ Ioo a b →
      (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
      0 < deriv (deriv φ) x₀ →
      (∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ 3 φ U) →
      (∃ (U : Set ℝ) (L : NNReal), IsOpen U ∧ x₀ ∈ U ∧ LipschitzOnWith L g U) →
      ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ a < x₀-r ∧ x₀+r < b ∧
        Integrable (fun y : ℝ => (|y|+|y|^3) *
          Real.exp (-(deriv (deriv φ) x₀/4)*y^2)) ∧
        ∀ t : ℝ, 0 < t → ∀ y : ℝ, |y| ≤ r * Real.sqrt t →
          ‖Real.exp (-t*(φ (x₀+y/Real.sqrt t)-φ x₀)) • g (x₀+y/Real.sqrt t) -
            Real.exp (-deriv (deriv φ) x₀*y^2/2) • g x₀‖ ≤
          (Real.sqrt t)⁻¹ * A * (|y|+|y|^3) *
            Real.exp (-(deriv (deriv φ) x₀/4)*y^2)
 := by
  intro φ g a b x₀ hφ _hg hx hmin hd h3 hLip
  obtain ⟨r₀, hr₀, ha₀, hb₀, hlow⟩ :=
    LaplaceLocalization.localLower φ a b x₀ hφ hx hmin hd
  obtain ⟨r₁, C, hr₁, hC, _ha₁, _hb₁, hcub⟩ :=
    cubic_remainder φ a b x₀ hφ hx hmin h3
  obtain ⟨U, L, hU, hxU, hL⟩ := hLip
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let r := min r₀ (min r₁ (δ/2))
  let A := (L : ℝ) + ‖g x₀‖ * C
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ (half_pos hδ))
  have hr0 : r ≤ r₀ := min_le_left _ _
  have hr1 : r ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r < δ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hA : 0 ≤ A := add_nonneg L.coe_nonneg (mul_nonneg (norm_nonneg _) hC)
  refine ⟨r, A, hr, hA, by linarith, by linarith,
    gaussian_moment_integrable _ (div_pos hd (by norm_num)), ?_⟩
  intro t ht y hy
  have hs := Real.sqrt_pos.mpr ht
  have hh : |y/Real.sqrt t| ≤ r := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hy
  have hyU : x₀ + y/Real.sqrt t ∈ U := by
    apply hδU
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    exact hh.trans_lt hrδ
  have hlip : ‖g (x₀+y/Real.sqrt t) - g x₀‖ ≤ (L : ℝ)*|y/Real.sqrt t| := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left] using
      hL.dist_le_mul _ hyU _ hxU
  have he := scaled_local_error_le (φ (x₀+y/Real.sqrt t)-φ x₀)
    (deriv (deriv φ) x₀) y t (deriv (deriv φ) x₀/4) C (L : ℝ)
    (g (x₀+y/Real.sqrt t)) (g x₀) ht
    (hlow _ (hh.trans hr0)) (by linarith)
    (hcub _ (hh.trans hr1)) hlip
  refine he.trans ?_
  have hcoef : (L : ℝ)*|y| + ‖g x₀‖*C*|y|^3 ≤ A*(|y|+|y|^3) := by
    dsimp [A]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (g x₀)) hC) (abs_nonneg y),
      mul_nonneg L.coe_nonneg (pow_nonneg (abs_nonneg y) 3)]
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (inv_nonneg.mpr hs.le))
    (Real.exp_pos (-(deriv (deriv φ) x₀/4)*y^2)).le
  simpa only [mul_assoc] using this

theorem local_control : Specs.SingleVariableAnalysis.Ch17.LaplaceError.localControl := by
  intro k
  cases k with
  | real => exact @local_control_aux ℝ inferInstance
  | complex => exact @local_control_aux ℂ inferInstance

/-- Norm control from a Gaussian moment bound on any measurable subset.
The upper bound is the finite whole-line moment. -/
theorem gaussian_error_integral_le {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {f : ℝ → K} {E : Set ℝ} (hE : MeasurableSet E)
    {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hf : ∀ y ∈ E, ‖f y‖ ≤ B * ((|y|+|y|^3)*Real.exp (-c*y^2))) :
    ‖∫ y in E, f y‖ ≤ B * ∫ y : ℝ, (|y|+|y|^3)*Real.exp (-c*y^2) := by
  have hi := gaussian_moment_integrable c hc
  calc
    _ ≤ ∫ y in E, B * ((|y|+|y|^3)*Real.exp (-c*y^2)) :=
      norm_integral_le_of_norm_le ((hi.const_mul B).integrableOn)
        (by filter_upwards [ae_restrict_mem hE] with y hy; exact hf y hy)
    _ = B * ∫ y in E, (|y|+|y|^3)*Real.exp (-c*y^2) := integral_const_mul _ _
    _ ≤ B * ∫ y : ℝ, (|y|+|y|^3)*Real.exp (-c*y^2) :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hi
        (ae_of_all _ (fun y => by positivity))) hB

/-- Gaussian truncation error controlled by the omitted tail. -/
theorem gaussian_truncation_error (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    |(∫ y in -R..R, Real.exp (-c*y^2)) - Real.sqrt (Real.pi/c)| ≤
      ∫ y in {y : ℝ | R ≤ |y|}, Real.exp (-c*y^2) := by
  have hi := integrable_exp_neg_mul_sq hc
  have hab : -R ≤ R := by linarith
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have he := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hi
  rw [integral_gaussian c] at he
  have hnn : 0 ≤ ∫ y in (Icc (-R) R)ᶜ, Real.exp (-c*y^2) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have he' : (∫ y in Icc (-R) R, Real.exp (-c*y^2)) - Real.sqrt (Real.pi/c) =
      -(∫ y in (Icc (-R) R)ᶜ, Real.exp (-c*y^2)) := by linarith
  rw [he', abs_neg, abs_of_nonneg hnn]
  apply setIntegral_mono_set hi.integrableOn
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
  apply ae_of_all
  intro y hy
  by_contra h
  have hh : |y| < R := lt_of_not_ge h
  exact hy (abs_le.mp hh.le)

/-- Any positive exponential rate dominates the inverse square-root scale. -/
theorem exp_isBigO_inv_sqrt (η : ℝ) (hη : 0 < η) :
    IsBigO atTop (fun t : ℝ => Real.exp (-η*t)) (fun t : ℝ => (Real.sqrt t)⁻¹) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hη (-1/2)).isBigO
  apply h.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]
  congr 1
  ring

/-- The additional normalization factor sqrt(t) still leaves an error
smaller than the inverse square root. -/
theorem sqrt_exp_isBigO_inv_sqrt (η : ℝ) (hη : 0 < η) :
    IsBigO atTop (fun t : ℝ => Real.sqrt t * Real.exp (-η*t))
      (fun t : ℝ => (Real.sqrt t)⁻¹) := by
  have hl := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 η hη
  simp only [Real.rpow_one] at hl
  have hb := hl.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  apply IsBigO.of_bound 1
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with t ht hpos
  have hs := Real.sqrt_pos.mpr hpos
  simp only [Real.norm_eq_abs, abs_of_pos (mul_pos hs (Real.exp_pos _)),
    abs_of_pos (inv_pos.mpr hs), one_mul]
  apply (mul_le_mul_iff_right₀ hs).mp
  rw [mul_inv_cancel₀ hs.ne']
  have hsq := Real.sq_sqrt hpos.le
  nlinarith [Real.exp_pos (-η*t)]

/-- Integrating the pointwise error and restoring the omitted Gaussian
mass gives a bound for the entire local approximation. -/
theorem local_integral_bound {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [CompleteSpace K] (f : ℝ → K) (z : K)
    (R c e B : ℝ) (hR : 0 ≤ R) (hc : 0 < c) (he : 0 < e) (hB : 0 ≤ B)
    (hf : IntervalIntegrable f volume (-R) R)
    (hp : ∀ y ∈ Icc (-R) R,
      ‖f y - Real.exp (-c*y^2) • z‖ ≤ B * ((|y|+|y|^3)*Real.exp (-e*y^2))) :
    ‖(∫ y in -R..R, f y) - Real.sqrt (Real.pi/c) • z‖ ≤
      B * (∫ y : ℝ, (|y|+|y|^3)*Real.exp (-e*y^2)) +
      ‖z‖ * (∫ y in {y : ℝ | R ≤ |y|}, Real.exp (-c*y^2)) := by
  have hle : -R ≤ R := by linarith
  have hg : IntervalIntegrable (fun y : ℝ => Real.exp (-c*y^2) • z) volume (-R) R :=
    (show Continuous (fun y : ℝ => Real.exp (-c*y^2) • z) by fun_prop).intervalIntegrable _ _
  have hi := gaussian_error_integral_le (f := fun y => f y - Real.exp (-c*y^2) • z)
    measurableSet_Icc he hB hp
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_sub hf hg] at hi
  have htail := gaussian_truncation_error c R hc hR
  have hid : (∫ y in -R..R, f y) - Real.sqrt (Real.pi/c) • z =
      ((∫ y in -R..R, f y) - ∫ y in -R..R, Real.exp (-c*y^2) • z) +
      ((∫ y in -R..R, Real.exp (-c*y^2)) - Real.sqrt (Real.pi/c)) • z := by
    rw [intervalIntegral.integral_smul_const, sub_smul]
    abel
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add hi ?_)
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left htail (norm_nonneg z)

/-- The affine rescaling of the local proper integral. -/
theorem local_rescaling {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (f : ℝ → K) (x₀ r t : ℝ) (ht : 0 < t) :
    (∫ y in -(r*Real.sqrt t)..r*Real.sqrt t, f (x₀+y/Real.sqrt t)) =
      Real.sqrt t • ∫ x in x₀-r..x₀+r, f x := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsub := intervalIntegral.integral_comp_add_div (a := -(r*Real.sqrt t))
    (b := r*Real.sqrt t) f hs x₀
  have hl : x₀ + -(r*Real.sqrt t)/Real.sqrt t = x₀-r := by field_simp; ring
  have hr : x₀ + (r*Real.sqrt t)/Real.sqrt t = x₀+r := by field_simp
  rwa [hl, hr] at hsub

/-- Extracting the value of the phase at the minimum is an exact identity. -/
theorem center_phase {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (φ : ℝ → ℝ) (g : ℝ → K) (a b x₀ t : ℝ) :
    Real.exp (t*φ x₀) • (∫ x in a..b, Real.exp (-t*φ x) • g x) =
      ∫ x in a..b, Real.exp (-t*(φ x-φ x₀)) • g x := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- The local normalized integral has the source's quantitative rate. -/
theorem local_normalized_error {K : Type*} [RCLike K]
    (φ : ℝ → ℝ) (g : ℝ → K) (x₀ r d A : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hA : 0 ≤ A)
    (hφ : ContinuousOn φ (Icc (x₀-r) (x₀+r)))
    (hg : ContinuousOn g (Icc (x₀-r) (x₀+r)))
    (hp : ∀ t : ℝ, 0 < t → ∀ y : ℝ, |y| ≤ r*Real.sqrt t →
      ‖Real.exp (-t*(φ (x₀+y/Real.sqrt t)-φ x₀)) • g (x₀+y/Real.sqrt t) -
        Real.exp (-d*y^2/2) • g x₀‖ ≤
      (Real.sqrt t)⁻¹*A*(|y|+|y|^3)*Real.exp (-(d/4)*y^2)) :
    IsBigO atTop
      (fun t : ℝ => Real.sqrt t •
        (∫ x in x₀-r..x₀+r, Real.exp (-t*(φ x-φ x₀)) • g x) -
        Real.sqrt (2*Real.pi/d) • g x₀)
      (fun t : ℝ => (Real.sqrt t)⁻¹) := by
  have hd2 : 0 < d/2 := by positivity
  have hd4 : 0 < d/4 := by positivity
  obtain ⟨T, hT, htail⟩ := omitted_gaussian_tail (d/2) r hd2 hr
  let J := ∫ y : ℝ, (|y|+|y|^3)*Real.exp (-(d/4)*y^2)
  let η := ((d/2)*r^2/2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hub : IsBigO atTop
      (fun t : ℝ => (A*J)*(Real.sqrt t)⁻¹ + (‖g x₀‖*T)*Real.exp (-η*t))
      (fun t : ℝ => (Real.sqrt t)⁻¹) := by
    exact ((isBigO_refl (fun t : ℝ => (Real.sqrt t)⁻¹) atTop).const_mul_left (A*J)).add
      ((exp_isBigO_inv_sqrt η hη).const_mul_left (‖g x₀‖*T))
  refine (IsBigO.of_norm_eventuallyLE ?_).trans hub
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs := Real.sqrt_pos.mpr ht
  let R := r*Real.sqrt t
  have hR : 0 ≤ R := mul_nonneg hr.le hs.le
  have hle : -R ≤ R := by linarith
  have hmap : MapsTo (fun y : ℝ => x₀+y/Real.sqrt t) (Icc (-R) R)
      (Icc (x₀-r) (x₀+r)) := by
    intro y hy
    have hl : -r ≤ y/Real.sqrt t := by
      rw [le_div_iff₀ hs]
      dsimp [R] at hy
      linarith [hy.1]
    have hu : y/Real.sqrt t ≤ r := by
      rw [div_le_iff₀ hs]
      exact hy.2
    constructor <;> linarith
  have hmapc : Continuous (fun y : ℝ => x₀+y/Real.sqrt t) := by fun_prop
  have hfc : ContinuousOn
      (fun y : ℝ => Real.exp (-t*(φ (x₀+y/Real.sqrt t)-φ x₀)) •
        g (x₀+y/Real.sqrt t)) (Icc (-R) R) :=
    (((hφ.comp hmapc.continuousOn hmap).sub continuousOn_const).const_mul (-t)).rexp.smul
      (hg.comp hmapc.continuousOn hmap)
  have hfi : IntervalIntegrable
      (fun y : ℝ => Real.exp (-t*(φ (x₀+y/Real.sqrt t)-φ x₀)) •
        g (x₀+y/Real.sqrt t)) volume (-R) R := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hle] using hfc
  have he := local_integral_bound _ (g x₀) R (d/2) (d/4)
    ((Real.sqrt t)⁻¹*A) hR hd2 hd4 (mul_nonneg (inv_nonneg.mpr hs.le) hA) hfi
    (fun y hy => by
      have hpy := hp t ht y (abs_le.mpr hy)
      have hquad : -(d/2)*y^2 = -d*y^2/2 := by ring
      simpa only [hquad, mul_assoc] using hpy)
  have hconst : Real.pi/(d/2) = 2*Real.pi/d := by field_simp
  dsimp only [R] at he
  rw [hconst, local_rescaling (fun x => Real.exp (-t*(φ x-φ x₀)) • g x) x₀ r t ht] at he
  change ‖Real.sqrt t • _ - _‖ ≤ (Real.sqrt t)⁻¹*A*J + _ at he
  have he' := he.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (htail t ht.le) (norm_nonneg (g x₀))))
  simpa only [mul_assoc, mul_comm, mul_left_comm, J, η] using he'

/-- A compact exterior gap gives the quantitative normalized exterior rate. -/
theorem exterior_normalized_error {K : Type*} [RCLike K]
    (φ : ℝ → ℝ) (g : ℝ → K) (a b x₀ r : ℝ)
    (hφ : ContinuousOn φ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hx : x₀ ∈ Ioo a b) (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x)
    (hr : 0 < r) (hra : a < x₀-r) (hrb : x₀+r < b) :
    IsBigO atTop (fun t : ℝ => Real.sqrt t •
      ((∫ x in a..x₀-r, Real.exp (-t*(φ x-φ x₀)) • g x) +
       (∫ x in x₀+r..b, Real.exp (-t*(φ x-φ x₀)) • g x)))
      (fun t : ℝ => (Real.sqrt t)⁻¹) := by
  obtain ⟨η, hη, hgap⟩ := LaplaceLocalization.exteriorGap φ a b x₀ hφ hx hmin r hr
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := (norm_nonneg (g x₀)).trans (hM x₀ ⟨hx.1.le, hx.2.le⟩)
  refine (IsBigO.of_norm_eventuallyLE ?_).trans
    ((sqrt_exp_isBigO_inv_sqrt η hη).const_mul_left (M*(b-a)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hp (x : ℝ) (hxi : x ∈ Icc a b) (hxr : r ≤ |x-x₀|) :
      ‖Real.exp (-t*(φ x-φ x₀)) • g x‖ ≤ Real.exp (-η*t)*M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hM x hxi) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have := hgap x hxi hxr
    nlinarith
  have hL := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => Real.exp (-t*(φ x-φ x₀)) • g x)
    (a := a) (b := x₀-r) (C := Real.exp (-η*t)*M) (fun x hxL => by
      rw [uIoc_of_le hra.le] at hxL
      apply hp x ⟨hxL.1.le, by linarith [hxL.2]⟩
      rw [abs_of_nonpos (by linarith [hxL.2] : x-x₀ ≤ 0)]
      linarith [hxL.2])
  have hR := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => Real.exp (-t*(φ x-φ x₀)) • g x)
    (a := x₀+r) (b := b) (C := Real.exp (-η*t)*M) (fun x hxR => by
      rw [uIoc_of_le hrb.le] at hxR
      apply hp x ⟨by linarith [hxR.1], hxR.2⟩
      rw [abs_of_nonneg (by linarith [hxR.1] : 0 ≤ x-x₀)]
      linarith [hxR.1])
  rw [abs_of_nonneg (by linarith : 0 ≤ x₀-r-a)] at hL
  rw [abs_of_nonneg (by linarith : 0 ≤ b-(x₀+r))] at hR
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
  calc
    _ ≤ Real.sqrt t *
        (‖∫ x in a..x₀-r, Real.exp (-t*(φ x-φ x₀)) • g x‖ +
         ‖∫ x in x₀+r..b, Real.exp (-t*(φ x-φ x₀)) • g x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg t)
    _ ≤ Real.sqrt t * ((Real.exp (-η*t)*M)*(x₀-r-a) +
        (Real.exp (-η*t)*M)*(b-(x₀+r))) := by gcongr
    _ ≤ (M*(b-a)) * (Real.sqrt t * Real.exp (-η*t)) := by
      have hpos := mul_nonneg (Real.exp_pos (-η*t)).le hM0
      have hbound : (Real.exp (-η*t)*M)*(x₀-r-a) +
          (Real.exp (-η*t)*M)*(b-(x₀+r)) ≤ (Real.exp (-η*t)*M)*(b-a) := by
        nlinarith
      have hh := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg t)
      convert hh using 1 <;> ring

/-- Quantitative Laplace estimate for the interval integral. All integrands
are continuous on their proper integration intervals; the final theorem
below transfers this estimate to the manuscript's Darboux values. -/
theorem normalized_interval_error {K : Type*} [RCLike K]
    (φ : ℝ → ℝ) (g : ℝ → K) (a b x₀ : ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hx : x₀ ∈ Ioo a b) (hmin : ∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x)
    (hd : 0 < deriv (deriv φ) x₀)
    (h3 : ∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ 3 φ U)
    (hLip : ∃ (U : Set ℝ) (L : NNReal), IsOpen U ∧ x₀ ∈ U ∧ LipschitzOnWith L g U) :
    IsBigO atTop
      (fun t : ℝ => (Real.sqrt t * Real.exp (t*φ x₀)) •
        (∫ x in a..b, Real.exp (-t*φ x) • g x) -
        Real.sqrt (2*Real.pi/deriv (deriv φ) x₀) • g x₀)
      (fun t : ℝ => (Real.sqrt t)⁻¹) := by
  obtain ⟨r, A, hr, hA, hra, hrb, _hi, hp⟩ :=
    local_control_aux φ g a b x₀ hφ hg hx hmin hd h3 hLip
  have hsub : Icc (x₀-r) (x₀+r) ⊆ Icc a b := Icc_subset_Icc hra.le hrb.le
  have hlocal := local_normalized_error φ g x₀ r (deriv (deriv φ) x₀) A
    hr hd hA (hφ.continuousOn.mono hsub) (hg.mono hsub) hp
  have hext := exterior_normalized_error φ g a b x₀ r hφ.continuousOn hg hx hmin hr hra hrb
  have hsum := hlocal.add hext
  apply hsum.congr' _ EventuallyEq.rfl
  apply Eventually.of_forall
  intro t
  have hfc : ContinuousOn (fun x => Real.exp (-t*(φ x-φ x₀)) • g x) (Icc a b) :=
    ((hφ.continuousOn.sub continuousOn_const).const_mul (-t)).rexp.smul hg
  have hint (u v : ℝ) (hu : a ≤ u) (hv : v ≤ b) (huv : u ≤ v) :
      IntervalIntegrable (fun x => Real.exp (-t*(φ x-φ x₀)) • g x) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact hfc.mono (Icc_subset_Icc hu hv)
  have hL := hint a (x₀-r) le_rfl (by linarith) hra.le
  have hC := hint (x₀-r) (x₀+r) hra.le hrb.le (by linarith)
  have hR := hint (x₀+r) b (by linarith) le_rfl hrb.le
  have hCR := hint (x₀-r) b hra.le le_rfl (by linarith)
  have he1 := intervalIntegral.integral_add_adjacent_intervals hC hR
  have he2 := intervalIntegral.integral_add_adjacent_intervals hL hCR
  dsimp only
  rw [mul_smul, center_phase, ← he2, ← he1]
  simp only [smul_add]
  abel

/-- The continuous real proper Darboux value equals the interval value.
The proof uses a continuous extension and the proper Darboux FTC. -/
theorem real_continuous_integral_eq (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (h : Riemann.RealIntegrable f a b) :
    Riemann.realIntegral f h = ∫ x in a..b, f x := by
  obtain ⟨F, hF, hFe⟩ := Riemann.continuous_extension_from_Icc (E := ℝ) hab hf
  have hdF (y : ℝ) : HasDerivAt (fun z => ∫ x in a..z, F x) (F y) y :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
      hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hv := Riemann.real_ftc_second (fun z => ∫ x in a..z, F x) f a b hab
    (fun y _ => (hdF y).continuousAt.continuousWithinAt)
    (fun y hy => by rw [← hFe (Ioo_subset_Icc_self hy)]; exact hdF y) h
  have hv' : Riemann.realIntegral f h = ∫ x in a..b, F x := by
    simpa only [intervalIntegral.integral_same, sub_zero] using hv
  exact hv'.trans (intervalIntegral.integral_congr
    (by simpa only [uIcc_of_le hab] using hFe))

/-- The continuous complex proper Darboux value equals the interval value.
The proof uses a continuous extension and the proper Darboux FTC. -/
theorem complex_continuous_integral_eq (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (h : Riemann.ComplexIntegrable f a b) :
    Riemann.complexIntegral f h = ∫ x in a..b, f x := by
  obtain ⟨F, hF, hFe⟩ := Riemann.continuous_extension_from_Icc (E := ℂ) hab hf
  have hdF (y : ℝ) : HasDerivAt (fun z => ∫ x in a..z, F x) (F y) y :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
      hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hv := Riemann.complex_ftc_second (fun z => ∫ x in a..z, F x) f a b hab
    (fun y _ => (hdF y).continuousAt.continuousWithinAt)
    (fun y hy => by rw [← hFe (Ioo_subset_Icc_self hy)]; exact hdF y) h
  have hv' : Riemann.complexIntegral f h = ∫ x in a..b, F x := by
    simpa only [intervalIntegral.integral_same, sub_zero] using hv
  exact hv'.trans (intervalIntegral.integral_congr
    (by simpa only [uIcc_of_le hab] using hFe))

/-- K03.17.laplace_local, quantitative corollary. The error is additive,
so the result includes g(x₀) = 0. Integrability of every proper section is
proved, and no quantitative error estimate is assumed as a certificate. -/
theorem normalized_error : S.normalizedError := by
  intro k
  cases k with
  | real =>
    letI := Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.scalarRCLike .real
    intro φ g a b x₀ hφ hg hx hmin hd h3 hLip
    change ℝ → ℝ at g
    have hab : a ≤ b := (hx.1.trans hx.2).le
    have hfc (t : ℝ) : ContinuousOn (fun x => Real.exp (-t*φ x) • g x) (Icc a b) :=
      (hφ.continuousOn.const_mul (-t)).rexp.smul hg
    let hI := fun t => LaplaceLocalization.scalar_continuous_integrable .real
      (fun x => Real.exp (-t*φ x) • g x) a b hab (hfc t)
    refine ⟨hI, ?_⟩
    have h := normalized_interval_error φ g a b x₀ hφ hg hx hmin hd h3 hLip
    apply h.congr' _ EventuallyEq.rfl
    apply Eventually.of_forall
    intro t
    have hv := real_continuous_integral_eq _ a b hab (hfc t) (hI t)
    exact congrArg (fun v : ℝ => (Real.sqrt t * Real.exp (t*φ x₀)) • v -
      Real.sqrt (2*Real.pi/deriv (deriv φ) x₀) • g x₀) hv.symm
  | complex =>
    letI := Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.scalarRCLike .complex
    intro φ g a b x₀ hφ hg hx hmin hd h3 hLip
    change ℝ → ℂ at g
    have hab : a ≤ b := (hx.1.trans hx.2).le
    have hfc (t : ℝ) : ContinuousOn (fun x => Real.exp (-t*φ x) • g x) (Icc a b) :=
      (hφ.continuousOn.const_mul (-t)).rexp.smul hg
    let hI := fun t => LaplaceLocalization.scalar_continuous_integrable .complex
      (fun x => Real.exp (-t*φ x) • g x) a b hab (hfc t)
    refine ⟨hI, ?_⟩
    have h := normalized_interval_error φ g a b x₀ hφ hg hx hmin hd h3 hLip
    apply h.congr' _ EventuallyEq.rfl
    apply Eventually.of_forall
    intro t
    have hv := complex_continuous_integral_eq _ a b hab (hfc t) (hI t)
    exact congrArg (fun v : ℂ => (Real.sqrt t * Real.exp (t*φ x₀)) • v -
      Real.sqrt (2*Real.pi/deriv (deriv φ) x₀) • g x₀) hv.symm

end SingleVariableAnalysis.LaplaceError
