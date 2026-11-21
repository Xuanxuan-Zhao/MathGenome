import MathGenome.Internal.LinearPDE.P201Specs.Potential.BallGreen
import MathGenome.Internal.LinearPDE.P201.Potential.Fundamental
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 250000

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff RealInnerProductSpace Topology
namespace P201.BallGreen

abbrev imagePoint : P201Specs.BallGreen.ImagePointType := @P201Specs.BallGreen.imagePoint
abbrev symmetricPolynomial : P201Specs.BallGreen.SymmetricPolynomialType :=
  @P201Specs.BallGreen.symmetricPolynomial
abbrev kernel : P201Specs.BallGreen.KernelType := @P201Specs.BallGreen.kernel
abbrev pointDirac : P201Specs.BallGreen.PointDiracType := @P201Specs.BallGreen.pointDirac

@[simp] theorem symmetricPolynomial_comm {n : ℕ} (r : ℝ) (x y : Space n) :
    symmetricPolynomial r x y = symmetricPolynomial r y x := by
  simp only [symmetricPolynomial, P201Specs.BallGreen.symmetricPolynomial, real_inner_comm y x]
  ring

theorem translation : P201Specs.BallGreen.TranslationStatement := by
  intro n a r x y
  simp only [kernel, P201Specs.BallGreen.kernel, sub_zero]
  congr 1
  congr 1
  abel

theorem symmetry : P201Specs.BallGreen.SymmetryStatement := by
  intro n _ a r _ x y
  simp only [kernel, P201Specs.BallGreen.kernel, P201Specs.fundamentalKernel, norm_sub_rev y x, symmetricPolynomial_comm r (y-a) (x-a)]

theorem center : P201Specs.BallGreen.CenterStatement := by
  intro n _ a r hr y
  have hs : Real.sqrt (r ^ 4) = r ^ 2 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg r)]
  simp only [kernel, P201Specs.BallGreen.kernel, sub_self,
    P201Specs.BallGreen.symmetricPolynomial, inner_zero_left, mul_zero, norm_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero, add_zero, hs]
  rw [show r ^ 2 / r = r from by field_simp]

/-- Quantitative positivity of the symmetric polynomial on the closed ball. -/
theorem symmetricPolynomial_lower {n : ℕ} (r : ℝ) (_hr : 0 ≤ r) (x y : Space n) :
    (r ^ 2 - ‖x‖ * ‖y‖) ^ 2 ≤ symmetricPolynomial r x y := by
  have hi := real_inner_le_norm x y
  have hm := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hi)
  dsimp [symmetricPolynomial, P201Specs.BallGreen.symmetricPolynomial]
  nlinarith

theorem symmetricPolynomial_pos {n : ℕ} {a x y : Space n} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ ball a r) (hy : y ∈ closedBall a r) :
    0 < symmetricPolynomial r (x-a) (y-a) := by
  have hx' : ‖x-a‖ < r := by simpa [mem_ball, dist_eq_norm] using hx
  have hy' : ‖y-a‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hy
  have hp : ‖x-a‖ * ‖y-a‖ < r ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hy' (norm_nonneg (x-a))
    nlinarith
  exact lt_of_lt_of_le (sq_pos_of_pos (sub_pos.mpr hp))
    (symmetricPolynomial_lower r hr.le (x-a) (y-a))

/-- On the sphere, the correction has exactly the same radial argument as Phi. -/
theorem symmetricPolynomial_boundary {n : ℕ} (r : ℝ) (x ζ : Space n) (hζ : ‖ζ‖ = r) :
    symmetricPolynomial r x ζ = r ^ 2 * ‖ζ-x‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_comm x ζ]
  dsimp [symmetricPolynomial, P201Specs.BallGreen.symmetricPolynomial]
  rw [hζ]
  ring

theorem correction_radius_boundary {n : ℕ} {a ζ : Space n} {r : ℝ}
    (hr : 0 < r) (x : Space n) (hζ : ζ ∈ sphere a r) :
    Real.sqrt (symmetricPolynomial r (x-a) (ζ-a)) / r = ‖ζ-x‖ := by
  have hζ' : ‖ζ-a‖ = r := by simpa [mem_sphere, dist_eq_norm] using hζ
  rw [symmetricPolynomial_boundary r (x-a) (ζ-a) hζ']
  rw [show ζ-a-(x-a) = ζ-x by abel]
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg hr.le (norm_nonneg _))]
  field_simp

theorem boundary_zero : P201Specs.BallGreen.BoundaryZeroStatement := by
  intro n _ a r hr x _ ζ hζ
  change P201Specs.fundamentalKernel n (ζ-x) - P201Specs.fundamentalProfile n
    (Real.sqrt (symmetricPolynomial r (x-a) (ζ-a)) / r) = 0
  rw [correction_radius_boundary hr x hζ]
  exact sub_self _

/-- The common radial profile is smooth at every positive radius. -/
theorem profile_contDiffAt (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (P201Specs.fundamentalProfile n) t := by
  unfold P201Specs.fundamentalProfile
  split_ifs
  · exact contDiffAt_id.neg.div_const 2
  · exact contDiffAt_const.mul (contDiffAt_id.log ht)
  · exact (contDiffAt_id.rpow_const_of_ne ht).div_const _

/-- Smoothness of the symmetric polynomial on the entire product space. -/
theorem symmetricPolynomial_contDiff {n : ℕ} (a : Space n) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × Space n =>
      symmetricPolynomial r (p.1-a) (p.2-a)) := by
  exact contDiff_const.sub (contDiff_const.mul
    ((contDiff_fst.sub contDiff_const).inner ℝ (contDiff_snd.sub contDiff_const))) |>.add
      (((contDiff_fst.sub contDiff_const).norm_sq ℝ).mul
        ((contDiff_snd.sub contDiff_const).norm_sq ℝ))

theorem smooth : P201Specs.BallGreen.SmoothStatement := by
  intro n _ a r hr x hx y hy hne
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space n × Space n =>
    P201Specs.fundamentalProfile n ‖p.2-p.1‖ -
    P201Specs.fundamentalProfile n (Real.sqrt (symmetricPolynomial r (p.1-a) (p.2-a)) / r)) (x,y)
  have hq := symmetricPolynomial_pos hr hx hy
  have hrad : 0 < Real.sqrt (symmetricPolynomial r (x-a) (y-a)) / r :=
    div_pos (Real.sqrt_pos.mpr hq) hr
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space n × Space n =>
      Real.sqrt (symmetricPolynomial r (p.1-a) (p.2-a)) / r) (x,y) :=
    (((symmetricPolynomial_contDiff a r).contDiffAt (x := (x,y))).sqrt hq.ne').div_const r
  have hd : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : Space n × Space n => ‖p.2-p.1‖) (x,y) :=
    (contDiffAt_snd.sub contDiffAt_fst).norm ℝ (sub_ne_zero.mpr hne.symm)
  exact ((profile_contDiffAt n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm))).comp
    (x,y) hd).sub ((profile_contDiffAt n hrad.ne').comp (x,y) hc)

/-- The algebraic identity used in the source's inversion argument. -/
theorem imagePoint_polynomial {n : ℕ} (r : ℝ) {x : Space n} (hx : x ≠ 0)
    (y : Space n) : symmetricPolynomial r x y = ‖x‖ ^ 2 * ‖y-imagePoint r x‖ ^ 2 := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  dsimp [symmetricPolynomial, P201Specs.BallGreen.symmetricPolynomial,
    imagePoint, P201Specs.BallGreen.imagePoint]
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg r) (sq_nonneg ‖x‖)), real_inner_smul_right,
    real_inner_comm x y]
  field_simp
  <;> ring

theorem correction_radius_image {n : ℕ} {r : ℝ} (_hr : 0 < r)
    {x : Space n} (hx : x ≠ 0) (y : Space n) :
    Real.sqrt (symmetricPolynomial r x y) / r = ‖x‖ * ‖y-imagePoint r x‖ / r := by
  rw [imagePoint_polynomial r hx, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- Homogeneity of the radial profile with its exact dimensional constants. -/
theorem profile_scale {n : ℕ} (hn : 3 ≤ n) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    P201Specs.fundamentalProfile n (s*t) = (s ^ (n-2))⁻¹ * P201Specs.fundamentalProfile n t := by
  have hexp : 2 - (n : ℝ) = -((n-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    ring
  simp only [P201Specs.fundamentalProfile,
    ite_eq_right (by omega : n ≠ 1), ite_eq_right (by omega : n ≠ 2), hexp,
    Real.rpow_neg (mul_pos hs ht).le, Real.rpow_neg ht.le,
    Real.rpow_natCast, mul_pow, mul_inv_rev]
  ring

theorem image_formula_higher : P201Specs.BallGreen.ImageFormulaHigherStatement := by
  intro n hn r hr x y hx _ hy
  have hx' := norm_pos_iff.mpr hx
  have hy' := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  have he := profile_scale hn (div_pos hx' hr) hy'
  change P201Specs.fundamentalKernel n (y-x) - P201Specs.fundamentalProfile n
    (Real.sqrt (symmetricPolynomial r (x-0) (y-0)) / r) = _
  simp only [sub_zero, correction_radius_image hr hx]
  rw [show ‖x‖ * ‖y-imagePoint r x‖ / r = (‖x‖ / r) * ‖y-imagePoint r x‖ by ring]
  rw [he]
  congr 1
  rw [div_pow, inv_div, ← div_pow]
  rfl

theorem image_formula_two : P201Specs.BallGreen.ImageFormulaTwoStatement := by
  intro r hr x y hx hy hyi
  have hx' := (norm_pos_iff.mpr hx).ne'
  have hy' := (norm_pos_iff.mpr (sub_ne_zero.mpr hy)).ne'
  have hi' := (norm_pos_iff.mpr (sub_ne_zero.mpr hyi)).ne'
  change P201Specs.fundamentalProfile 2 ‖y-x‖ - P201Specs.fundamentalProfile 2
    (Real.sqrt (symmetricPolynomial r (x-0) (y-0)) / r) = _
  simp only [sub_zero, correction_radius_image hr hx,
    P201Specs.fundamentalProfile,
    show ¬ (2 : ℕ) = 1 by decide, ↓reduceIte]
  rw [Real.log_div (mul_ne_zero hx' hi') hr.ne', Real.log_mul hx' hi',
    Real.log_div (mul_ne_zero hx' hi') (mul_ne_zero hr.ne' hy'),
    Real.log_mul hx' hi', Real.log_mul hr.ne' hy']
  ring

/-- Derivative of the fundamental solution in a translated Euclidean chart. -/
theorem fundamental_hasFDerivAt {n : ℕ} (hn : 1 ≤ n) (p y : Space n) (hne : y ≠ p) :
    HasFDerivAt (fun z => P201Specs.fundamentalKernel n (z-p))
      ((-1 / (omega n * ‖y-p‖ ^ n)) • innerSL ℝ (y-p)) y := by
  have hnorm : ‖y-p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hd₀ := ((hasFDerivAt_id y).sub_const p).norm_sq.sqrt (pow_ne_zero 2 hnorm)
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at hd₀
  have hd := ((fundamentalFlux n hn ‖y-p‖ (lt_of_le_of_ne (norm_nonneg _) hnorm.symm)).1).comp_hasFDerivAt y hd₀
  convert! hd using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul, id_eq]
  rw [show ‖y-p‖ ^ n = ‖y-p‖ ^ (n-1) * ‖y-p‖ by
    rw [← pow_succ]; congr 1; omega]
  field_simp
  <;> ring

/-- First derivative of the polynomial in the second variable. -/
theorem symmetricPolynomial_hasFDerivAt {n : ℕ} (r : ℝ) (x y : Space n) :
    HasFDerivAt (symmetricPolynomial r x)
      ((-2*r^2) • innerSL ℝ x + (2*‖x‖^2) • innerSL ℝ y) y := by
  have hd := (hasFDerivAt_const (r^4) y).sub
    (((innerSL ℝ x).hasFDerivAt (x := y)).const_mul (2*r^2)) |>.add
      ((hasFDerivAt_id y).norm_sq.const_mul (‖x‖^2))
  convert! hd using 1
  ext v
  simp [symmetricPolynomial, P201Specs.BallGreen.symmetricPolynomial]
  <;> ring

/-- The gradient of the correction, evaluated on the actual outward normal. -/
theorem correction_normal {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    {x ζ : Space n} (hζ : ζ ∈ sphere (0 : Space n) r) (hne : ζ ≠ x) :
    fderiv ℝ (fun y => P201Specs.fundamentalProfile n (Real.sqrt (symmetricPolynomial r x y) / r))
      ζ (r⁻¹ • ζ) = -(‖x‖^2 - inner ℝ x ζ) / (r * omega n * ‖ζ-x‖^n) := by
  have hz : ‖ζ‖ = r := by simpa [mem_sphere, dist_zero_right] using hζ
  have hd : 0 < ‖ζ-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hq : symmetricPolynomial r x ζ = (r*‖ζ-x‖)^2 := by
    rw [symmetricPolynomial_boundary r x ζ hz, mul_pow]
  have hs : Real.sqrt (symmetricPolynomial r x ζ) = r*‖ζ-x‖ := by
    rw [hq, Real.sqrt_sq (mul_pos hr hd).le]
  have hrad : Real.sqrt (symmetricPolynomial r x ζ) / r = ‖ζ-x‖ := by
    rw [hs]; field_simp
  have hdq := ((symmetricPolynomial_hasFDerivAt r x ζ).sqrt
    (by rw [hq]; positivity)).mul_const r⁻¹
  simp only [← div_eq_mul_inv] at hdq
  have hdf := ((fundamentalFlux n hn (Real.sqrt (symmetricPolynomial r x ζ) / r)
    (by rwa [hrad])).1).comp_hasFDerivAt ζ hdq
  simp only [hrad] at hdf
  change (fderiv ℝ (P201Specs.fundamentalProfile n ∘
    (fun y => Real.sqrt (symmetricPolynomial r x y) / r)) ζ) (r⁻¹ • ζ) = _
  rw [hdf.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul, hs, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, hz, id_eq, nsmul_eq_mul]
  rw [show ‖ζ-x‖ ^ n = ‖ζ-x‖ ^ (n-1) * ‖ζ-x‖ by
    rw [← pow_succ]; congr 1; omega]
  field_simp
  <;> ring


theorem correction_contDiffAt {n : ℕ} {r : ℝ} (hr : 0 < r) (x y : Space n)
    (hq : 0 < symmetricPolynomial r x y) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z =>
      P201Specs.fundamentalProfile n (Real.sqrt (symmetricPolynomial r x z) / r)) y := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (symmetricPolynomial r x) := by
    simpa only [Function.comp_def, sub_zero, id_eq] using
      (symmetricPolynomial_contDiff (0 : Space n) r).comp (contDiff_const.prodMk contDiff_id)
  have hs := (hp.contDiffAt (x := y)).sqrt hq.ne' |>.div_const r
  exact (profile_contDiffAt n (div_pos (Real.sqrt_pos.mpr hq) hr).ne').comp y hs

theorem normal_derivative_zero {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    {x ζ : Space n} (hx : x ∈ ball 0 r) (hζ : ζ ∈ sphere 0 r) :
    -fderiv ℝ (kernel 0 r x) ζ (r⁻¹ • ζ) = BallPoisson.kernel 0 r x ζ := by
  have hne : ζ ≠ x := (BallPoisson.interior_ne_boundary hx hζ).symm
  have hd := fundamental_hasFDerivAt (by omega : 1 ≤ n) x ζ hne
  have hq : 0 < symmetricPolynomial r x ζ := by
    simpa only [sub_zero] using symmetricPolynomial_pos hr hx (sphere_subset_closedBall hζ)
  have hc := (correction_contDiffAt hr x ζ hq).differentiableAt (by simp)
  have hek : P201Specs.BallGreen.kernel 0 r x = (fun y =>
      P201Specs.fundamentalKernel n (y-x) -
      P201Specs.fundamentalProfile n (Real.sqrt (symmetricPolynomial r x y) / r)) := by
    funext y
    simp only [P201Specs.BallGreen.kernel, sub_zero]
  change -(fderiv ℝ (P201Specs.BallGreen.kernel 0 r x) ζ) (r⁻¹ • ζ) = _
  rw [hek]
  change -(fderiv ℝ (fun y => P201Specs.fundamentalKernel n (y-x) -
    P201Specs.fundamentalProfile n (Real.sqrt (symmetricPolynomial r x y) / r)) ζ)
      (r⁻¹ • ζ) = _
  have hdsub := hd.sub hc.hasFDerivAt
  change HasFDerivAt (fun y => P201Specs.fundamentalKernel n (y-x) -
    P201Specs.fundamentalProfile n (Real.sqrt (symmetricPolynomial r x y) / r)) _ ζ at hdsub
  rw [hdsub.fderiv, ContinuousLinearMap.sub_apply]
  rw [show (fderiv ℝ (fun y => P201Specs.fundamentalProfile n
      (Real.sqrt (symmetricPolynomial r x y) / r)) ζ) (r⁻¹ • ζ) = _ from
    correction_normal (by omega : 1 ≤ n) hr hζ hne]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, inner_smul_right,
    smul_eq_mul, inner_sub_left, real_inner_self_eq_norm_sq]
  have hz : ‖ζ‖ = r := by simpa [mem_sphere, dist_zero_right] using hζ
  simp only [BallPoisson.kernel, P201Specs.BallPoisson.kernel, sub_zero,
    norm_sub_rev x ζ, hz]
  field_simp
  <;> ring

theorem normal_derivative : P201Specs.BallGreen.NormalDerivativeStatement := by
  intro n hn a r hr x hx ζ hζ
  have hx' : x-a ∈ ball (0 : Space n) r := by simpa [mem_ball, dist_eq_norm] using hx
  have hz' : ζ-a ∈ sphere (0 : Space n) r := by simpa [mem_sphere, dist_eq_norm] using hζ
  have hne : x-a ≠ ζ-a := by
    intro he
    apply BallPoisson.interior_ne_boundary hx hζ
    simpa only [sub_add_cancel] using congrArg (fun t => t+a) he
  have hj := smooth hn (0 : Space n) r hr (x-a) hx' (ζ-a)
    (sphere_subset_closedBall hz') hne
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (P201Specs.BallGreen.kernel 0 r (x-a)) (ζ-a) :=
    hj.comp (ζ-a) (contDiffAt_const.prodMk contDiffAt_id)
  have he : P201Specs.BallGreen.kernel a r x = P201Specs.BallGreen.kernel 0 r (x-a) ∘ (fun y => y-a) := by
    funext y; exact translation a r x y
  have hsub : DifferentiableAt ℝ (fun y : Space n => y-a) ζ :=
    ((hasFDerivAt_id ζ).sub_const a).differentiableAt
  rw [he, fderiv_comp ζ (hc.differentiableAt (by simp)) hsub]
  have hsder : fderiv ℝ (fun y : Space n => y-a) ζ = ContinuousLinearMap.id ℝ (Space n) :=
    ((hasFDerivAt_id ζ).sub_const a).fderiv
  rw [hsder, ContinuousLinearMap.comp_id]
  rw [normal_derivative_zero hn hr hx' hz']
  simp only [BallPoisson.kernel, P201Specs.BallPoisson.kernel, sub_zero,
    show x-a-(ζ-a) = x-ζ by abel]

/-- Fundamental solutions are smooth on the complement of the pole. -/
theorem fundamental_contDiffAt {n : ℕ} (p y : Space n) (hne : y ≠ p) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => P201Specs.fundamentalKernel n (z-p)) y := by
  exact (profile_contDiffAt n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))).comp y
    ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hne))

/-- Second directional derivative of the fundamental solution. -/
theorem fundamental_second_fderiv {n : ℕ} (hn : 1 ≤ n) (p y : Space n)
    (hne : y ≠ p) (v : Space n) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => P201Specs.fundamentalKernel n (w-p)) z v) y v =
      (omega n)⁻¹ * ((n : ℝ) * (inner ℝ (y-p) v)^2 * (‖y-p‖^(n+2))⁻¹ -
        ‖v‖^2 * (‖y-p‖^n)⁻¹) := by
  have hi := ((hasFDerivAt_id y).sub_const p).inner ℝ (hasFDerivAt_const v y)
  have hd := (hi.mul (BallPoisson.norm_inv_pow_hasFDerivAt p y n hne)).const_mul (-(omega n)⁻¹)
  have he : (fun z => fderiv ℝ (fun w => P201Specs.fundamentalKernel n (w-p)) z v) =ᶠ[𝓝 y]
      (fun z => -(omega n)⁻¹ * (inner ℝ (z-p) v * (‖z-p‖^n)⁻¹)) := by
    filter_upwards [eventually_ne_nhds hne] with z hz
    rw [(fundamental_hasFDerivAt hn p z hz).fderiv]
    simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
    <;> ring
  simp only [Pi.mul_apply, id_eq] at hd
  rw [he.fderiv_eq, hd.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left, real_inner_self_eq_norm_sq]
  <;> ring

/-- The canonical coordinate Laplacian vanishes away from the pole. -/
theorem fundamental_laplacian_zero {n : ℕ} (hn : 1 ≤ n) (p y : Space n) (hne : y ≠ p) :
    laplacian (fun z => P201Specs.fundamentalKernel n (z-p)) y = 0 := by
  let f := fun z => P201Specs.fundamentalKernel n (z-p)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hc : ContDiffAt ℝ 2 f y := (fundamental_contDiffAt p y hne).of_le (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hiter (v : Space n) : iteratedFDeriv ℝ 2 f y ![v,v] =
      fderiv ℝ (fun z => fderiv ℝ f z v) y v := by
    rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have hsq (u : Space n) : (∑ i : Fin n, (inner ℝ u (b i))^2) = ‖u‖^2 := by
    simpa only [pow_two, real_inner_comm, real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner u u
  change P201Specs.laplacian f y = 0
  rw [MeanValues.laplacian_bridge f y hc,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp_rw [hiter]
  dsimp only [f]
  simp_rw [fundamental_second_fderiv hn p y hne]
  simp only [b.orthonormal.norm_eq_one, one_pow, mul_one,
    ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hsq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : ‖y-p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  simp only [pow_add]
  field_simp
  <;> ring


theorem fundamental_harmonicAt {n : ℕ} (hn : 1 ≤ n) (p y : Space n) (hne : y ≠ p) :
    InnerProductSpace.HarmonicAt (fun z => P201Specs.fundamentalKernel n (z-p)) y := by
  refine ⟨(fundamental_contDiffAt p y hne).of_le (by simp), ?_⟩
  filter_upwards [eventually_ne_nhds hne] with z hz
  change Laplacian.laplacian (fun z => P201Specs.fundamentalKernel n (z-p)) z = 0
  rw [← MeanValues.laplacian_bridge _ _ ((fundamental_contDiffAt p z hz).of_le (by simp))]
  exact fundamental_laplacian_zero hn p z hz

/-- Homogeneity, with the additive logarithmic constant retained in dimension two. -/
theorem profile_scale_all {n : ℕ} (hn : 2 ≤ n) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    P201Specs.fundamentalProfile n (s*t) =
      (s ^ (n-2))⁻¹ * P201Specs.fundamentalProfile n t +
      if n = 2 then -(1 / (2*Real.pi)) * Real.log s else 0 := by
  by_cases h2 : n = 2
  · subst n
    simp only [P201Specs.fundamentalProfile, show ¬ (2 : ℕ) = 1 by decide,
      ↓reduceIte, Nat.sub_self, pow_zero, inv_one, one_mul,
      Real.log_mul hs.ne' ht.ne']
    ring
  · simpa only [ite_eq_right h2, add_zero] using profile_scale (by omega) hs ht

/-- The inversion point is strictly outside the ball for every noncentral pole. -/
theorem imagePoint_outside {n : ℕ} {r : ℝ} (hr : 0 < r) {x : Space n}
    (hx : ‖x‖ < r) (hne : x ≠ 0) : r < ‖imagePoint r x‖ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hne
  simp only [imagePoint, P201Specs.BallGreen.imagePoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (sq_pos_of_pos hr) (sq_pos_of_pos hx0))]
  rw [show r^2 / ‖x‖^2 * ‖x‖ = r^2 / ‖x‖ by field_simp]
  exact (lt_div_iff₀ hx0).mpr (by nlinarith)

theorem correction_harmonic : P201Specs.BallGreen.CorrectionHarmonicStatement := by
  intro n hn a r hr x hx
  apply (MeanValues.harmonic_bridge _ _).mpr
  by_cases hx0 : x-a = 0
  · have he : (fun y : Space n => P201Specs.fundamentalProfile n
        (Real.sqrt (symmetricPolynomial r (x-a) (y-a)) / r)) =
        (fun _ => P201Specs.fundamentalProfile n r) := by
      funext y
      have hs : Real.sqrt (r^4) / r = r := by
        rw [show r^4 = (r^2)^2 by ring, Real.sqrt_sq (sq_nonneg r)]
        field_simp
      simp only [hx0, symmetricPolynomial, P201Specs.BallGreen.symmetricPolynomial,
        inner_zero_left, mul_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        zero_mul, sub_zero, add_zero, hs]
    rw [he]
    exact InnerProductSpace.harmonicOnNhd_const _
  · have hxnorm : ‖x-a‖ < r := by simpa [mem_ball, dist_eq_norm] using hx
    have himage := imagePoint_outside hr hxnorm hx0
    let p := a + imagePoint r (x-a)
    have hp (y : Space n) (hy : y ∈ ball a r) : y ≠ p := by
      intro he
      have hy' : ‖y-a‖ < r := by simpa [mem_ball, dist_eq_norm] using hy
      rw [he, show p-a = imagePoint r (x-a) by dsimp [p]; abel] at hy'
      linarith
    intro y hy
    have he : (fun z => P201Specs.fundamentalProfile n
          (Real.sqrt (symmetricPolynomial r (x-a) (z-a)) / r)) =ᶠ[𝓝 y]
        (fun z => ( (‖x-a‖/r) ^ (n-2))⁻¹ * P201Specs.fundamentalKernel n (z-p) +
          if n = 2 then -(1/(2*Real.pi))*Real.log (‖x-a‖/r) else 0) := by
      filter_upwards [eventually_ne_nhds (hp y hy)] with z hz
      rw [correction_radius_image hr hx0]
      rw [show z-a-imagePoint r (x-a) = z-p by dsimp [p]; abel]
      rw [show ‖x-a‖ * ‖z-p‖ / r = (‖x-a‖ / r) * ‖z-p‖ by ring]
      exact profile_scale_all hn (div_pos (norm_pos_iff.mpr hx0) hr)
        (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
    apply (InnerProductSpace.harmonicAt_congr_nhds he).mpr
    exact ((fundamental_harmonicAt (by omega) p y (hp y hy)).const_smul
      (c := (((‖x-a‖/r) ^ (n-2))⁻¹))).add (InnerProductSpace.harmonicAt_const _)


/-- Translating the pole preserves the genuine local integrability. -/
theorem fundamental_translate_locallyIntegrable {n : ℕ} (hn : 1 ≤ n) (p : Space n) :
    LocallyIntegrable (fun y => P201Specs.fundamentalKernel n (y-p)) volume := by
  have h := fundamentalLocalIntegrability n hn
  have hm : Measure.map (Homeomorph.addRight (-p)) volume = volume :=
    (measurePreserving_add_right volume (-p)).map_eq
  rw [← hm] at h
  change LocallyIntegrable (P201Specs.fundamentalKernel n ∘ Homeomorph.addRight (-p)) volume
  exact (locallyIntegrable_map_homeomorph (Homeomorph.addRight (-p))).mp h

/-- An actual translated global test; no translated distribution is postulated. -/
def translatedTest {n : ℕ} {Ω : Domain n} (p : Space n) (φ : Test ℝ Ω) :
    Test ℝ (⊤ : Domain n) :=
  ⟨fun y => φ (y+p), φ.contDiff.comp (contDiff_id.add contDiff_const),
    φ.hasCompactSupport.comp_isClosedEmbedding (Homeomorph.addRight p).isClosedEmbedding,
    subset_univ _⟩

theorem translatedTest_partial {n : ℕ} {Ω : Domain n} (p : Space n) (φ : Test ℝ Ω)
    (w : List (Fin n)) :
    P102.U4.partialWord (translatedTest p φ) w =
      fun y => P102.U4.partialWord φ w (y+p) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext y
    simp only [P102.U4.partialWord, ih]
    have hd : DifferentiableAt ℝ (fun y : Space n => y+p) y :=
      ((hasFDerivAt_id y).add_const p).differentiableAt
    change (fderiv ℝ (P102.U4.partialWord φ w ∘ (fun y => y+p)) y)
      (P102.U4.coordinateVector n i) = _
    rw [fderiv_comp y (P102.U4.partialWord_contDiff φ.contDiff w |>.differentiable (by simp) _) hd]
    have hadd : fderiv ℝ (fun z : Space n => z+p) y = ContinuousLinearMap.id ℝ (Space n) :=
      ((hasFDerivAt_id y).add_const p).fderiv
    rw [hadd, ContinuousLinearMap.comp_id]

theorem translatedTest_laplacian {n : ℕ} {Ω : Domain n} (p : Space n) (φ : Test ℝ Ω)
    (y : Space n) : laplacian (translatedTest p φ) y = laplacian φ (y+p) := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (translatedTest_partial p φ _) y

/-- The fundamental solution pairing at an arbitrary pole. -/
theorem fundamental_translate_pairing {n : ℕ} (hn : 1 ≤ n) {Ω : Domain n}
    (p : Space n) (φ : Test ℝ Ω) :
    (∫ y, P201Specs.fundamentalKernel n (y-p) * laplacian φ y) = -φ p := by
  have h := fundamental_pairing hn (translatedTest p φ)
  simp_rw [translatedTest_laplacian] at h
  have ht := integral_add_right_eq_self (μ := volume)
    (fun y => P201Specs.fundamentalKernel n (y-p) * laplacian φ y) p
  simp only [add_sub_cancel_right] at ht
  change (∫ u, P201Specs.fundamentalKernel n u * laplacian φ (u+p)) = -φ (0+p) at h
  simp only [zero_add] at h
  exact ht.symm.trans h

/-- Canonical second distribution derivatives really pair with the test Laplacian. -/
theorem distributionLaplacian_pairing {n : ℕ} (Ω : Domain n) (u : Space n → ℝ)
    (hu : LocallyIntegrableOn u Ω volume) (φ : Test ℝ Ω) :
    distributionLaplacian (regularDistribution Ω u) φ = ∫ y, u y * laplacian φ y := by
  have he (i : Fin n) : distributionDerivative ({i,i} : MultiIndex n)
      (regularDistribution Ω u) φ =
      ∫ y, u y * P201Specs.multiPartial φ ({i,i} : MultiIndex n) y := by
    simp [P201Specs.distributionDerivative, P102.U4.distributionPartial,
      P201Specs.regularDistribution, P102.U4.regularDistribution,
      TestFunction.integralAgainstBilinCLM_eq_integral hu,
      P102.U4.testPartialWord_coe, P201Specs.multiPartial, P102.U4.multiPartial,
      Multiset.sort_cons, mul_comm]
  have hi (i : Fin n) : Integrable
      (fun y => u y * P201Specs.multiPartial φ ({i,i} : MultiIndex n) y) volume := by
    have h := (P102.U4.testPartialWord Ω [i,i] φ).integrable_bilin
      (ContinuousLinearMap.mul ℝ ℝ) hu
    simpa [ContinuousLinearMap.mul_apply', P102.U4.testPartialWord_coe,
      P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_cons, mul_comm] using h
  change (∑ i : Fin n, distributionDerivative ({i,i} : MultiIndex n)
    (regularDistribution Ω u)) φ = _
  simp only [sum_apply, he]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [P201Specs.laplacian, Finset.mul_sum]


def testLaplacian {n : ℕ} {Ω : Domain n} (φ : Test ℝ Ω) : Test ℝ Ω :=
  ∑ i : Fin n, P102.U4.testPartialWord Ω [i,i] φ

theorem testLaplacian_apply {n : ℕ} {Ω : Domain n} (φ : Test ℝ Ω) (y : Space n) :
    testLaplacian φ y = P201Specs.laplacian φ y := by
  simp [testLaplacian, P201Specs.laplacian, P201Specs.multiPartial, P102.U4.multiPartial,
    P102.U4.testPartialWord_coe, Multiset.sort_cons]

theorem test_laplacian_integrable {n : ℕ} (Ω : Domain n) (u : Space n → ℝ)
    (hu : LocallyIntegrableOn u Ω volume) (φ : Test ℝ Ω) :
    Integrable (fun y => u y * P201Specs.laplacian φ y) volume := by
  simpa only [ContinuousLinearMap.mul_apply', testLaplacian_apply, mul_comm] using
    (testLaplacian φ).integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu

/-- A C² harmonic function has zero pairing with every test Laplacian.
No behavior of its ambient representative outside the open domain is assumed. -/
theorem harmonic_pairing_zero {n : ℕ} (Ω : Domain n) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) (φ : Test ℝ Ω) :
    (∫ y, u y * P201Specs.laplacian φ y) = 0 := by
  have hul : LocallyIntegrableOn u Ω volume :=
    hu.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hc (i : Fin n) : ContDiffOn ℝ 0 (P201Specs.multiPartial u ({i,i} : MultiIndex n)) Ω := by
    simpa [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_cons] using
      P102.U4.partialWord_contDiffOn Ω hu.1 [i,i] 0 (by simp)
  have hi (i : Fin n) : Integrable (fun y =>
      P201Specs.multiPartial u ({i,i} : MultiIndex n) y * φ y) volume := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        ((hc i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
  have he (i : Fin n) : distributionDerivative ({i,i} : MultiIndex n)
      (regularDistribution Ω u) φ =
      ∫ y, P201Specs.multiPartial u ({i,i} : MultiIndex n) y * φ y := by
    have hd := P102.U4.derivative_classicalCompatibility n ℝ Ω ({i,i} : MultiIndex n) u
      (by simpa using hu.1)
    change P102.U4.distributionPartial ({i,i} : MultiIndex n) (P102.U4.regularDistribution Ω u) φ = _
    rw [hd]
    simp only [P102.U4.regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral
      ((hc i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet),
      ContinuousLinearMap.mul_apply', mul_comm]
  rw [← distributionLaplacian_pairing Ω u hul φ]
  change (∑ i : Fin n, distributionDerivative ({i,i} : MultiIndex n) (regularDistribution Ω u)) φ = 0
  simp only [sum_apply, he]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  rw [← Finset.sum_mul]
  change P201Specs.laplacian u y * φ y = 0
  by_cases hy : y ∈ Ω
  · rw [hu.2 y hy, zero_mul]
  · simp only [φ.zero_on_compl hy, Pi.zero_apply, mul_zero]

/-- The Dirichlet Green kernel has the correctly signed point source. -/
theorem distribution : P201Specs.BallGreen.DistributionStatement := by
  intro n hn a r hr x hx
  let Ω : Domain n := ⟨ball a r, isOpen_ball⟩
  let c : Space n → ℝ := fun y => P201Specs.fundamentalProfile n
    (Real.sqrt (symmetricPolynomial r (x-a) (y-a)) / r)
  have hc : P201Specs.MeanValues.IsHarmonic Ω c := correction_harmonic hn a r hr x hx
  have hcl : LocallyIntegrableOn c Ω volume :=
    hc.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hfl := (fundamental_translate_locallyIntegrable (by omega : 1 ≤ n) x).locallyIntegrableOn (Ω : Set (Space n))
  have hgl : LocallyIntegrableOn (P201Specs.BallGreen.kernel a r x) Ω volume := hfl.sub hcl
  refine ⟨hgl, ?_⟩
  ext φ
  change -distributionLaplacian (regularDistribution Ω (P201Specs.BallGreen.kernel a r x)) φ = φ x
  rw [distributionLaplacian_pairing Ω _ hgl]
  have hi := test_laplacian_integrable Ω _ hfl φ
  have hj := test_laplacian_integrable Ω _ hcl φ
  have he : (fun y => P201Specs.BallGreen.kernel a r x y * laplacian φ y) =
      (fun y => P201Specs.fundamentalKernel n (y-x) * laplacian φ y -
        c y * laplacian φ y) := by
    funext y; exact sub_mul _ _ _
  rw [he, integral_sub hi hj, fundamental_translate_pairing (by omega) x φ,
    harmonic_pairing_zero Ω c hc φ]
  ring


end P201.BallGreen
