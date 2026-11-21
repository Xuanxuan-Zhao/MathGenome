import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Poisson

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal NNReal Topology
namespace ExpandedFA.PartIV.HardyDisk
open HardyDiskSpec

abbrev H2 := HardyDiskSpec.H2
abbrev Circle := HardyDiskSpec.Circle
abbrev BoundaryL2 := HardyDiskSpec.BoundaryL2
abbrev disk := HardyDiskSpec.disk
abbrev Disk := HardyDiskSpec.Disk
abbrev infinityNorm := HardyDiskSpec.infinityNorm
abbrev HInfinity := HardyDiskSpec.HInfinity
abbrev eval := HardyDiskSpec.eval
abbrev boundary := HardyDiskSpec.boundary
abbrev shift := HardyDiskSpec.shift
abbrev IsInner := HardyDiskSpec.IsInner
abbrev IsOuter := HardyDiskSpec.IsOuter
abbrev nonnegativeFourier := HardyDiskSpec.nonnegativeFourier
abbrev poissonExtension := HardyDiskSpec.poissonExtension

theorem coefficient_norm : CoefficientNorm := by
  intro f
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) f

theorem boundary_series : BoundarySeries := by
  intro f
  exact modes_orthonormal.orthogonalFamily.hasSum_linearIsometry f

/-- Continuous Fourier coefficient functional on the a.e. quotient. -/
def fourierCoordinate (k : ℤ) : BoundaryL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).comp
    fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem fourierCoordinate_apply (k : ℤ) (g : BoundaryL2) :
    fourierCoordinate k g = fourierCoeff g k := fourierBasis_repr g k

@[simp] theorem fourierCoordinate_mode (k : ℤ) (n : ℕ) :
    fourierCoordinate k (fourierLp (T := 2 * π) 2 (n : ℤ)) =
      if k = (n : ℤ) then 1 else 0 := by
  rw [fourierCoordinate_apply,
    fourierCoeff_congr_ae (coeFn_fourierLp (T := 2 * π) 2 (n : ℤ)),
    fourierCoeff_fourier]
  simp [Pi.single_apply]

theorem boundary_coefficients : BoundaryCoefficients := by
  intro f k
  have h := (fourierCoordinate k).hasSum (boundary_series f)
  simp only [map_smul, fourierCoordinate_mode] at h
  rw [fourierCoordinate_apply] at h
  by_cases hk : 0 ≤ k
  · have heq : (fun n : ℕ => f n • (if k = (n : ℤ) then (1 : ℂ) else 0)) =
        (fun n : ℕ => if n = k.toNat then f k.toNat else 0) := by
      funext n
      by_cases hn : n = k.toNat
      · subst n; simp [Int.toNat_of_nonneg hk]
      · have hkn : k ≠ (n : ℤ) := by omega
        simp [hkn, hn]
    rw [heq] at h
    simpa only [ite_eq_left hk] using h.unique (hasSum_ite_eq k.toNat (f k.toNat))
  · have heq : (fun n : ℕ => f n • (if k = (n : ℤ) then (1 : ℂ) else 0)) = 0 := by
      funext n
      have hkn : k ≠ (n : ℤ) := by omega
      simp [hkn]
    rw [heq] at h
    simpa only [ite_eq_right hk] using h.unique hasSum_zero

theorem boundary_closed : BoundaryClosed := by
  have heq : (nonnegativeFourier : Set BoundaryL2) =
      ⋂ k : ℤ, ⋂ (_ : k < 0), {g | fourierCoordinate k g = 0} := by
    ext g
    simp [HardyDiskSpec.nonnegativeFourier]
  change IsClosed (nonnegativeFourier : Set BoundaryL2)
  rw [heq]
  exact isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_eq (fourierCoordinate k).continuous continuous_const

/-- Recover the one-sided sequence from the actual circle Fourier coefficients. -/
def coefficients (g : BoundaryL2) : H2 :=
  ⟨fun n => fourierCoeff g (n : ℤ), by
    apply memℓp_gen
    have h := (lp.memℓp (fourierBasis.repr g)).summable (by simp)
    simpa only [Function.comp_def, fourierBasis_repr] using
      h.comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ)) by
        intro i j hij; change (i : ℤ) = (j : ℤ) at hij; omega)⟩

theorem boundary_range : BoundaryRange := by
  apply le_antisymm
  · rintro g ⟨f, rfl⟩ k hk
    change fourierCoeff (HardyDiskSpec.boundary f) k = 0
    rw [boundary_coefficients]
    simp [show ¬ 0 ≤ k by omega]
  · intro g hg
    refine ⟨coefficients g, ?_⟩
    apply fourierBasis.repr.injective
    apply lp.ext
    funext k
    change fourierBasis.repr (HardyDiskSpec.boundary (coefficients g)) k = fourierBasis.repr g k
    rw [fourierBasis_repr, fourierBasis_repr, boundary_coefficients]
    by_cases hk : 0 ≤ k
    · simp [hk, coefficients, Int.toNat_of_nonneg hk]
    · simp [hk, hg k (by omega)]

/-- Actual isometry onto the circle Hardy subspace, for transporting Toeplitz operators. -/
def boundaryEquiv : H2 ≃ₗᵢ[ℂ] nonnegativeFourier :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := boundary.toLinearMap.codRestrict nonnegativeFourier (by
        intro f
        change HardyDiskSpec.boundary f ∈ HardyDiskSpec.nonnegativeFourier
        rw [← boundary_range]
        exact ⟨f, rfl⟩)
      norm_map' := fun f => boundary.norm_map f }
    (by
      intro g
      obtain ⟨f, hf⟩ := (show g.val ∈ LinearMap.range boundary.toLinearMap by
        change g.val ∈ LinearMap.range HardyDiskSpec.boundary.toLinearMap
        rw [boundary_range]; exact g.property)
      exact ⟨f, Subtype.ext hf⟩)

theorem boundary_unitary : BoundaryUnitary := ⟨boundaryEquiv, fun _ => rfl⟩

/-- The scalar formal series with the canonical Hardy coefficients. -/
def taylorSeries (f : H2) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ f

theorem taylorSeries_sum (f : H2) : (taylorSeries f).sum = eval f := by
  funext z
  exact FormalMultilinearSeries.ofScalars_sum_eq (f : ℕ → ℂ) z

theorem one_le_taylorRadius (f : H2) : (1 : ℝ≥0∞) ≤ (taylorSeries f).radius := by
  simpa only [ENNReal.coe_one] using
    (taylorSeries f).le_radius_of_bound ‖f‖ (r := (1 : ℝ≥0)) (by
      intro n
      simpa [taylorSeries, FormalMultilinearSeries.ofScalars_norm] using
        lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f n)

theorem unit_eball : Metric.eball (0 : ℂ) (1 : ℝ≥0∞) = disk := by
  rw [← ENNReal.coe_one, Metric.eball_coe]
  rfl

theorem taylor_hasSeries (f : H2) :
    HasFPowerSeriesOnBall (eval f) (taylorSeries f) 0 1 := by
  rw [← taylorSeries_sum]
  exact ((taylorSeries f).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) (one_le_taylorRadius f))).mono
    (by norm_num) (one_le_taylorRadius f)

theorem analytic_evaluation : AnalyticEvaluation := by
  intro f
  simpa only [unit_eball] using (taylor_hasSeries f).analyticOnNhd

theorem evaluation_hasSum : EvaluationHasSum := by
  intro f z hz
  have h := (taylor_hasSeries f).hasSum (by rwa [unit_eball])
  simpa [taylorSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using h

/-- The ℓ² geometric sequence used in point evaluation. -/
def geometricSequence (z : Disk) : H2 :=
  ⟨fun n => z.val ^ n, by
    apply memℓp_gen
    have hz : ‖z.val‖ < 1 := by
      simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using z.property
    have hs := summable_geometric_of_lt_one (sq_nonneg ‖z.val‖)
      (show ‖z.val‖ ^ 2 < 1 by nlinarith [norm_nonneg z.val])
    simpa [norm_pow, ← pow_mul, ENNReal.toReal_ofNat, Real.rpow_two,
      Nat.mul_comm] using hs⟩

theorem geometricSequence_norm (z : Disk) :
    ‖geometricSequence z‖ = (Real.sqrt (1 - ‖z.val‖ ^ 2))⁻¹ := by
  have hz : ‖z.val‖ < 1 := by
    simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using z.property
  have hz2 : ‖z.val‖ ^ 2 < 1 := by nlinarith [norm_nonneg z.val]
  have h := (coefficient_norm (geometricSequence z)).tsum_eq
  have hsq : ‖geometricSequence z‖ ^ 2 = (1 - ‖z.val‖ ^ 2)⁻¹ := by
    rw [← h]
    change (∑' n : ℕ, ‖z.val ^ n‖ ^ 2) = _
    simpa only [norm_pow, ← pow_mul, Nat.mul_comm] using
      tsum_geometric_of_lt_one (sq_nonneg ‖z.val‖) hz2
  calc
    ‖geometricSequence z‖ = Real.sqrt (‖geometricSequence z‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [hsq, Real.sqrt_inv]

theorem evaluation_bound : EvaluationBound := by
  intro f z hz
  let g := geometricSequence ⟨z, hz⟩
  have hc : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  have hs := lp.summable_mul hc f g
  calc
    ‖eval f z‖ ≤ ∑' n : ℕ, ‖f n‖ * ‖g n‖ := by
      have hs' : Summable (fun n : ℕ => ‖f n * z ^ n‖) := by
        simpa only [g, geometricSequence, norm_mul] using hs
      simpa only [HardyDiskSpec.eval, g, geometricSequence, norm_mul] using norm_tsum_le_tsum_norm hs'
    _ ≤ ‖f‖ * ‖g‖ := lp.tsum_mul_le_mul_norm' hc f g
    _ = _ := by rw [geometricSequence_norm]; rfl

/-- Equality of analytic functions on the disk determines the canonical ℓ² vector. -/
theorem evaluation_injective : EvaluationInjective := by
  intro f g h
  have he : eval f =ᶠ[𝓝 (0 : ℂ)] eval g := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    exact h hz
  have hp := (taylor_hasSeries f).hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    (taylor_hasSeries g).hasFPowerSeriesAt he
  apply lp.ext
  exact (FormalMultilinearSeries.ofScalars_series_eq_iff ℂ (f : ℕ → ℂ) g).mp hp

theorem shift_series (f : H2) :
    HasSum (fun n : ℕ => f n • lp.single (E := fun _ : ℕ => ℂ) 2 (n + 1) (1 : ℂ)) (shift f) :=
  shiftedModes_orthonormal.orthogonalFamily.hasSum_linearIsometry f

@[simp] theorem shift_zero (f : H2) : shift f 0 = 0 := by
  have h := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0).hasSum (shift_series f)
  have heq : (fun n : ℕ => (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0)
      (f n • lp.single (E := fun _ : ℕ => ℂ) 2 (n + 1) (1 : ℂ))) = 0 := by
    funext n
    change f n * lp.single (E := fun _ : ℕ => ℂ) 2 (n + 1) (1 : ℂ) 0 = 0
    simp [lp.single_apply]
  rw [heq] at h
  exact h.unique hasSum_zero

@[simp] theorem shift_succ (f : H2) (k : ℕ) : shift f (k + 1) = f k := by
  have h := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 (k + 1)).hasSum (shift_series f)
  have heq : (fun n : ℕ => (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 (k + 1))
      (f n • lp.single (E := fun _ : ℕ => ℂ) 2 (n + 1) (1 : ℂ))) =
      (fun n : ℕ => if n = k then f k else 0) := by
    funext n
    change f n * lp.single (E := fun _ : ℕ => ℂ) 2 (n + 1) (1 : ℂ) (k + 1) = _
    simp [lp.single_apply, Pi.single_apply, eq_comm]
    split_ifs with hn <;> simp_all
  rw [heq] at h
  exact h.unique (hasSum_ite_eq k (f k))

theorem shift_evaluation : ShiftEvaluation := by
  intro f z hz
  change (∑' n : ℕ, shift f n * z ^ n) = z * (∑' n : ℕ, f n * z ^ n)
  rw [(evaluation_hasSum (shift f) z hz).summable.tsum_eq_zero_add]
  simp only [shift_zero, zero_mul, zero_add, shift_succ, pow_succ]
  simp_rw [← mul_assoc]
  rw [tsum_mul_right]
  ring

/-- Clipping only extends the auxiliary radial family outside its intended [0,1] domain. -/
def clippedRadius (r : ℝ) : ℝ := max 0 (min r 1)

theorem clippedRadius_nonneg (r : ℝ) : 0 ≤ clippedRadius r := le_max_left _ _
theorem clippedRadius_le_one (r : ℝ) : clippedRadius r ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem clippedRadius_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    clippedRadius r = r := by simp [clippedRadius, hr0, hr1]

def radialCoefficients (r : ℝ) (f : H2) : H2 :=
  ⟨fun n => f n * (clippedRadius r : ℂ) ^ n, by
    refine (lp.memℓp f).mono' fun n => ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (clippedRadius_nonneg r)]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀
      (clippedRadius_nonneg r) (clippedRadius_le_one r))⟩

@[simp] theorem radialCoefficients_apply (r : ℝ) (f : H2) (n : ℕ) :
    radialCoefficients r f n = f n * (clippedRadius r : ℂ) ^ n := rfl

theorem radialCoefficients_norm_le (r : ℝ) (f : H2) : ‖radialCoefficients r f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  simp only [radialCoefficients_apply, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (clippedRadius_nonneg r)]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀
    (clippedRadius_nonneg r) (clippedRadius_le_one r))

theorem radialCoefficients_tendsto (f : H2) :
    Tendsto (fun r => radialCoefficients r f) (𝓝 (1 : ℝ)) (𝓝 f) := by
  have hcl : Continuous clippedRadius :=
    continuous_const.max (continuous_id.min continuous_const)
  have hcl1 : Tendsto clippedRadius (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [clippedRadius] using hcl.continuousAt.tendsto (x := (1 : ℝ))
  have hcz : Tendsto (fun r => (clippedRadius r : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hcl1
  have hpt (n : ℕ) : Tendsto
      (fun r => ‖(radialCoefficients r f - f) n‖ ^ 2) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, radialCoefficients_apply, one_pow, mul_one,
      sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (((hcz.pow n).const_mul (f n)).sub_const (f n)).norm.pow 2
  have hnorm (r : ℝ) (n : ℕ) : ‖(radialCoefficients r f - f) n‖ ≤ 2 * ‖f n‖ := by
    change ‖f n * (clippedRadius r : ℂ) ^ n - f n‖ ≤ _
    calc
      _ ≤ ‖f n * (clippedRadius r : ℂ) ^ n‖ + ‖f n‖ := norm_sub_le _ _
      _ ≤ ‖f n‖ + ‖f n‖ := by
        gcongr
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (clippedRadius_nonneg r)]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀
          (clippedRadius_nonneg r) (clippedRadius_le_one r))
      _ = _ := by ring
  have hs : Summable (fun n : ℕ => 4 * ‖f n‖ ^ 2) := (coefficient_norm f).summable.mul_left 4
  have ht := tendsto_tsum_of_dominated_convergence hs hpt
    (Eventually.of_forall fun r n => show ‖‖(radialCoefficients r f - f) n‖ ^ 2‖ ≤
        4 * ‖f n‖ ^ 2 by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (2 * ‖f n‖ - ‖(radialCoefficients r f - f) n‖),
        norm_nonneg ((radialCoefficients r f - f) n), norm_nonneg (f n), hnorm r n])
  have ht' : Tendsto (fun r => ‖radialCoefficients r f - f‖ ^ 2)
      (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [tsum_zero, (coefficient_norm _).tsum_eq] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht'.sqrt

theorem fourier_nat_power (n : ℕ) (t : Circle) :
    fourier (T := 2 * π) (n : ℤ) t = fourier (T := 2 * π) 1 t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem norm_fourier_point (k : ℤ) (t : Circle) :
    ‖fourier (T := 2 * π) k t‖ = 1 := _root_.Circle.norm_coe _

theorem radial_point_mem_disk {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : Circle) :
    (r : ℂ) * fourier (T := 2 * π) 1 t ∈ disk := by
  simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right, norm_mul,
    norm_fourier_point, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0] using hr1

theorem radial_boundary_values (f : H2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (boundary (radialCoefficients r f) : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun t => eval f ((r : ℂ) * fourier (T := 2 * π) 1 t)) := by
  let terms (n : ℕ) : BoundaryL2 :=
    radialCoefficients r f n • fourierLp (T := 2 * π) 2 (n : ℤ)
  have hs : Summable (fun n : ℕ => ‖terms n‖) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left ‖f‖).of_norm_bounded fun n => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    dsimp only [terms]
    rw [norm_smul, (orthonormal_fourier (T := 2 * π)).norm_eq_one, mul_one,
      radialCoefficients_apply, clippedRadius_eq hr0 hr1.le,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num) f n)
      (pow_nonneg hr0 n)
  have hsum : HasSum terms (boundary (radialCoefficients r f)) :=
    boundary_series (radialCoefficients r f)
  have ha := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hs)
  rw [hsum.tsum_eq] at ha
  have hterms : ∀ᵐ t ∂AddCircle.haarAddCircle, ∀ n : ℕ,
      terms n t = radialCoefficients r f n * fourier (T := 2 * π) (n : ℤ) t := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (radialCoefficients r f n)
      (fourierLp (T := 2 * π) 2 (n : ℤ)),
      coeFn_fourierLp (T := 2 * π) 2 (n : ℤ)] with t ht hm
    simp only [terms, ht, Pi.smul_apply, hm, smul_eq_mul]
  filter_upwards [ha, hterms] with t ht hterms
  have heq : (fun n : ℕ => terms n t) =
      (fun n : ℕ => f n * ((r : ℂ) * fourier (T := 2 * π) 1 t) ^ n) := by
    funext n
    rw [hterms n, radialCoefficients_apply, clippedRadius_eq hr0 hr1.le,
      fourier_nat_power, mul_pow, mul_assoc]
  rw [heq] at ht
  exact ht.unique (evaluation_hasSum f _ (radial_point_mem_disk hr0 hr1 t))

theorem radial_convergence : RadialConvergence := by
  intro f
  refine ⟨fun r => boundary (radialCoefficients r f),
    fun r hr0 hr1 => radial_boundary_values f hr0 hr1, ?_⟩
  have ht : Tendsto (fun r => boundary (radialCoefficients r f)) (𝓝 (1 : ℝ))
      (𝓝 (boundary f)) := (boundary.continuous.tendsto f).comp
        (radialCoefficients_tendsto f)
  exact ht.mono_left inf_le_left

/-- Uniquely determined Taylor coefficients of any disk-holomorphic function. -/
def analyticCoefficients (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0

theorem analyticCoefficients_hasSum {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F disk) {z : ℂ} (hz : z ∈ disk) :
    HasSum (fun n : ℕ => analyticCoefficients F n * z ^ n) (F z) := by
  convert Complex.hasSum_taylorSeries_on_ball hF hz using 1
  funext n
  simp only [analyticCoefficients, sub_zero, smul_eq_mul]
  ring

theorem analyticCoefficients_radius {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F disk) :
    (1 : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ (analyticCoefficients F)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
  have hz : (r : ℂ) ∈ disk := by
    simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg] using hr1
  have ht := (analyticCoefficients_hasSum hF hz).summable.tendsto_atTop_zero.norm
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  exact (FormalMultilinearSeries.ofScalars ℂ (analyticCoefficients F)).le_radius_of_bound C
    (by
      intro n
      simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg] using
        hC (Set.mem_range_self n))

/-- A summable Hardy series can also be synthesized pointwise on the circle. -/
theorem boundary_values_of_summable (f : H2) (hs : Summable (fun n : ℕ => ‖f n‖)) :
    (boundary f : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun t => ∑' n : ℕ, f n * fourier (T := 2 * π) (n : ℤ) t) := by
  let terms (n : ℕ) : BoundaryL2 := f n • fourierLp (T := 2 * π) 2 (n : ℤ)
  have hnorm : Summable (fun n => ‖terms n‖) := by
    simpa only [terms, norm_smul, (orthonormal_fourier (T := 2 * π)).norm_eq_one,
      mul_one] using hs
  have ha := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  rw [(boundary_series f).tsum_eq] at ha
  have hterms : ∀ᵐ t ∂AddCircle.haarAddCircle, ∀ n : ℕ,
      terms n t = f n * fourier (T := 2 * π) (n : ℤ) t := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (f n) (fourierLp (T := 2 * π) 2 (n : ℤ)),
      coeFn_fourierLp (T := 2 * π) 2 (n : ℤ)] with t ht hm
    simp only [terms, ht, Pi.smul_apply, hm, smul_eq_mul]
  filter_upwards [ha, hterms] with t ht hm
  rw [← ht.tsum_eq]
  congr 1
  funext n
  exact hm n

set_option maxHeartbeats 800000 in
/-- Square summability of coefficients of any holomorphic function whose radial
circle functions have uniformly bounded L² norm. This is a proved construction,
not an extra assumption on the eventual multiplier. -/
theorem hardy_of_circleBound {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F disk)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ r : ℝ, 0 ≤ r → r < 1 → ∃ g : BoundaryL2,
      (g : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
        (fun t => F ((r : ℂ) * fourier (T := 2 * π) 1 t)) ∧ ‖g‖ ≤ C) :
    ∃ f : H2, Set.EqOn (eval f) F disk ∧ ‖f‖ ≤ C := by
  let a := analyticCoefficients F
  have harr (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
      Summable (fun n : ℕ => ‖a n * (r : ℂ) ^ n‖) := by
    have hr : (r : ℂ) ∈ Metric.eball 0
        (FormalMultilinearSeries.ofScalars ℂ a).radius := by
      apply Metric.eball_subset_eball (analyticCoefficients_radius hF)
      rw [unit_eball]
      simpa only [HardyDiskSpec.disk, Metric.mem_ball,
        dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      (FormalMultilinearSeries.ofScalars ℂ a).summable_norm_apply hr
  have hfinite (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (s : Finset ℕ) :
      ∑ n ∈ s, ‖a n * (r : ℂ) ^ n‖ ^ 2 ≤ C ^ 2 := by
    let ar : H2 := ⟨fun n => a n * (r : ℂ) ^ n,
      Memℓp.of_exponent_ge (q := 1)
        (memℓp_gen (by simpa only [ENNReal.toReal_one, Real.rpow_one] using harr r hr0 hr1))
        (by norm_num)⟩
    obtain ⟨g, hg, hgnorm⟩ := hbound r hr0 hr1
    have hae : (boundary ar : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
        (fun t => F ((r : ℂ) * fourier (T := 2 * π) 1 t)) := by
      filter_upwards [boundary_values_of_summable ar (harr r hr0 hr1)] with t ht
      rw [ht]
      have heq : (fun n : ℕ => ar n * fourier (T := 2 * π) (n : ℤ) t) =
          (fun n : ℕ => a n * ((r : ℂ) * fourier (T := 2 * π) 1 t) ^ n) := by
        funext n
        simp only [ar, fourier_nat_power, mul_pow, mul_assoc]
      rw [heq]
      exact (analyticCoefficients_hasSum hF (radial_point_mem_disk hr0 hr1 t)).tsum_eq
    have he : boundary ar = g := Lp.ext (hae.trans hg.symm)
    have hn : ‖ar‖ ≤ C := by rw [← boundary.norm_map ar, he]; exact hgnorm
    have hsum := lp.sum_rpow_le_norm_rpow (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ar s
    have hsum' : ∑ n ∈ s, ‖a n * (r : ℂ) ^ n‖ ^ 2 ≤ ‖ar‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum
    exact hsum'.trans (by nlinarith [norm_nonneg ar])
  have hfinal (s : Finset ℕ) : ∑ n ∈ s, ‖a n‖ ^ 2 ≤ C ^ 2 := by
    have hcont : Continuous (fun r : ℝ => ∑ n ∈ s, ‖a n * (r : ℂ) ^ n‖ ^ 2) := by
      fun_prop
    have ht : Tendsto (fun r : ℝ => ∑ n ∈ s, ‖a n * (r : ℂ) ^ n‖ ^ 2)
        (𝓝[<] (1 : ℝ)) (𝓝 (∑ n ∈ s, ‖a n‖ ^ 2)) := by
      simpa only [Complex.ofReal_one, one_pow, mul_one] using
        (hcont.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds : (𝓝[<] (1 : ℝ)) ≤ 𝓝 (1 : ℝ))
    apply le_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact hfinite r hr.1.le hr.2 s
  have hmem : Memℓp a 2 := memℓp_gen' (C := C ^ 2) (by
    intro s
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hfinal s)
  refine ⟨⟨a, hmem⟩, ?_, ?_⟩
  · intro z hz
    exact (analyticCoefficients_hasSum hF hz).tsum_eq
  · apply lp.norm_le_of_forall_sum_le (by simp) hC
    intro s
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hfinal s

/-- Radial restriction of a disk-continuous function to a genuine circle function. -/
def circleValues (F : ℂ → ℂ) (hF : ContinuousOn F disk) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : C(Circle, ℂ) :=
  ⟨fun t => F ((r : ℂ) * fourier (T := 2 * π) 1 t),
    hF.comp_continuous (continuous_const.mul (fourier 1).continuous)
      (radial_point_mem_disk hr0 hr1)⟩

def circleValuesLp (F : ℂ → ℂ) (hF : ContinuousOn F disk) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : BoundaryL2 :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleValues F hF r hr0 hr1)

theorem circleValuesLp_coe (F : ℂ → ℂ) (hF : ContinuousOn F disk) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (circleValuesLp F hF r hr0 hr1 : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun t => F ((r : ℂ) * fourier (T := 2 * π) 1 t)) :=
  ContinuousMap.coeFn_toLp _ (circleValues F hF r hr0 hr1)

theorem infinityNorm_bddAbove (b : HInfinity) :
    BddAbove (Set.range (fun z : Disk => ‖b.val z‖)) := by
  obtain ⟨C, hC⟩ := b.property.2
  exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩

theorem norm_le_infinityNorm (b : HInfinity) (z : Disk) : ‖b.val z‖ ≤ infinityNorm b :=
  le_ciSup (infinityNorm_bddAbove b) z

theorem infinityNorm_nonneg (b : HInfinity) : 0 ≤ infinityNorm b :=
  (norm_nonneg (b.val ⟨0, by simp [HardyDiskSpec.disk]⟩)).trans (norm_le_infinityNorm b _)

theorem zeroExtend_apply (b : Disk → ℂ) (z : Disk) :
    zeroExtend b z = b z := by simp [zeroExtend, z.property]

theorem zeroExtend_norm_le (b : HInfinity) {z : ℂ} (hz : z ∈ disk) :
    ‖zeroExtend b.val z‖ ≤ infinityNorm b := by
  change ‖zeroExtend b.val (⟨z, hz⟩ : Disk)‖ ≤ _
  rw [zeroExtend_apply]
  exact norm_le_infinityNorm b ⟨z, hz⟩

theorem bounded_analytic_coefficients : BoundedAnalyticCoefficients := by
  intro b
  have hF := b.property.1
  obtain ⟨f, hf, _⟩ := hardy_of_circleBound hF (infinityNorm_nonneg b) (by
    intro r hr0 hr1
    let g := circleValuesLp (zeroExtend b.val) hF.continuousOn r hr0 hr1
    have hg := circleValuesLp_coe (zeroExtend b.val) hF.continuousOn r hr0 hr1
    refine ⟨g, hg, ?_⟩
    have hn : ‖g‖ ≤ infinityNorm b * ‖(fourierLp (T := 2 * π) 2 0 : BoundaryL2)‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hg, coeFn_fourierLp (T := 2 * π) 2 0] with t ht hm
      rw [ht, hm, norm_fourier_point, mul_one]
      exact zeroExtend_norm_le b (radial_point_mem_disk hr0 hr1 t)
    simpa only [(orthonormal_fourier (T := 2 * π)).norm_eq_one, mul_one] using hn)
  exact ⟨f, fun z => (hf z.property).trans (zeroExtend_apply b.val z)⟩

theorem evaluation_add (f g : H2) (z : ℂ) (hz : z ∈ disk) :
    eval (f + g) z = eval f z + eval g z := by
  have hs := (evaluation_hasSum f z hz).add (evaluation_hasSum g z hz)
  have heq : (fun n : ℕ => f n * z ^ n + g n * z ^ n) =
      (fun n : ℕ => (f + g) n * z ^ n) := by funext n; simp [add_mul]
  rw [heq] at hs
  exact (evaluation_hasSum (f + g) z hz).unique hs

theorem evaluation_smul (c : ℂ) (f : H2) (z : ℂ) :
    eval (c • f) z = c * eval f z := by
  change (∑' n : ℕ, (c • f) n * z ^ n) = c * (∑' n : ℕ, f n * z ^ n)
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]

/-- Membership and the norm bound are derived for every bounded holomorphic
symbol, using radial circle bounds rather than assuming a multiplier certificate. -/
theorem multiplier_exists (b : HInfinity) (f : H2) :
    ∃ h : H2, Set.EqOn (eval h) (fun z => zeroExtend b.val z * eval f z) disk ∧
      ‖h‖ ≤ infinityNorm b * ‖f‖ := by
  have hF : DifferentiableOn ℂ (fun z => zeroExtend b.val z * eval f z) disk :=
    b.property.1.mul (analytic_evaluation f).differentiableOn
  apply hardy_of_circleBound hF (mul_nonneg (infinityNorm_nonneg b) (norm_nonneg f))
  intro r hr0 hr1
  let g := circleValuesLp _ hF.continuousOn r hr0 hr1
  have hg := circleValuesLp_coe _ hF.continuousOn r hr0 hr1
  refine ⟨g, hg, ?_⟩
  have hn : ‖g‖ ≤ infinityNorm b * ‖boundary (radialCoefficients r f)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hg, radial_boundary_values f hr0 hr1] with t ht hf
    rw [ht, hf, norm_mul]
    exact mul_le_mul_of_nonneg_right (zeroExtend_norm_le b
      (radial_point_mem_disk hr0 hr1 t)) (norm_nonneg _)
  rw [boundary.norm_map] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left (radialCoefficients_norm_le r f)
    (infinityNorm_nonneg b))

def multiplierVector (b : HInfinity) (f : H2) : H2 := Classical.choose (multiplier_exists b f)

theorem multiplierVector_eval (b : HInfinity) (f : H2) {z : ℂ} (hz : z ∈ disk) :
    eval (multiplierVector b f) z = zeroExtend b.val z * eval f z :=
  (Classical.choose_spec (multiplier_exists b f)).1 hz

theorem multiplierVector_norm (b : HInfinity) (f : H2) :
    ‖multiplierVector b f‖ ≤ infinityNorm b * ‖f‖ :=
  (Classical.choose_spec (multiplier_exists b f)).2

def multiplierLinear (b : HInfinity) : H2 →ₗ[ℂ] H2 where
  toFun := multiplierVector b
  map_add' := by
    intro f g
    apply evaluation_injective
    intro z hz
    change eval (multiplierVector b (f + g)) z =
      eval (multiplierVector b f + multiplierVector b g) z
    rw [multiplierVector_eval b (f + g) hz, evaluation_add _ _ _ hz,
      evaluation_add _ _ _ hz, multiplierVector_eval b f hz, multiplierVector_eval b g hz,
      mul_add]
  map_smul' := by
    intro c f
    apply evaluation_injective
    intro z hz
    simp only [RingHom.id_apply]
    change eval (multiplierVector b (c • f)) z = eval (c • multiplierVector b f) z
    rw [multiplierVector_eval b (c • f) hz, evaluation_smul, evaluation_smul,
      multiplierVector_eval b f hz]
    ring

/-- Bounded multiplication on the canonical coefficient Hilbert space. -/
def multiplier (b : HInfinity) : H2 →L[ℂ] H2 :=
  (multiplierLinear b).mkContinuous (infinityNorm b) (multiplierVector_norm b)

theorem bounded_multiplier : BoundedMultiplier := by
  intro b
  refine ⟨multiplier b, ?_, ?_⟩
  · intro f z
    change eval (multiplierVector b f) z = _
    rw [multiplierVector_eval b f z.property, zeroExtend_apply]
  · exact LinearMap.mkContinuous_norm_le _ (infinityNorm_nonneg b) (multiplierVector_norm b)

/-- The real Poisson kernel, bundled as a continuous circle function. -/
def poissonKernelMap (z : Disk) : C(Circle, ℂ) := by
  have hne (t : Circle) : fourier (T := 2 * π) 1 t - z.val ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_fourier_point] at hn
    have hz : ‖z.val‖ < 1 := by
      simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using z.property
    linarith
  refine ⟨fun t => (((1 - ‖z.val‖ ^ 2) /
    ‖fourier (T := 2 * π) 1 t - z.val‖ ^ 2 : ℝ) : ℂ), ?_⟩
  exact Complex.continuous_ofReal.comp (continuous_const.div
    (((fourier 1).continuous.sub continuous_const).norm.pow 2)
    (fun t => pow_ne_zero _ (norm_ne_zero_iff.mpr (hne t))))

/-- Pairing with the Poisson kernel on L², hence a continuous functional. -/
def poissonFunctional (z : Disk) : BoundaryL2 →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (poissonKernelMap z))

theorem poissonFunctional_apply (z : Disk) (g : BoundaryL2) :
    poissonFunctional z g = ∫ t : Circle,
      ((1 - ‖z.val‖ ^ 2) / ‖fourier (T := 2 * π) 1 t - z.val‖ ^ 2) • g t
        ∂AddCircle.haarAddCircle := by
  rw [poissonFunctional, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) AddCircle.haarAddCircle (poissonKernelMap z)] with t ht
  rw [ht]
  simp only [RCLike.inner_apply', poissonKernelMap, ContinuousMap.coe_mk,
    Complex.conj_ofReal, Complex.real_smul]

theorem poissonExtension_eq_functional (f : H2) (z : Disk) :
    poissonExtension f z = poissonFunctional z (boundary f) :=
  (poissonFunctional_apply z (boundary f)).symm

theorem circle_integral_eq_average (G : ℂ → ℂ) :
    (∫ t : Circle, G (fourier (T := 2 * π) 1 t) ∂AddCircle.haarAddCircle) =
      Real.circleAverage G 0 1 := by
  rw [ExpandedFA.Fourier.TorusFourierBasis.normalized_integral (2 * π) _ 0,
    Real.circleAverage_def]
  simp only [zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  change G (fourier (T := 2 * π) 1 (θ : AddCircle (2 * π))) = G (circleMap 0 1 θ)
  rw [ExpandedFA.Fourier.TorusFourierBasis.modes.1]
  simp [circleMap_zero, mul_comm]

theorem radial_diffContOnCl (f : H2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    DiffContOnCl ℂ (fun w : ℂ => eval f ((r : ℂ) * w)) disk := by
  have hmem (w : ℂ) (hw : w ∈ Metric.closedBall 0 1) : (r : ℂ) * w ∈ disk := by
    have hw1 : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hn : ‖(r : ℂ) * w‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact (mul_le_of_le_one_right hr0 hw1).trans_lt hr1
    simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using hn
  constructor
  · intro w hw
    have hd := ((analytic_evaluation f) _
      (hmem w (Metric.ball_subset_closedBall hw))).differentiableAt
    exact (hd.comp w ((differentiableAt_const _).mul differentiableAt_id)).differentiableWithinAt
  · intro w hw
    change w ∈ closure (Metric.ball (0 : ℂ) 1) at hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.closure_ball_subset_closedBall hw
    exact (((analytic_evaluation f) _ (hmem w hw')).continuousAt.comp
      (continuous_const.mul continuous_id).continuousAt).continuousWithinAt

theorem poisson_radial_evaluation (f : H2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (z : Disk) : poissonExtension (radialCoefficients r f) z = eval f ((r : ℂ) * z.val) := by
  have hpoisson := (radial_diffContOnCl f hr0 hr1).circleAverage_poissonKernel_smul' z.property
  rw [← circle_integral_eq_average] at hpoisson
  calc
    poissonExtension (radialCoefficients r f) z =
        ∫ t : Circle, ((1 - ‖z.val‖ ^ 2) /
          ‖fourier (T := 2 * π) 1 t - z.val‖ ^ 2) •
          eval f ((r : ℂ) * fourier (T := 2 * π) 1 t) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [radial_boundary_values f hr0 hr1] with t ht
      rw [ht]
    _ = _ := by
      simpa only [sub_zero, norm_fourier_point, one_pow] using hpoisson

theorem poisson_evaluation : PoissonEvaluation := by
  intro f w hw
  let z : Disk := ⟨w, hw⟩
  have hleft : Tendsto (fun r => poissonExtension (radialCoefficients r f) z)
      (𝓝[<] (1 : ℝ)) (𝓝 (poissonExtension f z)) := by
    simp only [poissonExtension_eq_functional]
    exact ((poissonFunctional z).continuous.tendsto (boundary f)).comp
      (((boundary.continuous.tendsto f).comp (radialCoefficients_tendsto f)).mono_left inf_le_left)
  have hright : Tendsto (fun r : ℝ => eval f ((r : ℂ) * z.val))
      (𝓝[<] (1 : ℝ)) (𝓝 (eval f z)) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ) * z.val) (𝓝[<] (1 : ℝ)) (𝓝 z.val) := by
      simpa only [Complex.ofReal_one, one_mul] using
        ((Complex.continuous_ofReal.tendsto (1 : ℝ)).mul_const z.val).mono_left
          (nhdsWithin_le_nhds : (𝓝[<] (1 : ℝ)) ≤ 𝓝 (1 : ℝ))
    exact ((analytic_evaluation f) z.val z.property).continuousAt.tendsto.comp ht
  have heq : (fun r => poissonExtension (radialCoefficients r f) z) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r : ℝ => eval f ((r : ℂ) * z.val)) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact poisson_radial_evaluation f hr.1.le hr.2 z
  exact tendsto_nhds_unique (hleft.congr' heq) hright

theorem hilbert_complete : HilbertComplete := by
  change CompleteSpace H2
  infer_instance

theorem boundary_norm : BoundaryNorm := fun f => boundary.norm_map f

/-- Bounded analytic evaluation as a continuous complex-linear functional. -/
def evaluationMap (z : Disk) : H2 →L[ℂ] ℂ :=
  ({ toFun := fun f => eval f z
     map_add' := fun f g => evaluation_add f g z z.property
     map_smul' := fun c f => evaluation_smul c f z } : H2 →ₗ[ℂ] ℂ).mkContinuous
    (Real.sqrt (1 - ‖z.val‖ ^ 2))⁻¹
    (by
      intro f
      change ‖HardyDiskSpec.eval f z‖ ≤ (Real.sqrt (1 - ‖z.val‖ ^ 2))⁻¹ * ‖f‖
      simpa only [div_eq_mul_inv, mul_comm] using evaluation_bound f z z.property)

theorem evaluation_functional : EvaluationFunctional := by
  intro z
  refine ⟨evaluationMap z, fun _ => rfl, ?_⟩
  apply LinearMap.mkContinuous_norm_le
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem monomial_evaluation : MonomialEvaluation := by
  intro n c z
  change (∑' k : ℕ, lp.single (E := fun _ : ℕ => ℂ) 2 n c k * z ^ k) = c * z ^ n
  simp [lp.single_apply, Pi.single_apply, ite_mul]

theorem polynomial_density : PolynomialDensity := by
  apply top_unique
  intro f _
  refine mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f)
    (Eventually.of_forall ?_)
  intro s
  apply Submodule.sum_mem
  intro n hn
  have he : lp.single (E := fun _ : ℕ => ℂ) 2 n (f n) = f n • lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ) := by
    rw [← lp.single_smul]
    simp
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

end ExpandedFA.PartIV.HardyDisk
