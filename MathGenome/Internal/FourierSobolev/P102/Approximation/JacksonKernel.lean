import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.JacksonKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open MeasureTheory Set
open scoped Real ComplexConjugate

namespace P102.Approximation.Jackson

abbrev AngularCircle := P102.Periodic.Circle (2 * Real.pi)
abbrev angularHaar := P102.Periodic.haar (2 * Real.pi)

abbrev sumModes := Expected.sumValue
abbrev raw := Expected.rawValue
abbrev mass := Expected.massValue
abbrev kernel := Expected.kernelValue

theorem raw_nonnegative (m : ℕ) (x : AngularCircle) : 0 ≤ raw m x :=
  pow_nonneg (norm_nonneg _) _

theorem sumModes_zero (m : ℕ) : sumModes m (0 : AngularCircle) = m := by
  simp [sumModes, Expected.sumValue, P102.Periodic.Expected.mode]

theorem raw_zero (m : ℕ) : raw m (0 : AngularCircle) = (m : ℝ) ^ 4 := by
  simp [raw, Expected.rawValue, sumModes_zero]

/-- The shared modes specialize to the manuscript's angular exponential sum. -/
lemma raw_formula (m : ℕ) (v : ℝ) :
    raw m (v : AngularCircle) =
      ‖∑ k ∈ Finset.range m, Complex.exp (Complex.I * (k : ℂ) * v)‖ ^ 4 := by
  simp only [raw, Expected.rawValue, ContinuousMap.coe_mk, sumModes,
    Expected.sumValue, ContinuousMap.sum_apply]
  change ‖∑ k ∈ Finset.range m,
    P102.Periodic.mode (2 * Real.pi) k (v : AngularCircle)‖ ^ 4 = _
  simp only [P102.Periodic.angular_mode, Int.cast_natCast]

theorem raw_integrable (m : ℕ) : Integrable (raw m) angularHaar :=
  (raw m).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mass_positive (m : ℕ) (hm : 1 ≤ m) : 0 < mass m := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : AngularCircle))
    (raw m).continuous (raw_integrable m) (raw_nonnegative m)
  rw [raw_zero]
  positivity

theorem kernel_nonnegative (m : ℕ) (hm : 1 ≤ m) (x : AngularCircle) :
    0 ≤ kernel m x :=
  div_nonneg (raw_nonnegative m x) (mass_positive m hm).le

theorem sumModes_neg (m : ℕ) (x : AngularCircle) :
    sumModes m (-x) = conj (sumModes m x) := by
  simp only [sumModes, Expected.sumValue, ContinuousMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change fourier (k : ℤ) (-x) = conj (fourier (k : ℤ) x)
  simp only [fourier_apply, smul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

theorem raw_even (m : ℕ) (x : AngularCircle) : raw m (-x) = raw m x := by
  simp only [raw, Expected.rawValue, ContinuousMap.coe_mk, sumModes_neg,
    Complex.norm_conj]

theorem kernel_even (m : ℕ) (_hm : 1 ≤ m) (x : AngularCircle) :
    kernel m (-x) = kernel m x := by
  change raw m (-x) / mass m = raw m x / mass m
  rw [raw_even]

theorem kernel_integral (m : ℕ) (hm : 1 ≤ m) :
    (∫ x, kernel m x ∂angularHaar) = 1 := by
  change (∫ x, raw m x / mass m ∂angularHaar) = 1
  rw [integral_div, show (∫ x, raw m x ∂angularHaar) = mass m from rfl]
  exact div_self (mass_positive m hm).ne'

/-- The four indices record the expansion S · conjugate S · S · conjugate S. -/
def rawCoefficients (m : ℕ) : ℤ →₀ ℂ :=
  ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range m,
    ∑ c ∈ Finset.range m, ∑ d ∈ Finset.range m,
      Finsupp.single ((a : ℤ) - b + c - d) 1

lemma norm_fourth_complex (z : ℂ) :
    ((‖z‖ ^ 4 : ℝ) : ℂ) = z * conj z * z * conj z := by
  calc
    _ = ((‖z‖ ^ 2 : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = (z * conj z) * (z * conj z) := by rw [Complex.mul_conj']; push_cast; rfl
    _ = _ := by ring

lemma fourier_four (a b c d : ℤ) (x : AngularCircle) :
    fourier (a - b + c - d) x =
      fourier a x * conj (fourier b x) * fourier c x * conj (fourier d x) := by
  simp only [sub_eq_add_neg, fourier_add, fourier_neg]

lemma synthesis_rawCoefficients (m : ℕ) (x : AngularCircle) :
    P102.Periodic.synthesis (2 * Real.pi) (rawCoefficients m) x = (raw m x : ℂ) := by
  simp only [rawCoefficients, map_sum, ContinuousMap.sum_apply]
  simp only [P102.Periodic.synthesis, Finsupp.linearCombination_single,
    one_smul]
  simp only [P102.Periodic.mode, fourier_four]
  rw [show (raw m x : ℂ) =
    sumModes m x * conj (sumModes m x) * sumModes m x * conj (sumModes m x)
      from norm_fourth_complex _]
  simp only [sumModes, Expected.sumValue, ContinuousMap.sum_apply, map_sum,
    P102.Periodic.Expected.mode]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

lemma rawCoefficients_supported (m : ℕ) (hm : 1 ≤ m) :
    rawCoefficients m ∈ Finsupp.supported ℂ ℂ
      (Icc (-((2 * m - 2 : ℕ) : ℤ)) ((2 * m - 2 : ℕ) : ℤ)) := by
  unfold rawCoefficients
  refine Submodule.sum_mem _ (fun a ha => ?_)
  refine Submodule.sum_mem _ (fun b hb => ?_)
  refine Submodule.sum_mem _ (fun c hc => ?_)
  refine Submodule.sum_mem _ (fun d hd => ?_)
  apply Finsupp.single_mem_supported
  simp only [Finset.mem_range] at ha hb hc hd
  constructor <;> omega

/-- The coefficient symmetry follows from the real-valued synthesis, using the
shared foundation's coefficient uniqueness rather than an index permutation. -/
theorem kernel_degree (m : ℕ) (hm : 1 ≤ m) :
    kernel m ∈ P102.Periodic.realTrigDegree (2 * Real.pi) (2 * m - 2) := by
  let c : ℤ →₀ ℂ := (mass m : ℂ)⁻¹ • rawCoefficients m
  have hs (x : AngularCircle) :
      P102.Periodic.synthesis (2 * Real.pi) c x = (kernel m x : ℂ) := by
    simp only [c, map_smul, ContinuousMap.smul_apply, smul_eq_mul,
      synthesis_rawCoefficients]
    change (↑(mass m) : ℂ)⁻¹ * ↑(raw m x) = ↑(raw m x / mass m)
    push_cast
    ring
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · exact (Finsupp.supported ℂ ℂ _).smul_mem (mass m : ℂ)⁻¹
      (rawCoefficients_supported m hm)
  · apply (P102.Periodic.real_synthesis_iff (2 * Real.pi) c).mp
    intro x
    rw [hs]
    exact Complex.ofReal_im _
  · ext x
    change (P102.Periodic.synthesis (2 * Real.pi) c x).re = kernel m x
    rw [hs, Complex.ofReal_re]

lemma angular_mode_re (k : ℤ) (v : ℝ) :
    (P102.Periodic.mode (2 * Real.pi) k (v : AngularCircle)).re = Real.cos (k * v) := by
  rw [P102.Periodic.angular_mode]
  rw [show Complex.I * (k : ℂ) * v = ((k * v : ℝ) : ℂ) * Complex.I by push_cast; ring]
  simp [Complex.exp_re]

lemma raw_lower_near_zero (m : ℕ) (hm : 1 ≤ m) (v : ℝ)
    (hv : |v| ≤ (m : ℝ)⁻¹) : (m : ℝ) ^ 4 / 16 ≤ raw m (v : AngularCircle) := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hterm (k : ℕ) (hk : k ∈ Finset.range m) :
      (1 : ℝ) / 2 ≤ (P102.Periodic.mode (2 * Real.pi) k (v : AngularCircle)).re := by
    rw [angular_mode_re]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hk).le
    have hb : |(k : ℝ) * v| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hk0]
      calc
        (k : ℝ) * |v| ≤ (m : ℝ) * (m : ℝ)⁻¹ := mul_le_mul hkm hv (abs_nonneg _) hm0.le
        _ = 1 := mul_inv_cancel₀ hm0.ne'
    obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
    have hsq : ((k : ℝ) * v) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (k : ℝ) * v)
        (by linarith : 0 ≤ 1 + (k : ℝ) * v)]
    have hcos := Real.one_sub_sq_div_two_le_cos (x := (k : ℝ) * v)
    push_cast
    linarith
  have hre : (m : ℝ) / 2 ≤ (sumModes m (v : AngularCircle)).re := by
    calc
      (m : ℝ) / 2 = ∑ _k ∈ Finset.range m, (1 : ℝ) / 2 := by simp; ring
      _ ≤ ∑ k ∈ Finset.range m,
          (P102.Periodic.mode (2 * Real.pi) k (v : AngularCircle)).re :=
        Finset.sum_le_sum hterm
      _ = _ := by simp [sumModes, Expected.sumValue, Complex.re_sum]
  have hn : (m : ℝ) / 2 ≤ ‖sumModes m (v : AngularCircle)‖ :=
    hre.trans (Complex.re_le_norm _)
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m / 2) hn 4
  change (m : ℝ) ^ 4 / 16 ≤ ‖sumModes m (v : AngularCircle)‖ ^ 4
  nlinarith

lemma real_integral_interval (f : AngularCircle → ℝ) (a : ℝ) :
    (∫ x, f x ∂angularHaar) =
      (2 * Real.pi)⁻¹ * ∫ v in a..a + 2 * Real.pi, f (v : AngularCircle) := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) a f]
  rfl

lemma continuous_lift (f : C(AngularCircle, ℝ)) :
    Continuous (fun v : ℝ => f (v : AngularCircle)) :=
  f.continuous.comp (by fun_prop)

/-- A quantitative mass lower bound obtained on the arc |v| ≤ 1/m. -/
theorem mass_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ 3 / (16 * Real.pi) ≤ mass m := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hminv : (m : ℝ)⁻¹ ≤ Real.pi := by
    have : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hm0).mpr (by exact_mod_cast hm)
    linarith [Real.two_le_pi]
  have hint (a b : ℝ) : IntervalIntegrable (fun v : ℝ => raw m (v : AngularCircle))
      volume a b := (continuous_lift (raw m)).intervalIntegrable _ _
  have hsmall : (m : ℝ) ^ 3 / 8 ≤
      ∫ v in -(m : ℝ)⁻¹..(m : ℝ)⁻¹, raw m (v : AngularCircle) := by
    have h := intervalIntegral.integral_mono_on
      (by have := inv_pos.mpr hm0; linarith : -(m : ℝ)⁻¹ ≤ (m : ℝ)⁻¹)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (m : ℝ) ^ 4 / 16)
        volume (-(m : ℝ)⁻¹) ((m : ℝ)⁻¹))
      (hint _ _) (fun v hv => raw_lower_near_zero m hm v (abs_le.mpr hv))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    convert h using 1; field_simp; ring
  have hlarge : (∫ v in -(m : ℝ)⁻¹..(m : ℝ)⁻¹, raw m (v : AngularCircle)) ≤
      ∫ v in -Real.pi..Real.pi, raw m (v : AngularCircle) := by
    exact intervalIntegral.integral_mono_interval (neg_le_neg hminv)
      (by have := inv_pos.mpr hm0; linarith) hminv
      (ae_of_all _ (fun _v => raw_nonnegative m _)) (hint _ _)
  have h := mul_le_mul_of_nonneg_left (hsmall.trans hlarge)
    (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
  rw [mass, Expected.massValue, real_integral_interval _ (-Real.pi)]
  convert h using 1
  · field_simp
    ring
  · congr 2; ring

/-- Coefficients of |S_m|², before the second squaring. -/
def squareCoefficients (m : ℕ) : ℤ →₀ ℂ :=
  ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range m, Finsupp.single ((a : ℤ) - b) 1

lemma synthesis_squareCoefficients (m : ℕ) (x : AngularCircle) :
    P102.Periodic.synthesis (2 * Real.pi) (squareCoefficients m) x =
      ((‖sumModes m x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [squareCoefficients, map_sum, ContinuousMap.sum_apply]
  simp only [P102.Periodic.synthesis, Finsupp.linearCombination_single, one_smul,
    P102.Periodic.mode, sub_eq_add_neg, fourier_add, fourier_neg]
  rw [show ((‖sumModes m x‖ ^ 2 : ℝ) : ℂ) = sumModes m x * conj (sumModes m x) by
    rw [Complex.mul_conj']; push_cast; rfl]
  simp only [sumModes, Expected.sumValue, ContinuousMap.sum_apply, map_sum,
    P102.Periodic.Expected.mode]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

lemma sumModes_integral_sq (m : ℕ) :
    (∫ x, ‖sumModes m x‖ ^ 2 ∂angularHaar) = m := by
  have h := P102.Periodic.coefficient_synthesis (2 * Real.pi) (squareCoefficients m) 0
  have hfun : (fun x => P102.Periodic.synthesis (2 * Real.pi) (squareCoefficients m) x) =
      (fun x : AngularCircle => ((‖sumModes m x‖ ^ 2 : ℝ) : ℂ)) :=
    funext (synthesis_squareCoefficients m)
  simp only [P102.Periodic.coefficient, P102.Periodic.mode, fourier_zero,
    map_one, mul_one] at h
  rw [hfun] at h
  rw [integral_complex_ofReal] at h
  have hc : squareCoefficients m 0 = (m : ℂ) := by
    classical
    simp [squareCoefficients, Finsupp.single_apply, sub_eq_zero, eq_comm]
    rw [Finset.filter_eq_self.mpr (fun a ha => Finset.mem_range.mp ha)]
    simp
  rw [hc] at h
  exact_mod_cast h

lemma mode_nat_pow (k : ℕ) (x : AngularCircle) :
    P102.Periodic.mode (2 * Real.pi) (k : ℤ) x =
      (P102.Periodic.mode (2 * Real.pi) 1 x) ^ k := by
  induction k with
  | zero => simp [P102.Periodic.mode]
  | succ k hk =>
    rw [Nat.cast_add, Nat.cast_one, P102.Periodic.mode, fourier_add]
    rw [← P102.Periodic.mode, hk, pow_succ]

lemma geometric_identity (m : ℕ) (x : AngularCircle) :
    (1 - P102.Periodic.mode (2 * Real.pi) 1 x) * sumModes m x =
      1 - P102.Periodic.mode (2 * Real.pi) (m : ℤ) x := by
  simp only [sumModes, Expected.sumValue, ContinuousMap.sum_apply]
  change (1 - P102.Periodic.mode (2 * Real.pi) 1 x) *
    (∑ k ∈ Finset.range m, P102.Periodic.mode (2 * Real.pi) k x) = _
  simp_rw [mode_nat_pow]
  exact mul_neg_geom_sum _ m

/-- The geometric identity makes the weighted energy of Q_m at most 4m. -/
lemma energy_pointwise (m : ℕ) (x : AngularCircle) :
    ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * raw m x ≤
      4 * ‖sumModes m x‖ ^ 2 := by
  have hnorm : ‖1 - P102.Periodic.mode (2 * Real.pi) (m : ℤ) x‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (P102.Periodic.mode (2 * Real.pi) (m : ℤ) x)
    simp only [norm_one, P102.Periodic.mode, fourier_apply, Circle.norm_coe] at h
    norm_num at h
    exact h
  have hn := congrArg norm (geometric_identity m x)
  rw [norm_mul] at hn
  have hs : ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * ‖sumModes m x‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (1 - P102.Periodic.mode (2 * Real.pi) (m : ℤ) x)]
  change ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * ‖sumModes m x‖ ^ 4 ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖sumModes m x‖)]

lemma energy_integral (m : ℕ) :
    (∫ x, ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * raw m x ∂angularHaar) ≤
      4 * (m : ℝ) := by
  have hcont : Continuous (fun x : AngularCircle =>
      ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * raw m x) := by fun_prop
  have hcont' : Continuous (fun x : AngularCircle => 4 * ‖sumModes m x‖ ^ 2) := by fun_prop
  have hi : Integrable (fun x : AngularCircle =>
      ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * raw m x) angularHaar :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun x : AngularCircle => 4 * ‖sumModes m x‖ ^ 2) angularHaar :=
    hcont'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi hi' (energy_pointwise m)
  rwa [integral_const_mul, sumModes_integral_sq] at h

lemma arc_le_chord (v : ℝ) (hv : |v| ≤ Real.pi) :
    |v| ≤ Real.pi * ‖1 - P102.Periodic.mode (2 * Real.pi) 1 (v : AngularCircle)‖ := by
  rw [P102.Periodic.angular_mode]
  simp only [Int.cast_one, mul_one]
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.mul_abs_le_abs_sin (x := v / 2) (by
    simpa [abs_div] using
      (div_le_div_of_nonneg_right hv (by norm_num : (0 : ℝ) ≤ 2)))
  have hp : 0 < Real.pi := Real.pi_pos
  have h' := mul_le_mul_of_nonneg_left h hp.le
  have heq : Real.pi * (2 / Real.pi * |v / 2|) = |v| := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [heq] at h'
  nlinarith [abs_nonneg (Real.sin (v / 2))]

lemma moment_pointwise (m : ℕ) (v : ℝ) (hv : |v| ≤ Real.pi) :
    (m : ℝ) * (|v| * raw m (v : AngularCircle)) ≤
      Real.pi * ((m : ℝ)^2 *
        (‖1 - P102.Periodic.mode (2 * Real.pi) 1 (v : AngularCircle)‖^2 *
          raw m (v : AngularCircle)) + raw m (v : AngularCircle)) := by
  have h := arc_le_chord v hv
  let a := ‖1 - P102.Periodic.mode (2 * Real.pi) 1 (v : AngularCircle)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hy : (m : ℝ) * a ≤ (m : ℝ)^2 * a^2 + 1 := by
    nlinarith [sq_nonneg ((m : ℝ) * a - 1)]
  have h1 := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m)
  have h2 := mul_le_mul_of_nonneg_left hy Real.pi_pos.le
  have h3 : (m : ℝ) * |v| ≤ Real.pi * ((m : ℝ)^2 * a^2 + 1) := by
    nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (raw_nonnegative m (v : AngularCircle))
  dsimp only [a] at h4
  nlinarith

/-- The first moment before division by the normalizing mass. -/
lemma raw_first_moment_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * ((2 * Real.pi)⁻¹ * ∫ v in -Real.pi..Real.pi,
      |v| * raw m (v : AngularCircle)) ≤
        (Real.pi * (64 * Real.pi + 1)) * mass m := by
  let e : C(AngularCircle, ℝ) :=
    ⟨fun x => ‖1 - P102.Periodic.mode (2 * Real.pi) 1 x‖ ^ 2 * raw m x, by fun_prop⟩
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hr : IntervalIntegrable (fun v : ℝ => raw m (v : AngularCircle)) volume
      (-Real.pi) Real.pi := (continuous_lift (raw m)).intervalIntegrable _ _
  have he : IntervalIntegrable (fun v : ℝ => e (v : AngularCircle)) volume
      (-Real.pi) Real.pi := (continuous_lift e).intervalIntegrable _ _
  have hf : IntervalIntegrable (fun v : ℝ => |v| * raw m (v : AngularCircle)) volume
      (-Real.pi) Real.pi := by
    exact (continuous_abs.mul (continuous_lift (raw m))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hab (hf.const_mul (m : ℝ))
    (((he.const_mul ((m : ℝ)^2)).add hr).const_mul Real.pi)
    (fun v hv => moment_pointwise m v (abs_le.mpr hv))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (he.const_mul _) hr,
    intervalIntegral.integral_const_mul] at h
  have hscaled := mul_le_mul_of_nonneg_left h
    (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
  have hmEq : (2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
      raw m (v : AngularCircle)) = mass m := by
    simpa only [mass, Expected.massValue, show -Real.pi + 2 * Real.pi = Real.pi by ring]
      using (real_integral_interval (raw m) (-Real.pi)).symm
  have heEq : (2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
      e (v : AngularCircle)) = ∫ x, e x ∂angularHaar := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring]
      using (real_integral_interval e (-Real.pi)).symm
  have hnorm : (m : ℝ) * ((2 * Real.pi)⁻¹ * ∫ v in -Real.pi..Real.pi,
      |v| * raw m (v : AngularCircle)) ≤
      Real.pi * ((m : ℝ)^2 * (∫ x, e x ∂angularHaar) + mass m) := by
    rw [← hmEq, ← heEq]
    convert hscaled using 1 <;> ring
  have hgrowth : (m : ℝ)^3 ≤ 16 * Real.pi * mass m := by
    have hh := (div_le_iff₀ (by positivity : 0 < 16 * Real.pi)).mp (mass_lower_bound m hm)
    nlinarith
  have hen : (m : ℝ)^2 * (∫ x, e x ∂angularHaar) ≤ 4 * (m : ℝ)^3 := by
    have hh := mul_le_mul_of_nonneg_left (energy_integral m) (sq_nonneg (m : ℝ))
    convert hh using 1; ring
  nlinarith [mul_le_mul_of_nonneg_left hgrowth (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]

/-- An absolute finite constant, valid also for m=1. -/
theorem kernel_first_moment : Expected.firstMomentStatement := by
  refine ⟨Real.pi * (64 * Real.pi + 1), by positivity, ?_⟩
  intro m hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hmass : 0 < mass m := mass_positive m hm
  have h := raw_first_moment_bound m hm
  change (2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
    |v| * (raw m (v : AngularCircle) / mass m)) ≤ _
  simp_rw [← mul_div_assoc]
  rw [intervalIntegral.integral_div]
  apply (le_div_iff₀ hm0).mpr
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  exact (div_le_iff₀ hmass).mpr (by nlinarith [h])

end P102.Approximation.Jackson
