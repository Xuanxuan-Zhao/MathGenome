import MathGenome.Internal.FourierSobolev.P102.Approximation.JacksonKernel
import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.JacksonPeriodic
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open Set Filter
open scoped Topology

namespace P102.Approximation.JacksonPeriodic

open P102.Periodic

abbrev modulus := Expected.modulusValue
abbrev realBestError := Expected.realBestErrorValue
abbrev complexBestError := Expected.complexBestErrorValue

variable (T : ℝ) [hT : Fact (0 < T)]

/-- In coordinates the metric is the distance to the closest period multiple. -/
theorem arc_distance_formula (s t : ℝ) :
    dist (s : Circle T) (t : Circle T) =
      |s - t - round (T⁻¹ * (s - t)) * T| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq]

theorem norm_rescale (U : ℝ) [hU : Fact (0 < U)] (x : Circle T) :
    ‖rescale T U x‖ = (U / T) * ‖x‖ := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    rw [rescale_formula]
    have h := AddCircle.norm_coe_mul T t (U / T)
    rw [div_mul_cancel₀ U hT.out.ne', abs_of_pos (div_pos hU.out hT.out)] at h
    rw [show U * t / T = (U / T) * t by ring]
    exact h

theorem dist_rescale (U : ℝ) [Fact (0 < U)] (x y : Circle T) :
    dist (rescale T U x) (rescale T U y) = (U / T) * dist x y := by
  rw [dist_eq_norm, ← map_sub, norm_rescale, dist_eq_norm]

theorem rescale_symm (U : ℝ) [hU : Fact (0 < U)] :
    (rescale T U).symm = rescale U T := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    simp only [rescale, AddCircle.equivAddCircle_symm_apply_mk,
      AddCircle.equivAddCircle_apply_mk]

def rescaleContinuousMap (U : ℝ) [hU : Fact (0 < U)] : C(Circle T, Circle U) :=
  ⟨rescale T U, AddCircle.continuous_equivAddCircle T U hT.out.ne' hU.out.ne'⟩

section Modulus
variable {E : Type*} [NormedAddCommGroup E] (f : C(Circle T, E))

theorem increments_bddAbove (δ : ℝ) :
    BddAbove {r : ℝ | ∃ x y : Circle T, dist x y ≤ δ ∧ r = ‖f x - f y‖} := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨x, y, hxy, rfl⟩
  calc
    ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)
    _ = _ := by ring

theorem increments_nonempty {δ : ℝ} (hδ : 0 ≤ δ) :
    {r : ℝ | ∃ x y : Circle T, dist x y ≤ δ ∧ r = ‖f x - f y‖}.Nonempty :=
  ⟨0, 0, 0, by simpa using hδ, by simp⟩

theorem norm_sub_le_modulus {δ : ℝ} {x y : Circle T} (hxy : dist x y ≤ δ) :
    ‖f x - f y‖ ≤ modulus T f δ :=
  le_csSup (increments_bddAbove T f δ) ⟨x, y, hxy, rfl⟩

theorem modulus_nonnegative {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ modulus T f δ := by
  simpa using norm_sub_le_modulus T f (x := 0) (y := 0) (by simpa using hδ)

theorem modulus_le {δ M : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x y : Circle T, dist x y ≤ δ → ‖f x - f y‖ ≤ M) :
    modulus T f δ ≤ M := by
  apply csSup_le (increments_nonempty T f hδ)
  rintro r ⟨x, y, hxy, rfl⟩
  exact h x y hxy

theorem modulus_mono {δ ε : ℝ} (hδ : 0 ≤ δ) (hδε : δ ≤ ε) :
    modulus T f δ ≤ modulus T f ε := by
  apply modulus_le T f hδ
  intro x y hxy
  exact norm_sub_le_modulus T f (hxy.trans hδε)

theorem modulus_le_two_norm {δ : ℝ} (hδ : 0 ≤ δ) : modulus T f δ ≤ 2 * ‖f‖ := by
  apply modulus_le T f hδ
  intro x y hxy
  calc
    ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)
    _ = _ := by ring

theorem modulus_zero : modulus T f 0 = 0 := by
  apply le_antisymm
  · apply modulus_le T f le_rfl
    intro x y hxy
    have : x = y := dist_le_zero.mp hxy
    simp [this]
  · exact modulus_nonnegative T f le_rfl

theorem modulus_le_holder {α H δ : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hf : ∀ x y : Circle T, ‖f x - f y‖ ≤ H * (dist x y) ^ α) :
    modulus T f δ ≤ H * δ ^ α := by
  apply modulus_le T f hδ
  intro x y hxy
  exact (hf x y).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow dist_nonneg hxy hα) hH)

end Modulus

theorem modulus_rescale (U : ℝ) [hU : Fact (0 < U)]
    {E : Type*} [NormedAddCommGroup E] (f : C(Circle U, E)) (g : C(Circle T, E))
    (hfg : ∀ x, g x = f (rescale T U x)) {δ : ℝ} (hδ : 0 ≤ δ) :
    modulus T g δ = modulus U f ((U / T) * δ) := by
  have hc : 0 < U / T := div_pos hU.out hT.out
  apply le_antisymm
  · apply modulus_le T g hδ
    intro x y hxy
    rw [hfg x, hfg y]
    apply norm_sub_le_modulus U f
    rw [dist_rescale]
    exact mul_le_mul_of_nonneg_left hxy hc.le
  · apply modulus_le U f (mul_nonneg hc.le hδ)
    intro x y hxy
    obtain ⟨x, rfl⟩ := (rescale T U).surjective x
    obtain ⟨y, rfl⟩ := (rescale T U).surjective y
    rw [dist_rescale] at hxy
    rw [← hfg x, ← hfg y]
    exact norm_sub_le_modulus T g ((mul_le_mul_iff_right₀ hc).mp hxy)

/-- Pullback by period rescaling preserves the uniform norm. -/
theorem norm_eq_of_rescale (U : ℝ) [Fact (0 < U)]
    {E : Type*} [NormedAddCommGroup E] (f : C(Circle U, E)) (g : C(Circle T, E))
    (hfg : ∀ x, g x = f (rescale T U x)) : ‖g‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    rw [hfg]
    exact f.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    obtain ⟨x, rfl⟩ := (rescale T U).surjective y
    rw [← hfg]
    exact g.norm_coe_le_norm _

theorem complexTrigDegree_mono {m n : ℕ} (hmn : m ≤ n) :
    complexTrigDegree T m ≤ complexTrigDegree T n := by
  apply Submodule.map_mono
  apply Finsupp.supported_mono
  intro k hk
  constructor <;> obtain ⟨hk₁, hk₂⟩ := hk <;> omega

theorem realTrigDegree_mono {m n : ℕ} (hmn : m ≤ n) :
    realTrigDegree T m ≤ realTrigDegree T n := by
  apply Submodule.map_mono
  rintro c ⟨hc, hs⟩
  refine ⟨?_, hs⟩
  exact (Finsupp.supported_mono (show Icc (-(m : ℤ)) (m : ℤ) ⊆
    Icc (-(n : ℤ)) (n : ℤ) by intro k hk; constructor <;> obtain ⟨hk₁, hk₂⟩ := hk <;> omega)) hc

section BestError
variable {𝕜 : Type*} [RCLike 𝕜] (f : C(Circle T, 𝕜))

theorem error_set_bddBelow (S : Submodule 𝕜 C(Circle T, 𝕜)) :
    BddBelow {r : ℝ | ∃ p ∈ S, r = ‖f - p‖} := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact norm_nonneg _

theorem error_set_nonempty (S : Submodule 𝕜 C(Circle T, 𝕜)) :
    {r : ℝ | ∃ p ∈ S, r = ‖f - p‖}.Nonempty :=
  ⟨‖f - 0‖, 0, S.zero_mem, rfl⟩

theorem bestError_nonnegative (S : Submodule 𝕜 C(Circle T, 𝕜)) :
    0 ≤ sInf {r : ℝ | ∃ p ∈ S, r = ‖f - p‖} := by
  apply le_csInf (error_set_nonempty T f S)
  rintro r ⟨p, hp, rfl⟩
  exact norm_nonneg _

theorem bestError_le_error (S : Submodule 𝕜 C(Circle T, 𝕜))
    {p : C(Circle T, 𝕜)} (hp : p ∈ S) :
    sInf {r : ℝ | ∃ p ∈ S, r = ‖f - p‖} ≤ ‖f - p‖ :=
  csInf_le (error_set_bddBelow T f S) ⟨p, hp, rfl⟩

theorem bestError_le_norm (S : Submodule 𝕜 C(Circle T, 𝕜)) :
    sInf {r : ℝ | ∃ p ∈ S, r = ‖f - p‖} ≤ ‖f‖ := by
  simpa using bestError_le_error T f S S.zero_mem

end BestError

/-- A quantitative consequence of a modulus estimate, independent of the
construction of the approximating polynomial. -/
theorem holder_bound_of_modulus_bound {E : Type*} [NormedAddCommGroup E]
    (f : C(Circle T, E)) {α H C e : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hf : ∀ x y : Circle T, ‖f x - f y‖ ≤ H * (dist x y) ^ α)
    (he : e ≤ C * modulus T f (T / (n : ℝ))) :
    e ≤ (C * H * T ^ α) * (n : ℝ) ^ (-α) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hmod := modulus_le_holder T f hα hH
    (div_nonneg hT.out.le hn0.le) hf
  calc
    e ≤ C * (H * (T / (n : ℝ)) ^ α) :=
      he.trans (mul_le_mul_of_nonneg_left hmod hC)
    _ = (C * H * T ^ α) * (n : ℝ) ^ (-α) := by
      rw [Real.div_rpow hT.out.le hn0.le, Real.rpow_neg hn0.le]
      ring

theorem realBestError_nonnegative (f : C(Circle T, ℝ)) (n : ℕ) :
    0 ≤ realBestError T f n := bestError_nonnegative T f (realTrigDegree T n)

theorem complexBestError_nonnegative (f : C(Circle T, ℂ)) (n : ℕ) :
    0 ≤ complexBestError T f n := bestError_nonnegative T f (complexTrigDegree T n)

/-- The asymptotic deduction uses only the universal direct estimate. -/
theorem holder_rate_of_direct (hdirect : Expected.directStatement) :
    Expected.holderStatement := by
  obtain ⟨C, hC, hbound⟩ := hdirect
  intro T hT α hα hα1 H hH
  constructor
  · intro f hf
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨C * H * T ^ α, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (realBestError_nonnegative T f n),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact holder_bound_of_modulus_bound T f hn hα.le hH hC hf ((hbound T n hn).1 f)
  · intro f hf
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨C * H * T ^ α, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (complexBestError_nonnegative T f n),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact holder_bound_of_modulus_bound T f hn hα.le hH hC hf ((hbound T n hn).2 f)

/-- Subdivision of a lifted arc controls arbitrary increments by the modulus. -/
theorem lifted_increment_bound {E : Type*} [NormedAddCommGroup E]
    (f : C(Circle T, E)) (m : ℕ) (hm : 1 ≤ m) (x : Circle T) (v : ℝ) :
    ‖f x - f (x - (v : Circle T))‖ ≤
      (1 + (m : ℝ) * |v|) * modulus T f (1 / (m : ℝ)) := by
  let q : ℕ := ⌊(m : ℝ) * |v|⌋₊ + 1
  have hm0 : (0 : ℝ) < m := by positivity
  have hq0 : (0 : ℝ) < q := by dsimp [q]; positivity
  have hq : (m : ℝ) * |v| ≤ q := by
    simpa only [q, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((m : ℝ) * |v|)).le
  have hq' : (q : ℝ) ≤ 1 + (m : ℝ) * |v| := by
    dsimp [q]
    push_cast
    linarith [Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (abs_nonneg v))]
  have hstep : |v| / (q : ℝ) ≤ 1 / (m : ℝ) := by
    apply (div_le_div_iff₀ hq0 hm0).mpr
    nlinarith
  let a : ℕ → Circle T := fun i => x - (((i : ℝ) * v / q : ℝ) : Circle T)
  have hd : ∀ i : ℕ, dist (a i) (a (i + 1)) ≤ 1 / (m : ℝ) := by
    intro i
    dsimp [a]
    rw [dist_eq_norm, show x - (((i : ℝ) * v / q : ℝ) : Circle T) -
      (x - ((((i + 1 : ℕ) : ℝ) * v / q : ℝ) : Circle T)) =
      (((((i + 1 : ℕ) : ℝ) * v / q : ℝ) : Circle T) -
        (((i : ℝ) * v / q : ℝ) : Circle T)) by abel,
      norm_sub_rev, ← QuotientAddGroup.mk_sub]
    calc
      _ ≤ ‖(i : ℝ) * v / q - ((i + 1 : ℕ) : ℝ) * v / q‖ :=
        QuotientAddGroup.norm_mk_le_norm
      _ = |v| / (q : ℝ) := by
        rw [show (i : ℝ) * v / q - ((i + 1 : ℕ) : ℝ) * v / q = -v / q by
          push_cast; ring, norm_div, norm_neg, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hq0]
      _ ≤ _ := hstep
  have hb := dist_le_range_sum_of_dist_le (f := fun i => f (a i)) q
    (d := fun _ => modulus T f (1 / (m : ℝ))) (fun {i} hi => by
      rw [dist_eq_norm]
      exact norm_sub_le_modulus T f (hd i))
  have ha0 : a 0 = x := by simp [a]
  have haq : a q = x - (v : Circle T) := by
    dsimp [a]
    rw [mul_div_cancel_left₀ v hq0.ne']
  rw [ha0, haq, dist_eq_norm] at hb
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hq'
    (modulus_nonnegative T f (by positivity)))

open MeasureTheory
open scoped ComplexConjugate

/-- A finite-frequency real kernel preserves the degree under convolution. -/
theorem convolution_polynomial (f : C(Circle T, ℂ)) (K : C(Circle T, ℝ))
    (n : ℕ) (hK : K ∈ realTrigDegree T n) :
    ∃ p ∈ complexTrigDegree T n, ∀ x : Circle T,
      p x = ∫ y, f (x - y) * (K y : ℂ) ∂haar T := by
  classical
  obtain ⟨c, ⟨hc, hsym⟩, hK⟩ := hK
  have hcK (x : Circle T) : (K x : ℂ) = synthesis T c x := by
    rw [← hK]
    exact symmetric_synthesis T c hsym x
  let d : ℤ →₀ ℂ := ∑ k ∈ c.support,
    Finsupp.single k (c k * coefficient T f k)
  have hd : d ∈ Finsupp.supported ℂ ℂ (Icc (-(n : ℤ)) (n : ℤ)) := by
    apply Submodule.sum_mem
    intro k hk
    exact Finsupp.single_mem_supported ℂ _ ((Finsupp.mem_supported ℂ c).mp hc hk)
  refine ⟨synthesis T d, ⟨d, hd, rfl⟩, ?_⟩
  intro x
  have hmode (k : ℤ) (y : Circle T) :
      mode T k (x - y) = mode T k x * conj (mode T k y) := by
    simp only [mode, fourier_apply, sub_eq_add_neg, smul_add, smul_neg,
      AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul,
      Circle.coe_inv_eq_conj]
  have hswap : (∫ y, f (x - y) * (K y : ℂ) ∂haar T) =
      ∫ y, f y * (K (x - y) : ℂ) ∂haar T := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self (fun y => f y * (K (x - y) : ℂ)) (haar T) x)
  rw [hswap]
  have heq : (fun y : Circle T => f y * (K (x - y) : ℂ)) =
      fun y => ∑ k ∈ c.support,
        (c k * mode T k x) * (f y * conj (mode T k y)) := by
    funext y
    rw [hcK, synth_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmode]
    ring
  rw [heq, integral_finsetSum]
  · simp only [integral_const_mul]
    simp only [d, map_sum, ContinuousMap.sum_apply, synthesis,
      Finsupp.linearCombination_single, ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    unfold coefficient
    ring
  · intro k hk
    have hcont : Continuous (fun y : Circle T =>
        (c k * mode T k x) * (f y * conj (mode T k y))) := by fun_prop
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The mass and first moment give the pointwise Jackson error bound. -/
theorem jackson_pointwise : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), 1 ≤ m →
    ∀ (f : C(Circle (2 * Real.pi), ℂ)) (x : Circle (2 * Real.pi)),
    ‖f x - ∫ y, f (x - y) * (Jackson.kernel m y : ℂ) ∂haar (2 * Real.pi)‖ ≤
      C * modulus (2 * Real.pi) f (1 / (m : ℝ)) := by
  obtain ⟨C₀, hC₀, hmoment⟩ := Jackson.kernel_first_moment
  refine ⟨1 + C₀, by linarith, ?_⟩
  intro m hm f x
  let K := Jackson.kernel m
  let M := modulus (2 * Real.pi) f (1 / (m : ℝ))
  have hM : 0 ≤ M := modulus_nonnegative _ f (by positivity)
  have hm0 : (0 : ℝ) < m := by positivity
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hscale : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hK : ∀ y, 0 ≤ K y := Jackson.kernel_nonnegative m hm
  have hint : (∫ y, K y ∂haar (2 * Real.pi)) = 1 := Jackson.kernel_integral m hm
  have hi : Integrable (fun y => f (x - y) * (K y : ℂ)) (haar (2 * Real.pi)) := by
    have hc : Continuous (fun y => f (x - y) * (K y : ℂ)) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiconst : Integrable (fun y => f x * (K y : ℂ)) (haar (2 * Real.pi)) := by
    have hc : Continuous (fun y : Circle (2 * Real.pi) => f x * (K y : ℂ)) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have herr : f x - (∫ y, f (x - y) * (K y : ℂ) ∂haar (2 * Real.pi)) =
      ∫ y, (f x - f (x - y)) * (K y : ℂ) ∂haar (2 * Real.pi) := by
    simp_rw [sub_mul]
    rw [integral_sub hiconst hi, integral_const_mul, integral_complex_ofReal, hint]
    simp
  rw [herr, AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi),
    show -Real.pi + 2 * Real.pi = Real.pi by ring, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hscale]
  have hKlift := Jackson.continuous_lift K
  have hiK := hKlift.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hiMoment : IntervalIntegrable (fun v : ℝ => |v| * K (v : Circle (2 * Real.pi)))
      volume (-Real.pi) Real.pi :=
    (continuous_abs.mul hKlift).intervalIntegrable (-Real.pi) Real.pi
  have hbound : ‖∫ v in -Real.pi..Real.pi,
        (f x - f (x - (v : Circle (2 * Real.pi)))) * (K (v : Circle (2 * Real.pi)) : ℂ)‖ ≤
      ∫ v in -Real.pi..Real.pi,
        (K (v : Circle (2 * Real.pi)) + (m : ℝ) *
          (|v| * K (v : Circle (2 * Real.pi)))) * M := by
    apply intervalIntegral.norm_integral_le_of_norm_le hπ
    · apply ae_of_all
      intro v hv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK _)]
      have hh := mul_le_mul_of_nonneg_right
        (lifted_increment_bound (2 * Real.pi) f m hm x v) (hK (v : Circle (2 * Real.pi)))
      dsimp only [M] at *
      nlinarith [hh]
    · exact (hiK.add (hiMoment.const_mul (m : ℝ))).mul_const M
  have hmass : (2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
      K (v : Circle (2 * Real.pi))) = 1 := by
    rw [← hint]
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      (Jackson.real_integral_interval K (-Real.pi)).symm
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
        (K (v : Circle (2 * Real.pi)) + (m : ℝ) *
          (|v| * K (v : Circle (2 * Real.pi)))) * M) :=
      mul_le_mul_of_nonneg_left hbound hscale
    _ = (1 + (m : ℝ) * ((2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
        |v| * K (v : Circle (2 * Real.pi))))) * M := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_add hiK (hiMoment.const_mul (m : ℝ)),
        intervalIntegral.integral_const_mul]
      nlinarith [hmass]
    _ ≤ (1 + C₀) * M := by
      have hh := (hmoment m hm)
      have hh' : (m : ℝ) * ((2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
          |v| * K (v : Circle (2 * Real.pi)))) ≤ C₀ := by
        exact (mul_le_mul_of_nonneg_left hh hm0.le).trans_eq (by field_simp)
      exact mul_le_mul_of_nonneg_right (by linarith) hM

/-- The first-moment bound and finite-frequency convolution give one absolute
approximation constant for real and complex data on the angular circle. -/
theorem angular_approximation : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), 1 ≤ m →
    (∀ f : C(Circle (2 * Real.pi), ℝ), ∃ p ∈ realTrigDegree (2 * Real.pi) (2 * m - 2),
      ‖f - p‖ ≤ C * modulus (2 * Real.pi) f (1 / (m : ℝ))) ∧
    (∀ f : C(Circle (2 * Real.pi), ℂ), ∃ p ∈ complexTrigDegree (2 * Real.pi) (2 * m - 2),
      ‖f - p‖ ≤ C * modulus (2 * Real.pi) f (1 / (m : ℝ))) := by
  obtain ⟨C, hC, hpoint⟩ := jackson_pointwise
  have hcomplex : ∀ m : ℕ, 1 ≤ m →
      ∀ f : C(Circle (2 * Real.pi), ℂ),
      ∃ p ∈ complexTrigDegree (2 * Real.pi) (2 * m - 2),
        ‖f - p‖ ≤ C * modulus (2 * Real.pi) f (1 / (m : ℝ)) := by
    intro m hm f
    obtain ⟨p, hp, hpx⟩ := convolution_polynomial (2 * Real.pi) f
      (Jackson.kernel m) (2 * m - 2) (Jackson.kernel_degree m hm)
    refine ⟨p, hp, (ContinuousMap.norm_le _ (mul_nonneg hC
      (modulus_nonnegative _ f (by positivity)))).mpr ?_⟩
    intro x
    change ‖f x - p x‖ ≤ _
    rw [hpx]
    exact hpoint m hm f x
  refine ⟨C, hC, ?_⟩
  intro m hm
  refine ⟨?_, hcomplex m hm⟩
  intro f
  let F : C(Circle (2 * Real.pi), ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  obtain ⟨p, hp, hpx⟩ := convolution_polynomial (2 * Real.pi) F
    (Jackson.kernel m) (2 * m - 2) (Jackson.kernel_degree m hm)
  have hpReal : ∀ x, (p x).im = 0 := by
    intro x
    rw [hpx]
    change (∫ y, (f (x - y) : ℂ) * (Jackson.kernel m y : ℂ)
      ∂haar (2 * Real.pi)).im = 0
    simp_rw [← Complex.ofReal_mul]
    rw [integral_complex_ofReal, Complex.ofReal_im]
  obtain ⟨c, hc, hcp⟩ := hp
  have hsym : c ∈ symmetricCoefficients := by
    apply (real_synthesis_iff (2 * Real.pi) c).mp
    intro x
    rw [hcp]
    exact hpReal x
  let q := realSynthesis (2 * Real.pi) c
  have hq : q ∈ realTrigDegree (2 * Real.pi) (2 * m - 2) :=
    ⟨c, ⟨hc, hsym⟩, rfl⟩
  have hqp (x : Circle (2 * Real.pi)) : (q x : ℂ) = p x := by
    change (realSynthesis (2 * Real.pi) c x : ℂ) = p x
    rw [symmetric_synthesis _ c hsym, hcp]
  have hmod : modulus (2 * Real.pi) F (1 / (m : ℝ)) =
      modulus (2 * Real.pi) f (1 / (m : ℝ)) := by
    unfold modulus Expected.modulusValue
    simp only [F, ContinuousMap.coe_mk, ← Complex.ofReal_sub, Complex.norm_real]
  refine ⟨q, hq, (ContinuousMap.norm_le _ (mul_nonneg hC
    (modulus_nonnegative _ f (by positivity)))).mpr ?_⟩
  intro x
  change ‖f x - q x‖ ≤ _
  have heq : ‖f x - q x‖ = ‖F x - p x‖ := by
    rw [← hqp]
    change ‖f x - q x‖ = ‖(f x : ℂ) - (q x : ℂ)‖
    rw [← Complex.ofReal_sub, Complex.norm_real]
  rw [heq, hpx]
  exact (hpoint m hm F x).trans_eq (by rw [hmod])

theorem jackson_scale_bound (n : ℕ) (hn : 1 ≤ n) :
    (T / (2 * Real.pi)) * (1 / ((n / 2 + 1 : ℕ) : ℝ)) ≤ T / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hm0 : (0 : ℝ) < (n / 2 + 1 : ℕ) := by positivity
  have hnm : (n : ℝ) ≤ 2 * ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (n / 2 + 1) by omega)
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hnm' : (n : ℝ) ≤ (2 * Real.pi) * ((n / 2 + 1 : ℕ) : ℝ) :=
    hnm.trans (mul_le_mul_of_nonneg_right hpi hm0.le)
  calc
    _ = T / ((2 * Real.pi) * ((n / 2 + 1 : ℕ) : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ T / (n : ℝ) := div_le_div_of_nonneg_left hT.out.le hn0 hnm'

theorem direct_estimate : Expected.directStatement := by
  obtain ⟨C, hC, happrox⟩ := angular_approximation
  refine ⟨C, hC, ?_⟩
  intro T hT n hn
  let m := n / 2 + 1
  have hm : 1 ≤ m := by omega
  have hdeg : 2 * m - 2 ≤ n := by omega
  have hδ : 0 ≤ 1 / (m : ℝ) := by positivity
  have hδT : 0 ≤ T / (2 * Real.pi) * (1 / (m : ℝ)) :=
    mul_nonneg (div_nonneg hT.out.le (by positivity)) hδ
  constructor
  · intro f
    let F := f.comp (rescaleContinuousMap (2 * Real.pi) T)
    obtain ⟨p, hp, herr⟩ := (happrox m hm).1 F
    let q := p.comp (rescaleContinuousMap T (2 * Real.pi))
    have hq : q ∈ realTrigDegree T n := by
      apply realTrigDegree_mono T hdeg
      exact ((real_trig_transport T (2 * Real.pi) p q (fun x => rfl) (2 * m - 2)).2).mpr hp
    have hnorm : ‖f - q‖ = ‖F - p‖ := by
      apply norm_eq_of_rescale T (2 * Real.pi) (F - p) (f - q)
      intro x
      change f x - p (rescale T (2 * Real.pi) x) =
        f (rescale (2 * Real.pi) T (rescale T (2 * Real.pi) x)) -
          p (rescale T (2 * Real.pi) x)
      rw [← rescale_symm T (2 * Real.pi), AddEquiv.symm_apply_apply]
    have hmod : modulus (2 * Real.pi) F (1 / (m : ℝ)) ≤ modulus T f (T / (n : ℝ)) := by
      rw [modulus_rescale (2 * Real.pi) T f F (fun x => rfl) hδ]
      exact modulus_mono T f hδT (jackson_scale_bound T n hn)
    exact (bestError_le_error T f (realTrigDegree T n) hq).trans
      (hnorm.le.trans (herr.trans (mul_le_mul_of_nonneg_left hmod hC)))
  · intro f
    let F := f.comp (rescaleContinuousMap (2 * Real.pi) T)
    obtain ⟨p, hp, herr⟩ := (happrox m hm).2 F
    let q := p.comp (rescaleContinuousMap T (2 * Real.pi))
    have hq : q ∈ complexTrigDegree T n := by
      apply complexTrigDegree_mono T hdeg
      exact ((complex_trig_transport T (2 * Real.pi) p q (fun x => rfl) (2 * m - 2)).2).mpr hp
    have hnorm : ‖f - q‖ = ‖F - p‖ := by
      apply norm_eq_of_rescale T (2 * Real.pi) (F - p) (f - q)
      intro x
      change f x - p (rescale T (2 * Real.pi) x) =
        f (rescale (2 * Real.pi) T (rescale T (2 * Real.pi) x)) -
          p (rescale T (2 * Real.pi) x)
      rw [← rescale_symm T (2 * Real.pi), AddEquiv.symm_apply_apply]
    have hmod : modulus (2 * Real.pi) F (1 / (m : ℝ)) ≤ modulus T f (T / (n : ℝ)) := by
      rw [modulus_rescale (2 * Real.pi) T f F (fun x => rfl) hδ]
      exact modulus_mono T f hδT (jackson_scale_bound T n hn)
    exact (bestError_le_error T f (complexTrigDegree T n) hq).trans
      (hnorm.le.trans (herr.trans (mul_le_mul_of_nonneg_left hmod hC)))

theorem holder_rate : Expected.holderStatement := holder_rate_of_direct direct_estimate

end P102.Approximation.JacksonPeriodic
