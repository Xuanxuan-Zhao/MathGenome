import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.PoissonNormRecovery
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal ComplexConjugate

namespace P102.Periodic
variable (T : ℝ) [Fact (0 < T)]

omit [Fact (0 < T)] in
lemma mode_norm (k : ℤ) (x : Circle T) : ‖mode T k x‖ = 1 := by
  exact Circle.norm_coe _

lemma poisson_denominator_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle T) :
    0 < 1 - 2 * r * (mode T 1 x).re + r ^ 2 := by
  have hx : (mode T 1 x).re ≤ 1 := by
    simpa only [mode_norm] using Complex.re_le_norm (mode T 1 x)
  have hsq : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hx)]

theorem poisson_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle T) :
    0 ≤ poissonKernel T r x := by
  apply div_nonneg _ (poisson_denominator_pos T hr hr1 x).le
  nlinarith

omit [Fact (0 < T)] in
theorem poisson_even (r : ℝ) (x : Circle T) :
    poissonKernel T r (-x) = poissonKernel T r x := by
  have hx : mode T 1 (-x) = conj (mode T 1 x) := by
    simp only [mode, fourier_apply, one_zsmul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  simp only [poissonKernel, hx, Complex.conj_re]

theorem poisson_kernel_basic : Expected.PoissonNormRecovery.kernelBasic := by
  intro T hT r hr hr1 x
  exact ⟨poisson_nonneg T hr hr1 x, poisson_even T r x⟩

lemma poisson_angular (r v : ℝ) :
    poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos v + r ^ 2) := by
  rw [poisson_formula]
  have h : 2 * Real.pi * (T * v / (2 * Real.pi)) / T = v := by
    field_simp [ne_of_gt (Fact.out : 0 < T)]
  rw [h]

theorem poisson_kernel_monotone : Expected.PoissonNormRecovery.kernelMonotone := by
  intro T hT r hr hr1 u hu v hv huv
  change poissonKernel T r _ ≤ poissonKernel T r _
  simp only [poisson_angular]
  have hc := Real.strictAntiOn_cos.antitoneOn hu hv huv
  have hn : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hd : 0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
    have hx := poisson_denominator_pos T hr hr1
      (((T * u / (2 * Real.pi) : ℝ) : Circle T))
    have hm : (mode T 1 (((T * u / (2 * Real.pi) : ℝ) : Circle T))).re = Real.cos u := by
      rw [mode, fourier_coe_apply]
      have he : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) *
          ((T * u / (2 * Real.pi) : ℝ) : ℂ) / T = (u : ℂ) * Complex.I := by
        push_cast
        field_simp [ne_of_gt (Fact.out : 0 < T)]
      rw [he]
      simp [Complex.exp_re]
    simpa only [hm] using hx
  apply div_le_div_of_nonneg_left hn hd
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hc)]

/-- A scalar majorant that remains valid at r = 0. -/
lemma summable_poisson_weights {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℤ => r ^ k.natAbs) := by
  have h : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr hr1
  exact Summable.of_nat_of_neg (by simpa using h) (by simpa using h)

lemma coefficient_norm_le_integral_norm (f : Circle T → ℂ) (k : ℤ) :
    ‖coefficient T f k‖ ≤ ∫ x, ‖f x‖ ∂haar T := by
  calc
    ‖coefficient T f k‖ ≤ ∫ x, ‖f x * conj (mode T k x)‖ ∂haar T :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ ∂haar T := by
      congr 1
      funext x
      simp

lemma poisson_series_abs {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle T) :
    Summable (fun k : ℤ => ‖(r ^ k.natAbs : ℂ) * mode T k x‖) := by
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    mode_norm, mul_one] using summable_poisson_weights hr hr1

lemma abel_term_bound {r : ℝ} (hr : 0 ≤ r) (f : Circle T → ℂ) (k : ℤ) (x : Circle T) :
    ‖(r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x‖ ≤
      r ^ k.natAbs * (∫ y, ‖f y‖ ∂haar T) := by
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    mode_norm, mul_one]
  exact mul_le_mul_of_nonneg_left (coefficient_norm_le_integral_norm T f k) (pow_nonneg hr _)

theorem abel_series : Expected.PoissonNormRecovery.abelSeries := by
  intro T hT r hr hr1 f hf
  have hw := (summable_poisson_weights hr hr1).mul_right (∫ y, ‖f y‖ ∂haar T)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => abel_term_bound T hr f k x) hw
  · refine tendstoUniformly_tsum hw ?_
    intro k x
    change ‖‖(r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x‖‖ ≤
      r ^ k.natAbs * (∫ y, ‖f y‖ ∂haar T)
    rw [norm_norm]
    exact abel_term_bound T hr f k x
  · exact tendstoUniformly_tsum hw (fun k x => abel_term_bound T hr f k x)

omit [Fact (0 < T)] in
lemma mode_nat (n : ℕ) (x : Circle T) : mode T (n : ℤ) x = mode T 1 x ^ n := by
  induction n with
  | zero => simp [mode]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, mode, fourier_add]
    change mode T (n : ℤ) x * mode T 1 x = mode T 1 x ^ (n + 1)
    rw [ih, pow_succ]

lemma poisson_hasSum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle T) :
    HasSum (fun k : ℤ => (r ^ k.natAbs : ℂ) * mode T k x)
      (poissonKernel T r x : ℂ) := by
  let z := mode T 1 x
  have hn : ‖z‖ = 1 := mode_norm T 1 x
  have ha : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hn, abs_of_nonneg hr] using hr1
  have hb : ‖(r : ℂ) * conj z‖ < 1 := by
    simpa [norm_mul, Complex.norm_conj, hn, abs_of_nonneg hr] using hr1
  have hpos : HasSum (fun n : ℕ => (r ^ (n : ℤ).natAbs : ℂ) * mode T (n : ℤ) x)
      (1 - (r : ℂ) * z)⁻¹ := by
    convert hasSum_geometric_of_norm_lt_one ha using 1
    funext n
    rw [Int.natAbs_natCast, mode_nat, mul_pow]
  have hneg : HasSum
      (fun n : ℕ => (r ^ (-(n + 1 : ℤ)).natAbs : ℂ) * mode T (-(n + 1 : ℤ)) x)
      ((r : ℂ) * conj z * (1 - (r : ℂ) * conj z)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hb).mul_left ((r : ℂ) * conj z) using 1
    funext n
    rw [mode, fourier_neg]
    change _ * conj (mode T (n + 1 : ℤ) x) = _
    rw [show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by simp, mode_nat, map_pow]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, mul_pow, pow_succ]
    dsimp only [z]
    ring
  have hsum := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => (r ^ k.natAbs : ℂ) * mode T k x) hpos hneg
  have hm : z * conj z = 1 := by rw [Complex.mul_conj', hn]; norm_num
  have hs : z + conj z = 2 * (z.re : ℂ) := by
    apply Complex.ext
    · simp
      ring
    · simp
  have hd : (1 - (r : ℂ) * z) * (1 - (r : ℂ) * conj z) =
      ((1 - 2 * r * z.re + r ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (r : ℂ) ^ 2 * hm - (r : ℂ) * hs
  have hda : 1 - (r : ℂ) * z ≠ 0 := by
    intro h
    have he : (r : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one, lt_self_iff_false] at ha
  have hdb : 1 - (r : ℂ) * conj z ≠ 0 := by
    intro h
    have he : (r : ℂ) * conj z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one, lt_self_iff_false] at hb
  convert hsum using 1
  change (((1 - r ^ 2) / (1 - 2 * r * z.re + r ^ 2) : ℝ) : ℂ) = _
  push_cast at hd ⊢
  rw [← hd]
  field_simp [hda, hdb]
  linear_combination (r : ℂ) ^ 2 * hm

theorem poisson_kernel_series : Expected.PoissonNormRecovery.kernelSeries := by
  intro T hT r hr hr1
  refine ⟨poisson_series_abs T hr hr1, ?_, ?_⟩
  · exact tendstoUniformly_tsum (summable_poisson_weights hr hr1)
      (fun k (x : Circle T) => by
        simp [norm_pow, abs_of_nonneg hr])
  · have hu := tendstoUniformly_tsum (summable_poisson_weights hr hr1)
      (fun k (x : Circle T) => show ‖(r ^ k.natAbs : ℂ) * mode T k x‖ ≤ r ^ k.natAbs by
        simp [norm_pow, abs_of_nonneg hr])
    have he : (fun x : Circle T => ∑' k : ℤ, (r ^ k.natAbs : ℂ) * mode T k x) =
        (fun x => (poissonKernel T r x : ℂ)) := by
      funext x
      exact (poisson_hasSum T hr hr1 x).tsum_eq
    rw [he] at hu
    exact hu

lemma poisson_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (poissonKernel T r) := by
  unfold poissonKernel
  exact continuous_const.div (by fun_prop)
    (fun x => (poisson_denominator_pos T hr hr1 x).ne')

lemma integral_mode (k : ℤ) : (∫ x, mode T k x ∂haar T) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) k) 0
  simpa [fourierCoeff, mode, fourier_zero, Pi.single_apply, eq_comm] using h

theorem poisson_kernel_mass : Expected.PoissonNormRecovery.kernelMass := by
  intro T hT r hr hr1
  have hc := poisson_continuous T hr hr1
  refine ⟨hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  have hint : ∀ k : ℤ,
      Integrable (fun x : Circle T => (r ^ k.natAbs : ℂ) * mode T k x) (haar T) := by
    intro k
    exact ((mode T k).continuous.const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm : Summable (fun k : ℤ =>
      ∫ x : Circle T, ‖(r ^ k.natAbs : ℂ) * mode T k x‖ ∂haar T) := by
    simpa [norm_mul, norm_pow, mode_norm, abs_of_nonneg hr] using
      summable_poisson_weights hr hr1
  have h := (integral_tsum_of_summable_integral_norm hint hnorm).symm
  have hs : (fun x : Circle T => ∑' k : ℤ, (r ^ k.natAbs : ℂ) * mode T k x) =
      (fun x => (poissonKernel T r x : ℂ)) := by
    funext x
    exact (poisson_hasSum T hr hr1 x).tsum_eq
  rw [hs, integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  change ((∫ x, poissonKernel T r x ∂haar T : ℝ) : ℂ) = 1
  rw [h]
  simp only [integral_const_mul, integral_mode]
  simp

omit [Fact (0 < T)] in
private lemma mode_sub (k : ℤ) (x y : Circle T) :
    mode T k (x - y) = mode T k x * conj (mode T k y) := by
  simp only [mode, fourier_apply, sub_eq_add_neg, smul_add, smul_neg,
    AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul, Circle.coe_inv_eq_conj]

lemma convolution_mode {f : Circle T → ℂ} (k : ℤ) (x : Circle T) :
    (∫ y, f (x - y) * mode T k y ∂haar T) = coefficient T f k * mode T k x := by
  rw [← integral_sub_left_eq_self (fun y => f (x - y) * mode T k y) (haar T) x]
  simp only [sub_sub_cancel, mode_sub]
  simp_rw [← mul_assoc]
  unfold coefficient
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by ring

theorem abel_convolution : Expected.PoissonNormRecovery.abelConvolution := by
  intro T hT r hr hr1 f hf x
  have hc : Continuous (fun y : Circle T => (poissonKernel T r y : ℂ)) :=
    Complex.continuous_ofReal.comp (poisson_continuous T hr hr1)
  have hp : Integrable (fun y => f (x - y) * (poissonKernel T r y : ℂ)) (haar T) := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hc.norm).bddAbove
    exact (hf.comp_sub_left x).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hC ⟨y, Set.mem_univ y, rfl⟩)
  refine ⟨hp, ?_⟩
  change abelMean T r f x = ∫ y, f (x - y) * (poissonKernel T r y : ℂ) ∂haar T
  have hi : ∀ k : ℤ, Integrable
      (fun y : Circle T => f (x - y) * ((r ^ k.natAbs : ℂ) * mode T k y)) (haar T) := by
    intro k
    convert ((hf.comp_sub_left x).fourier_smul k).const_mul (r ^ k.natAbs : ℂ) using 1
    funext y
    simp only [smul_eq_mul, mode]
    ring
  have hn : Summable (fun k : ℤ => ∫ y : Circle T,
      ‖f (x - y) * ((r ^ k.natAbs : ℂ) * mode T k y)‖ ∂haar T) := by
    simp only [norm_mul, norm_pow, mode_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr, integral_mul_const]
    exact (summable_poisson_weights hr hr1).mul_left _
  have ht := integral_tsum_of_summable_integral_norm hi hn
  have hs : ∀ y : Circle T,
      (∑' k : ℤ, f (x - y) * ((r ^ k.natAbs : ℂ) * mode T k y)) =
        f (x - y) * (poissonKernel T r y : ℂ) := by
    intro y
    rw [tsum_mul_left, (poisson_hasSum T hr hr1 y).tsum_eq]
  simp_rw [hs] at ht
  rw [← ht]
  apply tsum_congr
  intro k
  rw [show (fun y : Circle T => f (x - y) * ((r ^ k.natAbs : ℂ) * mode T k y)) =
    (fun y => (r ^ k.natAbs : ℂ) * (f (x - y) * mode T k y)) by funext y; ring,
    integral_const_mul, convolution_mode]
  ring

lemma mode_one_re_lt_one {x : Circle T} (hx : x ≠ 0) : (mode T 1 x).re < 1 := by
  have hn := mode_norm T 1 x
  have hle : (mode T 1 x).re ≤ 1 := by
    simpa only [hn] using Complex.re_le_norm (mode T 1 x)
  by_contra hlt
  have he : (mode T 1 x).re = 1 := le_antisymm hle (not_lt.mp hlt)
  have hi : (mode T 1 x).im = 0 := by
    have h := Complex.sq_norm_sub_sq_re (mode T 1 x)
    rw [hn, he] at h
    nlinarith [sq_nonneg (mode T 1 x).im]
  have hm : mode T 1 x = 1 := by
    apply Complex.ext
    · exact he
    · exact hi
  apply hx
  apply AddCircle.injective_toCircle (ne_of_gt (Fact.out : 0 < T))
  apply Subtype.coe_injective
  simpa [mode, fourier_apply] using hm

/-- A compact set avoiding zero has a uniform, strictly positive angular gap. -/
lemma poisson_gap {K : Set (Circle T)} (hK : IsCompact K) (h0 : (0 : Circle T) ∉ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ 1 - (mode T 1 x).re := by
  apply hK.exists_forall_le' (by fun_prop)
  intro x hx
  have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx
  exact sub_pos.mpr (mode_one_re_lt_one T hx0)

theorem poisson_kernel_decay : Expected.PoissonNormRecovery.kernelDecay := by
  intro T hT U hU
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV, h0V⟩
  obtain ⟨c, hc, hcb⟩ := poisson_gap T hV.isClosed_compl.isCompact (by simpa using h0V)
  have hnum : Tendsto (fun r : ℝ => (1 - r ^ 2) / c) (𝓝[<] 1) (𝓝 0) := by
    have h : ContinuousAt (fun r : ℝ => (1 - r ^ 2) / c) 1 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hnum (Metric.ball_mem_nhds 0 hε),
    self_mem_nhdsWithin, (show ∀ᶠ r : ℝ in 𝓝[<] 1, (1 / 2 : ℝ) < r from
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num)))] with r hnumr hr1 hrhalf
  intro x hx
  change dist ((1 - r ^ 2) / c) 0 < ε at hnumr
  change r < 1 at hr1
  have hxV : x ∈ Vᶜ := fun hv => hx (hVU hv)
  have hgap := hcb x hxV
  have hr : 0 ≤ r := by linarith
  have hn : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hd : c ≤ 1 - 2 * r * (mode T 1 x).re + r ^ 2 := by
    have h0 : 0 ≤ 1 - (mode T 1 x).re := hc.le.trans hgap
    nlinarith [sq_nonneg (1 - r), mul_nonneg (show 0 ≤ 2 * r - 1 by linarith) h0]
  have hp : poissonKernel T r x ≤ (1 - r ^ 2) / c :=
    div_le_div_of_nonneg_left hn hc hd
  change dist (0 : ℝ) (poissonKernel T r x) < ε
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (poisson_nonneg T hr hr1 x)]
  apply hp.trans_lt
  exact lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hnumr)

/-- Poisson kernels form an approximation of the identity for continuous maps
into every Banach space. This form also applies to translated functions. -/
lemma poisson_integral_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : C(Circle T, E)) :
    Tendsto (fun r : ℝ => ∫ y, poissonKernel T r y • g y ∂haar T)
      (𝓝[<] 1) (𝓝 (g 0)) := by
  have hparam : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)))]
      with r hr hr0
    exact ⟨hr0.le, hr⟩
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto
    (t := univ) (x₀ := (0 : Circle T)) MeasurableSet.univ (by simp) (by simp)
  · filter_upwards [hparam] with r hr x
    exact poisson_nonneg T hr.1 hr.2 x
  · intro U hU h0U
    exact poisson_kernel_decay T U (hU.mem_nhds h0U)
  · apply tendsto_const_nhds.congr'
    filter_upwards [hparam] with r hr
    rw [Measure.restrict_univ]
    exact (poisson_kernel_mass T r hr.1 hr.2).2.symm
  · filter_upwards [hparam] with r hr
    exact (poisson_continuous T hr.1 hr.2).aestronglyMeasurable
  · exact g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact g.continuous.tendsto 0

theorem abel_uniform_recovery : Expected.PoissonNormRecovery.uniformRecovery := by
  intro T hT f
  let g : C(Circle T, C(Circle T, ℂ)) :=
    ContinuousMap.curry ⟨fun p : Circle T × Circle T => f (p.2 - p.1), by fun_prop⟩
  have ht := poisson_integral_tendsto T g
  have h0 : g 0 = f := by ext x; simp [g, ContinuousMap.curry]
  rw [h0] at ht
  have hu := (ContinuousMap.tendsto_iff_tendstoUniformly).mp ht
  rw [← tendstoUniformlyOn_univ] at hu ⊢
  apply hu.congr
  have hparam : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)))]
      with r hr hr0
    exact ⟨hr0.le, hr⟩
  filter_upwards [hparam] with r hr x hx
  have hi : Integrable (fun y => poissonKernel T r y • g y) (haar T) :=
    ((poisson_continuous T hr.1 hr.2).smul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ y, poissonKernel T r y • g y ∂haar T) x = abelMean T r f x
  rw [ContinuousMap.integral_apply hi]
  have hf : Integrable (f : Circle T → ℂ) (haar T) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconv : abelMean T r f x =
      convolution T f (fun y => (poissonKernel T r y : ℂ)) x :=
    (abel_convolution T r hr.1 hr.2 f hf x).2
  rw [hconv]
  unfold convolution
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (poissonKernel T r y : ℂ) * f (x - y) = f (x - y) * (poissonKernel T r y : ℂ)
    ring

theorem abel_real_uniform_recovery : Expected.PoissonNormRecovery.realUniformRecovery := by
  intro T hT f
  exact abel_uniform_recovery T ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

lemma abel_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (f : Circle T → ℂ) :
    Continuous (abelMean T r f) := by
  apply continuous_tsum (fun k => (mode T k).continuous.const_mul _) 
    ((summable_poisson_weights hr hr1).mul_right (∫ y, ‖f y‖ ∂haar T))
  exact fun k x => abel_term_bound T hr f k x

lemma abel_memLp {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (f : Circle T → ℂ) (p : ℝ≥0∞) :
    MemLp (abelMean T r f) p (haar T) :=
  (abel_continuous T hr hr1 f).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integrable_continuous_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Circle T → E} (hf : Integrable f (haar T)) (K : C(Circle T, ℝ)) :
    Integrable (fun y => K y • f y) (haar T) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image K.continuous.norm).bddAbove
  exact hf.bdd_smul C K.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hC ⟨y, mem_univ y, rfl⟩)

lemma poisson_rpow_bound {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞)
    {f : Circle T → ℂ} (hf : MemLp f p (haar T)) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (x : Circle T) :
    ‖abelMean T r f x‖ ^ p.toReal ≤
      ∫ y, poissonKernel T r y * ‖f (x - y)‖ ^ p.toReal ∂haar T := by
  let K : C(Circle T, ℝ) := ⟨poissonKernel T r, poisson_continuous T hr hr1⟩
  have hK : ∀ y, 0 ≤ K y := poisson_nonneg T hr hr1
  let w : Circle T → ℝ≥0 := fun y => ⟨K y, hK y⟩
  have hw : Measurable w := K.continuous.measurable.subtype_mk
  let ν : Measure (Circle T) := (haar T).withDensity (fun y => (w y : ℝ≥0∞))
  have hmass : (∫ y, K y ∂haar T) = 1 := (poisson_kernel_mass T r hr hr1).2
  have : IsProbabilityMeasure ν := ⟨by
    change ((haar T).withDensity (fun y => (w y : ℝ≥0∞))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have he : (fun y => (w y : ℝ≥0∞)) = (fun y => ENNReal.ofReal (K y)) := by
      funext y
      exact ENNReal.ofReal_coe_nnreal.symm
    have hKi : Integrable (fun y => K y) (haar T) := (poisson_kernel_mass T r hr hr1).1
    rw [he, ← ofReal_integral_eq_lintegral_ofReal hKi (Filter.Eventually.of_forall hK), hmass]
    norm_num⟩
  have hnz : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hf1 : Integrable f (haar T) := hf.integrable hp
  have hfν : Integrable (fun y => f (x - y)) ν := by
    apply (integrable_withDensity_iff_integrable_smul hw).2
    exact integrable_continuous_smul T (hf1.comp_sub_left x) K
  have hnormν : Integrable (fun y => ‖f (x - y)‖) ν := hfν.norm
  have hpowν : Integrable (fun y => ‖f (x - y)‖ ^ p.toReal) ν := by
    apply (integrable_withDensity_iff_integrable_smul hw).2
    exact integrable_continuous_smul T ((hf.integrable_norm_rpow hnz hpfin).comp_sub_left x) K
  have hq : 1 ≤ p.toReal := by exact_mod_cast (ENNReal.toReal_le_toReal (by simp) hpfin).2 hp
  have hj := (convexOn_rpow hq).map_integral_le
    (by fun_prop) isClosed_Ici
    (Filter.Eventually.of_forall fun y => norm_nonneg (f (x - y))) hnormν hpowν
  have hc : (∫ y, f (x - y) ∂ν) = abelMean T r f x := by
    rw [integral_withDensity_eq_integral_smul hw]
    have hconv : abelMean T r f x = convolution T f (fun y => (K y : ℂ)) x :=
      (abel_convolution T r hr hr1 f hf1 x).2
    rw [hconv]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change (K y : ℂ) * f (x - y) = f (x - y) * (K y : ℂ)
      ring
  rw [← hc]
  apply (Real.rpow_le_rpow (norm_nonneg _) (norm_integral_le_integral_norm _) (by positivity)).trans
  apply hj.trans_eq
  rw [integral_withDensity_eq_integral_smul hw]
  rfl

lemma poisson_lp_contraction {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞)
    {f : Circle T → ℂ} (hf : MemLp f p (haar T)) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm (abelMean T r f) p (haar T) ≤ eLpNorm f p (haar T) := by
  have hnz : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hi := hf.integrable_norm_rpow hnz hpfin
  have hK := (poisson_kernel_mass T r hr hr1).1
  have hprod : Integrable (fun z : Circle T × Circle T =>
      ‖f (z.1 - z.2)‖ ^ p.toReal * poissonKernel T r z.2) ((haar T).prod (haar T)) := by
    have h := hi.mul_prod hK
    exact ((measurePreserving_sub_prod (haar T) (haar T)).integrable_comp h.aestronglyMeasurable).2 h
  have hm : (∫ x, ‖abelMean T r f x‖ ^ p.toReal ∂haar T) ≤
      ∫ x, ‖f x‖ ^ p.toReal ∂haar T := by
    calc
      _ ≤ ∫ x, ∫ y, ‖f (x - y)‖ ^ p.toReal * poissonKernel T r y ∂haar T ∂haar T := by
        apply integral_mono ((abel_memLp T hr hr1 f p).integrable_norm_rpow hnz hpfin)
          hprod.integral_prod_left
        intro x
        simpa only [mul_comm] using poisson_rpow_bound T hp hpfin hf hr hr1 x
      _ = ∫ y, ∫ x, ‖f (x - y)‖ ^ p.toReal * poissonKernel T r y ∂haar T ∂haar T :=
        integral_integral_swap hprod
      _ = ∫ x, ‖f x‖ ^ p.toReal ∂haar T := by
        simp only [integral_mul_const]
        have hint (y : Circle T) : (∫ a, ‖f (a - y)‖ ^ p.toReal ∂haar T) =
            ∫ a, ‖f a‖ ^ p.toReal ∂haar T := integral_sub_right_eq_self (fun a : Circle T => ‖f a‖ ^ p.toReal) y
        simp_rw [hint]
        rw [integral_const_mul]
        have hmass : (∫ y, poissonKernel T r y ∂haar T) = 1 := (poisson_kernel_mass T r hr hr1).2
        rw [hmass, mul_one]
  rw [(abel_memLp T hr hr1 f p).eLpNorm_eq_integral_rpow_norm hnz hpfin,
    hf.eLpNorm_eq_integral_rpow_norm hnz hpfin]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
    (integral_nonneg fun _ => by positivity) hm (by positivity))

lemma abel_sub {f g : Circle T → ℂ} (hf : Integrable f (haar T)) (hg : Integrable g (haar T))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : Circle T) :
    abelMean T r (f - g) x = abelMean T r f x - abelMean T r g x := by
  have hfg : abelMean T r (f - g) x = convolution T (f - g)
      (fun y => (poissonKernel T r y : ℂ)) x := (abel_convolution T r hr hr1 _ (hf.sub hg) x).2
  have hf' : abelMean T r f x = convolution T f (fun y => (poissonKernel T r y : ℂ)) x :=
    (abel_convolution T r hr hr1 _ hf x).2
  have hg' : abelMean T r g x = convolution T g (fun y => (poissonKernel T r y : ℂ)) x :=
    (abel_convolution T r hr hr1 _ hg x).2
  rw [hfg, hf', hg']
  unfold convolution
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub (abel_convolution T r hr hr1 _ hf x).1
    (abel_convolution T r hr hr1 _ hg x).1

lemma abel_continuous_lp_limit (p : ℝ≥0∞) (f : C(Circle T, ℂ)) :
    Tendsto (fun r => eLpNorm (fun x => abelMean T r f x - f x) p (haar T))
      (𝓝[<] 1) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  by_cases hεfin : ε = ∞
  · exact Filter.Eventually.of_forall fun r => hεfin ▸ le_top
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεfin
  have huni := Metric.tendstoUniformly_iff.mp (abel_uniform_recovery T f) ε.toReal hεpos
  filter_upwards [huni, self_mem_nhdsWithin,
    (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)))]
    with r huni hr1 hr0
  have hm : AEStronglyMeasurable (fun x => abelMean T r f x - f x) (haar T) :=
    ((abel_continuous T hr0.le hr1 f).sub f.continuous).aestronglyMeasurable
  have hb : ∀ᵐ x ∂haar T, ‖abelMean T r f x - f x‖ ≤ ε.toReal :=
    Filter.Eventually.of_forall fun x => by
      have hx : dist (f x) (abelMean T r f x) ≤ ε.toReal := (huni x).le
      simpa only [dist_eq_norm, norm_sub_rev] using hx
  have hbound := eLpNorm_le_of_ae_bound (p := p) hm hb
  simpa only [measure_univ, ENNReal.one_rpow, one_mul, ENNReal.ofReal_toReal hεfin] using hbound

set_option maxHeartbeats 600000 in
/-- The density argument is stated for all representatives with finite Lp seminorm. -/
lemma abel_memLp_limit {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞)
    {f : Circle T → ℂ} (hf : MemLp f p (haar T)) :
    Tendsto (fun r => eLpNorm (fun x => abelMean T r f x - f x) p (haar T))
      (𝓝[<] 1) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have hδ : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨g, hg, hgm⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hpfin hδ.ne'
  have hu := ENNReal.tendsto_nhds_zero.1 (abel_continuous_lp_limit T p g.toContinuousMap) (ε / 3) hδ
  filter_upwards [hu, self_mem_nhdsWithin,
    (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)))]
    with r hu hr1 hr0
  have hr : 0 ≤ r := hr0.le
  have hlin (x : Circle T) := abel_sub T (hf.integrable hp) (hgm.integrable hp) hr hr1 x
  have hdecomp : (fun x => abelMean T r f x - f x) =
      ((fun x => abelMean T r (f - g) x) + (fun x => abelMean T r g x - g x)) +
        (fun x => g x - f x) := by
    funext x
    simp only [Pi.add_apply, hlin]
    abel
  rw [hdecomp]
  calc
    _ ≤ eLpNorm ((fun x => abelMean T r (f - g) x) + (fun x => abelMean T r g x - g x)) p (haar T) +
        eLpNorm (fun x => g x - f x) p (haar T) :=
      eLpNorm_add_le
        (f := (fun x => abelMean T r (f - g) x) + (fun x => abelMean T r g x - g x))
        (g := fun x => g x - f x) hp
    _ ≤ (eLpNorm (abelMean T r (f - g)) p (haar T) +
        eLpNorm (fun x => abelMean T r g x - g x) p (haar T)) +
          eLpNorm (fun x => g x - f x) p (haar T) :=
      add_le_add (eLpNorm_add_le (μ := haar T) (f := fun x => abelMean T r (f - g) x)
        (g := fun x => abelMean T r g x - g x) hp) le_rfl
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      apply add_le_add
      · exact add_le_add ((poisson_lp_contraction T hp hpfin (hf.sub hgm) hr hr1).trans hg) hu
      · change eLpNorm ((g : Circle T → ℂ) - f) p (haar T) ≤ ε / 3
        rw [eLpNorm_sub_comm]
        exact hg
    _ = ε := ENNReal.add_thirds ε

theorem abel_lp_recovery : Expected.PoissonNormRecovery.lpRecovery := by
  intro T hT p hp hpfin f
  exact ⟨fun r hr hr1 => abel_memLp T hr hr1 f p,
    abel_memLp_limit T hp hpfin (Lp.memLp f)⟩

theorem abel_real_lp_recovery : Expected.PoissonNormRecovery.realLpRecovery := by
  intro T hT p hp hpfin f
  have hf : MemLp (fun x : Circle T => (f x : ℂ)) p (haar T) :=
    (Lp.memLp f).continuousLinearMap_comp Complex.ofRealCLM
  exact ⟨fun r hr hr1 => abel_memLp T hr hr1 _ p, abel_memLp_limit T hp hpfin hf⟩

end P102.Periodic
