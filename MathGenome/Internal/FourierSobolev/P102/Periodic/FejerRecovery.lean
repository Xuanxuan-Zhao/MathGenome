import MathGenome.Internal.FourierSobolev.P102.Periodic.Localization
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.FejerRecovery
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.FejerConcentration

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real ENNReal ComplexConjugate
set_option linter.unusedSectionVars false
namespace P102.Periodic

variable (T : ℝ) [Fact (0 < T)]

theorem fejerMean_cesaro (N : ℕ) (f : Circle T → ℂ) (x : Circle T) :
    fejerMean T N f x = (N + 1 : ℂ)⁻¹ *
      ∑ j ∈ Finset.range (N + 1), partialSum T j f x := rfl

theorem fejerKernel_positive (N : ℕ) (x : Circle T) :
    (fejerKernel T N x).im = 0 ∧ 0 ≤ (fejerKernel T N x).re := by
  constructor
  · rfl
  · change 0 ≤ (N + 1 : ℝ)⁻¹ * ‖_‖ ^ 2
    positivity

theorem fejerKernel_continuous (N : ℕ) : Continuous (fejerKernel T N) := by
  unfold fejerKernel
  exact Complex.continuous_ofReal.comp
    (continuous_const.mul ((continuous_finsetSum (Finset.range (N + 1)) (fun j _ => (mode T (j : ℤ)).continuous)).norm.pow 2))

theorem fejerKernel_angular_square (N : ℕ) (v : ℝ) :
    fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
      ((1 / (N + 1 : ℝ) * ‖∑ j ∈ Finset.range (N + 1),
        Complex.exp (Complex.I * (j : ℂ) * v)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [fejerKernel, angular_mode, Int.cast_natCast, one_div]

/-- The numerator identity holds without excluding the identity of the circle. -/
theorem sum_dirichletKernel_eq_normSquare (N : ℕ) (x : Circle T) :
    ∑ j ∈ Finset.range (N + 1), dirichletKernel T j x =
      (‖∑ j ∈ Finset.range (N + 1), mode T (j : ℤ) x‖ ^ 2 : ℝ) := by
  let S (n : ℕ) : ℂ := ∑ j ∈ Finset.range (n + 1), mode T (j : ℤ) x
  have hzero : S 0 = 1 := by simp [S, mode]
  have hsucc (n : ℕ) : S (n + 1) = S n + mode T (n + 1) x := by
    simp only [S, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  have hshift (n : ℕ) : S (n + 1) = 1 + mode T 1 x * S n := by
    change (∑ j ∈ Finset.range ((n + 1) + 1), mode T (j : ℤ) x) = _
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mode, fourier_zero,
      fourier_add, S, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hsplit (n : ℕ) : dirichletKernel T n x = S n + conj (S n) - 1 := by
    induction n with
    | zero => simp [hzero, dirichletKernel, frequencies, mode]
    | succ n ih =>
      rw [dirichletKernel_succ, ih, hsucc]
      simp only [map_add, mode, fourier_neg]
      ring
  have hsq (n : ℕ) : ∑ j ∈ Finset.range (n + 1), dirichletKernel T j x =
      S n * conj (S n) := by
    induction n with
    | zero => simp [hzero, dirichletKernel, frequencies, mode]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hsplit, hshift]
      simp only [map_add, map_mul, map_one]
      have hu : mode T 1 x * conj (mode T 1 x) = 1 := by
        rw [← fourier_neg, ← fourier_add]
        simp
      linear_combination -(S n * conj (S n)) * hu
  rw [hsq, Complex.mul_conj']
  simp only [S, Complex.ofReal_pow]

theorem fejerKernel_eq_average (N : ℕ) (x : Circle T) :
    fejerKernel T N x = (N + 1 : ℂ)⁻¹ *
      ∑ j ∈ Finset.range (N + 1), dirichletKernel T j x := by
  rw [sum_dirichletKernel_eq_normSquare]
  simp only [fejerKernel, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]

/-- Bridge to the independently proved angular finite-sum kernel. No integral
or regularity convention is involved in this pointwise identity. -/
theorem fejerKernel_eq_angular_library (N : ℕ) (v : ℝ) :
    fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
      SingleVariableAnalysis.fejerKernel N v := by
  rw [fejerKernel_angular_square]
  have h := SingleVariableAnalysis.fejerKernel_normSquare N v
  change SingleVariableAnalysis.fejerKernel N v = _ at h
  rw [h]
  simp only [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue,
    Int.cast_natCast, ← mul_assoc, div_eq_mul_inv]
  congr 1
  ring

theorem fejerKernel_outside_bound (δ : ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (N : ℕ) (v : ℝ) (hlo : δ ≤ |v|) (hhi : |v| ≤ Real.pi) :
    (fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))).re ≤
      1 / ((N + 1 : ℝ) * Real.sin (δ / 2) ^ 2) := by
  rw [fejerKernel_eq_angular_library]
  exact (SingleVariableAnalysis.fejerKernel_outside_bound δ hδ hδπ N v hlo hhi).2

/-- Finite averaging of the established Dirichlet convolution identity. -/
theorem fejerMean_eq_convolution (f : Circle T → ℂ) (hf : Integrable f (haar T))
    (N : ℕ) (x : Circle T) :
    ConvolutionExistsAt T f (fejerKernel T N) x ∧
      fejerMean T N f x = convolution T f (fejerKernel T N) x := by
  have hi (j : ℕ) : Integrable
      (fun y => f (x - y) * dirichletKernel T j y) (haar T) :=
    dirichlet_convolution_exists T f hf j x
  have hs := integrable_finsetSum (Finset.range (N + 1)) (fun j _ => hi j)
  have heq : (fun y => f (x - y) * fejerKernel T N y) =
      (fun y => (N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1),
        f (x - y) * dirichletKernel T j y) := by
    funext y
    rw [fejerKernel_eq_average, ← Finset.mul_sum]
    ring
  constructor
  · change Integrable _ _
    rw [heq]
    exact hs.const_mul _
  · unfold convolution fejerMean
    rw [heq, integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => partialSum_eq_convolution T f hf j x)

theorem integral_mode (k : ℤ) :
    (∫ x, mode T k x ∂haar T) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) k) 0
  simpa [fourierCoeff, mode, Pi.single_apply, eq_comm] using h

theorem integral_dirichletKernel (N : ℕ) :
    (∫ x, dirichletKernel T N x ∂haar T) = 1 := by
  unfold dirichletKernel
  rw [integral_finsetSum]
  · simp only [integral_mode]
    simp [frequencies]
  · intro k hk
    exact (mode T k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fejerKernel_mass (N : ℕ) : (∫ x, fejerKernel T N x ∂haar T) = 1 := by
  simp_rw [fejerKernel_eq_average]
  rw [integral_const_mul, integral_finsetSum]
  · simp only [integral_dirichletKernel, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity))
  · intro j hj
    exact (continuous_dirichletKernel T j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Unnormalized triangular coefficients, proved by adding the two endpoints. -/
theorem sum_dirichletKernel_eq_triangular (N : ℕ) (x : Circle T) :
    ∑ j ∈ Finset.range (N + 1), dirichletKernel T j x =
      ∑ k ∈ frequencies N, (((N + 1 : ℝ) - k.natAbs : ℝ) : ℂ) * mode T k x := by
  induction N with
  | zero => simp [dirichletKernel, frequencies, mode]
  | succ N ih =>
    let w (k : ℤ) : ℂ := (((N + 1 + 1 : ℝ) - k.natAbs : ℝ) : ℂ) * mode T k x
    have he := Finset.sum_Icc_succ_eq_add_endpoints w (N := N)
    change (∑ k ∈ frequencies (N + 1), w k) =
      w ((N : ℤ) + 1) + w (-((N : ℤ) + 1)) + ∑ k ∈ frequencies N, w k at he
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    change _ = ∑ k ∈ frequencies (N + 1), w k
    rw [he]
    have ha : ((N : ℤ) + 1).natAbs = N + 1 := by
      rw [show (N : ℤ) + 1 = ((N + 1 : ℕ) : ℤ) by simp]
      exact Int.natAbs_natCast _
    have hp : w ((N : ℤ) + 1) = mode T (N + 1) x := by
      simp only [w, ha, Nat.cast_add, Nat.cast_one]
      push_cast
      ring
    have hn : w (-((N : ℤ) + 1)) = mode T (-(N + 1)) x := by
      simp only [w, Int.natAbs_neg, ha, Nat.cast_add, Nat.cast_one]
      push_cast
      ring
    rw [hp, hn, dirichletKernel_succ]
    have hw : (∑ k ∈ frequencies N, w k) =
        (∑ k ∈ frequencies N, (((N + 1 : ℝ) - k.natAbs : ℝ) : ℂ) * mode T k x) +
        dirichletKernel T N x := by
      rw [dirichletKernel, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k hk => by dsimp [w]; push_cast; ring)
    rw [hw]
    ring

theorem fejerKernel_expansion (N : ℕ) (x : Circle T) :
    fejerKernel T N x = ∑ k ∈ frequencies N,
      ((1 - (k.natAbs : ℝ) / (N + 1 : ℝ) : ℝ) : ℂ) * mode T k x := by
  rw [fejerKernel_eq_average, sum_dirichletKernel_eq_triangular, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hn : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  push_cast
  field_simp

/-- Every finite combination supported in the specified frequency interval has
at most that degree, in the shared finite-support definition. -/
theorem finite_modes_mem_degree (N : ℕ) (a : ℤ → ℂ) :
    (∑ k ∈ frequencies N, a k • mode T k) ∈ complexTrigDegree T N := by
  classical
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  refine ⟨Finsupp.single k 1, ?_, ?_⟩
  · exact Finsupp.single_mem_supported ℂ 1 (Finset.mem_Icc.mp hk)
  · simp [synthesis, Finsupp.linearCombination_single]

theorem fejerKernel_degree (N : ℕ) :
    ∃ K : C(Circle T, ℂ), K ∈ complexTrigDegree T N ∧
      ∀ x, K x = fejerKernel T N x := by
  refine ⟨∑ k ∈ frequencies N,
    ((1 - (k.natAbs : ℝ) / (N + 1 : ℝ) : ℝ) : ℂ) • mode T k,
    finite_modes_mem_degree T N _, ?_⟩
  intro x
  simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] using
    (fejerKernel_expansion T N x).symm

theorem fejerMean_degree (N : ℕ) (f : Circle T → ℂ) :
    ∃ P : C(Circle T, ℂ), P ∈ complexTrigDegree T N ∧
      ∀ x, P x = fejerMean T N f x := by
  classical
  let P (j : ℕ) : C(Circle T, ℂ) :=
    ∑ k ∈ frequencies j, coefficient T f k • mode T k
  have hP (j : ℕ) (hj : j ∈ Finset.range (N + 1)) : P j ∈ complexTrigDegree T N := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    have hkN : k ∈ Set.Icc (-(N : ℤ)) (N : ℤ) := by
      have hkj := Finset.mem_Icc.mp hk
      have hjN := Finset.mem_range.mp hj
      constructor <;> omega
    refine ⟨Finsupp.single k 1, Finsupp.single_mem_supported ℂ 1 hkN, ?_⟩
    simp [synthesis, Finsupp.linearCombination_single]
  refine ⟨(N + 1 : ℂ)⁻¹ • ∑ j ∈ Finset.range (N + 1), P j,
    Submodule.smul_mem _ _ (Submodule.sum_mem _ hP), ?_⟩
  intro x
  simp [P, fejerMean, partialSum]

theorem positive_mode_sum_mul (N : ℕ) (x : Circle T) :
    (∑ j ∈ Finset.range (N + 1), mode T (j : ℤ) x) * (mode T 1 x - 1) =
      mode T (N + 1) x - 1 := by
  induction N with
  | zero => simp [mode]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have he : mode T (↑N + 1) x * mode T 1 x = mode T (↑N + 1 + 1) x :=
      fourier_add.symm
    rw [mul_sub, he, mul_one]
    ring

/-- Compactness away from zero bounds the inverse geometric denominator. -/
theorem fejerKernel_bound_off_neighborhood (U : Set (Circle T))
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (x : Circle T), x ∉ U →
      (fejerKernel T N x).re ≤ (N + 1 : ℝ)⁻¹ * C := by
  have hn (x : Circle T) (hx : x ∈ Uᶜ) : mode T 1 x - 1 ≠ 0 := by
    rw [sub_ne_zero, ne_eq, mode_one_eq_one_iff]
    exact fun he => hx (he ▸ h0)
  have hc : ContinuousOn (fun x : Circle T => (mode T 1 x - 1)⁻¹) Uᶜ :=
    ((mode T 1).continuous.sub continuous_const).continuousOn.inv₀ hn
  obtain ⟨B, hB⟩ := hU.isClosed_compl.isCompact.exists_bound_of_continuousOn hc
  refine ⟨(2 * max B 0) ^ 2, sq_nonneg _, ?_⟩
  intro N x hx
  have hS : (∑ j ∈ Finset.range (N + 1), mode T (j : ℤ) x) =
      (mode T (N + 1) x - 1) * (mode T 1 x - 1)⁻¹ := by
    rw [← positive_mode_sum_mul T N x, mul_inv_cancel_right₀ (hn x hx)]
  have hb : ‖∑ j ∈ Finset.range (N + 1), mode T (j : ℤ) x‖ ≤ 2 * max B 0 := by
    rw [hS, norm_mul]
    apply mul_le_mul _ ((hB x hx).trans (le_max_left B 0)) (norm_nonneg _) (by positivity)
    calc
      ‖mode T (N + 1) x - 1‖ ≤ ‖mode T (N + 1) x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [show ‖mode T (N + 1) x‖ = 1 from Circle.norm_coe _]; norm_num
  change (N + 1 : ℝ)⁻¹ * ‖_‖ ^ 2 ≤ _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (by positivity)

theorem fejerKernel_concentration (U : Set (Circle T)) (hU : U ∈ 𝓝 (0 : Circle T)) :
    Tendsto (fun N : ℕ => ∫ x in Uᶜ, (fejerKernel T N x).re ∂haar T) atTop (𝓝 0) := by
  obtain ⟨V, hVU, hV, h0⟩ := mem_nhds_iff.mp hU
  obtain ⟨C, hC, hb⟩ := fejerKernel_bound_off_neighborhood T V hV h0
  have hi (N : ℕ) : Integrable (fun x => (fejerKernel T N x).re) (haar T) :=
    (Complex.continuous_re.comp (fejerKernel_continuous T N)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbound (N : ℕ) : (∫ x in Uᶜ, (fejerKernel T N x).re ∂haar T) ≤
      (N + 1 : ℝ)⁻¹ * C := by
    calc
      _ ≤ ∫ _ in Uᶜ, (N + 1 : ℝ)⁻¹ * C ∂haar T := by
        apply integral_mono_ae (hi N).restrict (integrable_const _)
        have hsub : Uᶜ ⊆ Vᶜ := compl_subset_compl.mpr hVU
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
          (ae_restrict_mem (μ := haar T) hV.measurableSet.compl)] with x hx
        exact hb N x hx
      _ = (haar T).real Uᶜ * ((N + 1 : ℝ)⁻¹ * C) := by simp
      _ ≤ 1 * ((N + 1 : ℝ)⁻¹ * C) := by
        apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) hC)
        exact measureReal_le_one
      _ = _ := one_mul _
  have hlim : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹ * C) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N => integral_nonneg (fun x => (fejerKernel_positive T N x).2)) hbound

theorem fejerKernel_angular_expansion (N : ℕ) (v : ℝ) :
    fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
      ∑ k ∈ frequencies N, ((1 - (k.natAbs : ℝ) / (N + 1 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * k * v) := by
  rw [fejerKernel_expansion]
  simp only [angular_mode]

/-- The canonical finite-support definition agrees with the Fourier span. -/
theorem complexTrigPolynomials_eq_span :
    complexTrigPolynomials T = Submodule.span ℂ (Set.range (mode T)) :=
  Finsupp.range_linearCombination ℂ

theorem trig_uniform_density_complex (f : C(Circle T, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P ∈ complexTrigPolynomials T, ‖P - f‖ < ε := by
  have hd : Dense (complexTrigPolynomials T : Set C(Circle T, ℂ)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, complexTrigPolynomials_eq_span]
    exact span_fourier_closure_eq_top
  obtain ⟨P, hP, he⟩ := hd.exists_dist_lt f hε
  exact ⟨P, hP, by simpa only [dist_eq_norm, norm_sub_rev] using he⟩

/-- Reflection and conjugation preserve finite support. -/
def conjugateReflection (c : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.equivMapDomain (Equiv.neg ℤ) (c.mapRange conj (map_zero _))

@[simp] theorem conjugateReflection_apply (c : ℤ →₀ ℂ) (k : ℤ) :
    conjugateReflection c k = conj (c (-k)) := rfl

theorem synthesis_conjugateReflection (c : ℤ →₀ ℂ) (x : Circle T) :
    synthesis T (conjugateReflection c) x = conj (synthesis T c x) := by
  rw [synth_sum]
  change (conjugateReflection c).sum (fun k a => a * mode T k x) = _
  rw [conjugateReflection, Finsupp.sum_equivMapDomain,
    Finsupp.sum_mapRange_index (fun k => zero_mul _)]
  simp only [Equiv.neg_apply, mode, fourier_neg, ← map_mul]
  simpa only [synth_sum, mode, Finsupp.sum] using
    (map_sum conj (fun k => c k * fourier k x) c.support).symm

def symmetricPart (c : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  (1 / 2 : ℝ) • (c + conjugateReflection c)

theorem symmetricPart_mem (c : ℤ →₀ ℂ) : symmetricPart c ∈ symmetricCoefficients := by
  intro k
  simp only [symmetricPart, Finsupp.smul_apply, Finsupp.add_apply,
    conjugateReflection_apply, neg_neg, Complex.real_smul, map_mul, map_add,
    Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem synthesis_symmetricPart (c : ℤ →₀ ℂ) (x : Circle T) :
    synthesis T (symmetricPart c) x = ((synthesis T c x).re : ℂ) := by
  have hs : symmetricPart c = (1 / 2 : ℂ) • (c + conjugateReflection c) := by
    ext k
    simp [symmetricPart, Complex.real_smul]
  rw [hs, map_smul, map_add]
  simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul,
    synthesis_conjugateReflection]
  apply Complex.ext <;> simp
  ring

/-- Taking real parts yields an approximant in the symmetric-coefficient space. -/
theorem realPart_mem_realTrigPolynomials (P : C(Circle T, ℂ))
    (hP : P ∈ complexTrigPolynomials T) :
    (⟨fun x => (P x).re, Complex.continuous_re.comp P.continuous⟩ : C(Circle T, ℝ)) ∈
      realTrigPolynomials T := by
  obtain ⟨c, rfl⟩ := hP
  refine ⟨symmetricPart c, symmetricPart_mem c, ?_⟩
  ext x
  change (synthesis T (symmetricPart c) x).re = _
  rw [synthesis_symmetricPart, Complex.ofReal_re]
  rfl

theorem trig_uniform_density_real (f : C(Circle T, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P ∈ realTrigPolynomials T, ‖P - f‖ < ε := by
  let fc : C(Circle T, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  obtain ⟨P, hP, he⟩ := trig_uniform_density_complex T fc ε hε
  let Q : C(Circle T, ℝ) := ⟨fun x => (P x).re, Complex.continuous_re.comp P.continuous⟩
  refine ⟨Q, realPart_mem_realTrigPolynomials T P hP, lt_of_le_of_lt ?_ he⟩
  apply (ContinuousMap.norm_le _ (norm_nonneg (P - fc))).mpr
  intro x
  calc
    ‖(Q - f) x‖ = |(P x - fc x).re| := rfl
    _ ≤ ‖P x - fc x‖ := Complex.abs_re_le_norm _
    _ ≤ ‖P - fc‖ := (P - fc).norm_coe_le_norm x


theorem mode_re_im (k : ℤ) (t : ℝ) :
    (mode T k (t : Circle T)).re = Real.cos (2 * Real.pi * k * t / T) ∧
    (mode T k (t : Circle T)).im = Real.sin (2 * Real.pi * k * t / T) := by
  rw [mode_formula]
  have he : 2 * (Real.pi : ℂ) * Complex.I * k * t / T =
      ((2 * Real.pi * k * t / T : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he]
  simp [Complex.exp_re, Complex.exp_im]

theorem real_trig_sine_cosine (P : C(Circle T, ℝ)) (hP : P ∈ realTrigPolynomials T) :
    ∃ (N : ℕ) (a b : ℤ → ℝ), ∀ t : ℝ,
      P (t : Circle T) = ∑ k ∈ frequencies N,
        (a k * Real.cos (2 * Real.pi * k * t / T) +
         b k * Real.sin (2 * Real.pi * k * t / T)) := by
  classical
  obtain ⟨c, hc, rfl⟩ := hP
  let N := c.support.sup Int.natAbs
  have hs : c.support ⊆ frequencies N := by
    intro k hk
    have h := Finset.le_sup (f := Int.natAbs) hk
    have h1 := Int.le_natAbs (a := k)
    have h2 := Int.le_natAbs (a := -k)
    simp only [Int.natAbs_neg] at h2
    exact Finset.mem_Icc.mpr (by constructor <;> omega)
  refine ⟨N, fun k => (c k).re, fun k => -(c k).im, ?_⟩
  intro t
  change (synthesis T c (t : Circle T)).re = _
  rw [synth_sum, Complex.re_sum]
  rw [Finset.sum_subset hs]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Complex.mul_re, (mode_re_im T k t).1, (mode_re_im T k t).2]
    ring
  · intro k hk hkc
    simp [Finsupp.notMem_support_iff.mp hkc]

theorem sine_cosine_uniform_density (f : C(Circle T, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (a b : ℤ → ℝ), ∀ t : ℝ,
      |(∑ k ∈ frequencies N, (a k * Real.cos (2 * Real.pi * k * t / T) +
        b k * Real.sin (2 * Real.pi * k * t / T))) - f (t : Circle T)| < ε := by
  obtain ⟨P, hP, he⟩ := trig_uniform_density_real T f ε hε
  obtain ⟨N, a, b, h⟩ := real_trig_sine_cosine T P hP
  refine ⟨N, a, b, ?_⟩
  intro t
  rw [← h]
  exact lt_of_le_of_lt ((P - f).norm_coe_le_norm (t : Circle T)) he

/-- A uniformly dense linear space of continuous functions is dense in each
finite Lp space. This uses the same probability Haar measure and representatives. -/
theorem lp_approx_of_uniform_dense {𝕜 : Type} [RCLike 𝕜]
    (S : Submodule 𝕜 C(Circle T, 𝕜)) (hd : Dense (S : Set C(Circle T, 𝕜)))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → 𝕜) (hf : MemLp f p (haar T)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P ∈ S, eLpNorm (fun x => P x - f x) p (haar T) < ENNReal.ofReal ε := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  let L := ContinuousMap.toLp p (haar T) 𝕜 (E := 𝕜)
  have hL : DenseRange L := continuous_density T 𝕜 p hfin
  have hSL : DenseRange (fun P : S => L P) :=
    hL.comp hd.denseRange_val L.continuous
  obtain ⟨P, he⟩ := hSL.exists_dist_lt (hf.toLp f) hε
  refine ⟨P, P.property, ?_⟩
  have hed : edist (L P) (hf.toLp f) = eLpNorm (fun x => (P : C(Circle T, 𝕜)) x - f x) p (haar T) := by
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    exact ((ContinuousMap.coeFn_toLp (haar T) (𝕜 := 𝕜) (p := p)
      (P : C(Circle T, 𝕜))).sub hf.coeFn_toLp)
  rw [← hed, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by rwa [dist_comm])

theorem trig_lp_density_complex (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → ℂ) (hf : MemLp f p (haar T)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P ∈ complexTrigPolynomials T,
      eLpNorm (fun x => P x - f x) p (haar T) < ENNReal.ofReal ε := by
  apply lp_approx_of_uniform_dense T _ ?_ p hp hfin f hf ε hε
  rw [Submodule.dense_iff_topologicalClosure_eq_top, complexTrigPolynomials_eq_span]
  exact span_fourier_closure_eq_top

theorem trig_lp_density_real (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → ℝ) (hf : MemLp f p (haar T)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P ∈ realTrigPolynomials T,
      eLpNorm (fun x => P x - f x) p (haar T) < ENNReal.ofReal ε := by
  apply lp_approx_of_uniform_dense T _ ?_ p hp hfin f hf ε hε
  intro g
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨P, hP, he⟩ := trig_uniform_density_real T g δ hδ
  exact ⟨P, hP, by simpa only [dist_eq_norm, norm_sub_rev] using he⟩


theorem fejerKernel_integrable (N : ℕ) : Integrable (fejerKernel T N) (haar T) :=
  (fejerKernel_continuous T N).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fejerKernel_re_mass (N : ℕ) :
    (∫ x, (fejerKernel T N x).re ∂haar T) = 1 := by
  change (∫ x, RCLike.re (fejerKernel T N x) ∂haar T) = 1
  rw [integral_re (fejerKernel_integrable T N), fejerKernel_mass]
  rfl

/-- Regard all translates at once as a continuous-map-valued function. -/
def translateContinuous (f : C(Circle T, ℂ)) (y : Circle T) : C(Circle T, ℂ) :=
  ⟨fun x => f (x - y), f.continuous.comp (continuous_id.sub continuous_const)⟩

theorem continuous_translateContinuous (f : C(Circle T, ℂ)) :
    Continuous (translateContinuous T f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.sub continuous_fst)

theorem fejerKernel_uniform_off_neighborhood (U : Set (Circle T))
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    TendstoUniformlyOn (fun N x => (fejerKernel T N x).re) 0 atTop Uᶜ := by
  obtain ⟨C, hC, hb⟩ := fejerKernel_bound_off_neighborhood T U hU h0
  have hlim : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹ * C) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const C
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with N hN x hx
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (fejerKernel_positive T N x).2] using (hb N x hx).trans_lt hN

theorem integral_fejer_translate (f : C(Circle T, ℂ)) (N : ℕ) (x : Circle T) :
    (∫ y, (fejerKernel T N y).re • translateContinuous T f y ∂haar T) x =
      fejerMean T N f x := by
  have hi : Integrable (fun y => (fejerKernel T N y).re • translateContinuous T f y) (haar T) :=
    ((Complex.continuous_re.comp (fejerKernel_continuous T N)).smul
      (continuous_translateContinuous T f)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [ContinuousMap.integral_apply hi,
    (fejerMean_eq_convolution T f (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) N x).2]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change (fejerKernel T N y).re • f (x - y) = f (x - y) * fejerKernel T N y
  rw [Complex.real_smul, mul_comm]
  rfl

theorem fejerMean_uniform_complex (f : C(Circle T, ℂ)) :
    TendstoUniformly (fun N => fejerMean T N f) f atTop := by
  have hg : Integrable (translateContinuous T f) (haar T) :=
    (continuous_translateContinuous T f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcg : Tendsto (translateContinuous T f) (𝓝 0) (𝓝 f) := by
    have heq : translateContinuous T f 0 = f := by ext x; simp [translateContinuous]
    simpa only [heq] using (continuous_translateContinuous T f).tendsto 0
  have hh := tendsto_integral_peak_smul_of_integrable_of_tendsto
    (μ := haar T) (φ := fun N x => (fejerKernel T N x).re)
    (t := Set.univ) MeasurableSet.univ (by simp) (measure_ne_top _ _)
    (Eventually.of_forall fun N x => (fejerKernel_positive T N x).2)
    (fun U hU h0 => fejerKernel_uniform_off_neighborhood T U hU h0)
    (by simpa only [Measure.restrict_univ, fejerKernel_re_mass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
    (Eventually.of_forall fun N => (fejerKernel_integrable T N).re.aestronglyMeasurable)
    hg hcg
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hh) ε hε] with N hN x
  rw [dist_comm, dist_eq_norm, ← integral_fejer_translate T f N x]
  exact (( (∫ y, (fejerKernel T N y).re • translateContinuous T f y ∂haar T) - f
    ).norm_coe_le_norm x).trans_lt (by simpa only [dist_eq_norm] using hN)

/-- Real inputs stay real, even for arbitrary integrable representatives. -/
theorem fejerMean_real_im (f : Circle T → ℝ) (hf : Integrable f (haar T)) (N : ℕ)
    (x : Circle T) : (fejerMean T N (fun y => (f y : ℂ)) x).im = 0 := by
  have hfc : Integrable (fun y => (f y : ℂ)) (haar T) := hf.ofReal
  rw [(fejerMean_eq_convolution T _ hfc N x).2]
  unfold convolution
  change RCLike.im (∫ y, (f (x - y) : ℂ) * fejerKernel T N y ∂haar T) = 0
  rw [← integral_im (fejerMean_eq_convolution T _ hfc N x).1]
  change (∫ y, ((f (x - y) : ℂ) * fejerKernel T N y).im ∂haar T) = 0
  simp only [Complex.mul_im, Complex.ofReal_im, (fejerKernel_positive T N _).1,
    mul_zero, zero_mul, add_zero, integral_zero]

theorem fejerMean_uniform_real (f : C(Circle T, ℝ)) :
    (∀ N x, (fejerMean T N (fun y => (f y : ℂ)) x).im = 0) ∧
    TendstoUniformly (fun N x => (fejerMean T N (fun y => (f y : ℂ)) x).re) f atTop := by
  constructor
  · exact fejerMean_real_im T f (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  · let fc : C(Circle T, ℂ) :=
      ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp (fejerMean_uniform_complex T fc)) ε hε]
      with N hN x
    calc
      dist (f x) (fejerMean T N (fun y => (f y : ℂ)) x).re =
          |(fc x - fejerMean T N fc x).re| := rfl
      _ ≤ ‖fc x - fejerMean T N fc x‖ := Complex.abs_re_le_norm _
      _ < ε := by simpa only [dist_eq_norm] using hN x


/-- The probability measure used in Jensen's inequality. -/
def fejerMeasure (N : ℕ) : Measure (Circle T) :=
  (haar T).withDensity (fun x => ENNReal.ofReal (fejerKernel T N x).re)

instance fejerMeasure_probability (N : ℕ) : IsProbabilityMeasure (fejerMeasure T N) := by
  constructor
  have hi : Integrable (fun y => (fejerKernel T N y).re) (haar T) :=
    (fejerKernel_integrable T N).re
  rw [fejerMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (fun x => (fejerKernel_positive T N x).2)), fejerKernel_re_mass,
    ENNReal.ofReal_one]

/-- The probability-space L1-to-Lp comparison gives Jensen's power inequality,
including p=1 and allowing an infinite right hand side. -/
theorem enorm_integral_rpow_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (g : α → ℂ) (hg : AEStronglyMeasurable g ν) :
    ‖∫ y, g y ∂ν‖ₑ ^ p.toReal ≤ ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂ν := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hfin
  calc
    _ ≤ (eLpNorm g p ν) ^ p.toReal :=
      ENNReal.rpow_le_rpow ((enorm_integral_le_lintegral_enorm g).trans
        (lintegral_enorm_le_eLpNorm_one.trans (eLpNorm_le_eLpNorm_of_exponent_le hp))) hq.le
    _ = _ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hfin hg,
        ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

theorem fejerMean_eq_integral_fejerMeasure (f : Circle T → ℂ)
    (hf : Integrable f (haar T)) (N : ℕ) (x : Circle T) :
    fejerMean T N f x = ∫ y, f (x - y) ∂fejerMeasure T N := by
  have hm : Measurable (fun y => ENNReal.ofReal (fejerKernel T N y).re) :=
    (Complex.continuous_re.comp (fejerKernel_continuous T N)).measurable.ennreal_ofReal
  rw [fejerMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun y => ENNReal.ofReal_lt_top)),
    (fejerMean_eq_convolution T f hf N x).2]
  unfold convolution
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  rw [ENNReal.toReal_ofReal (fejerKernel_positive T N y).2, Complex.real_smul, mul_comm]
  rfl

theorem fejerMean_memLp (p : ℝ≥0∞) (hp : 1 ≤ p) (N : ℕ) (f : Circle T → ℂ) :
    MemLp (fejerMean T N f) p (haar T) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨P, hP, he⟩ := fejerMean_degree T N f
  have hPe : (P : Circle T → ℂ) = fejerMean T N f := funext he
  rw [← hPe]
  exact P.memLp (haar T) ℂ

theorem fejerMean_contraction_complex (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → ℂ) (hf : MemLp f p (haar T)) (N : ℕ) :
    MemLp (fejerMean T N f) p (haar T) ∧
      eLpNorm (fejerMean T N f) p (haar T) ≤ eLpNorm f p (haar T) := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hfin
  have hfm := fejerMean_memLp T p hp N f
  refine ⟨hfm, ?_⟩
  have hj (x : Circle T) :
      ‖fejerMean T N f x‖ₑ ^ p.toReal ≤
        ∫⁻ y, ‖f (x - y)‖ₑ ^ p.toReal ∂fejerMeasure T N := by
    rw [fejerMean_eq_integral_fejerMeasure T f (hf.integrable hp)]
    apply enorm_integral_rpow_le _ p hp hfin
    exact (hf.integrable hp).comp_sub_left x |>.aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hjoint : AEMeasurable (fun z : Circle T × Circle T => ‖f (z.1 - z.2)‖ₑ ^ p.toReal)
      ((haar T).prod (fejerMeasure T N)) :=
    (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (haar T) (fejerMeasure T N))).enorm.pow_const _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hfin hfm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hfin hf.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖f (x - y)‖ₑ ^ p.toReal ∂fejerMeasure T N ∂haar T :=
      lintegral_mono hj
    _ = ∫⁻ y, ∫⁻ x, ‖f (x - y)‖ₑ ^ p.toReal ∂haar T ∂fejerMeasure T N :=
      lintegral_lintegral_swap hjoint
    _ = _ := by
      simp_rw [lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ p.toReal)]
      simp


/-- Complexification is isometric for the actual Lp seminorm. -/
theorem eLpNorm_complexify (p : ℝ≥0∞) (f : Circle T → ℝ)
    (hf : AEStronglyMeasurable f (haar T)) :
    eLpNorm (fun x => (f x : ℂ)) p (haar T) = eLpNorm f p (haar T) :=
  eLpNorm_congr_norm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hf) hf
    (ae_of_all _ (fun _x => Complex.norm_real _))

theorem fejerMean_contraction_real (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → ℝ) (hf : MemLp f p (haar T)) (N : ℕ) :
    MemLp (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re) p (haar T) ∧
    eLpNorm (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re) p (haar T) ≤
      eLpNorm f p (haar T) := by
  obtain ⟨hm, hb⟩ := fejerMean_contraction_complex T p hp hfin
    (fun y => (f y : ℂ)) hf.ofReal N
  have hr : MemLp (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re) p (haar T) := hm.re
  refine ⟨hr, ?_⟩
  calc
    _ ≤ eLpNorm (fejerMean T N (fun y => (f y : ℂ))) p (haar T) :=
      eLpNorm_mono hr.aestronglyMeasurable (fun x => Complex.abs_re_le_norm _)
    _ ≤ _ := hb.trans_eq (eLpNorm_complexify T p f hf.aestronglyMeasurable)

theorem fejerMean_sub (N : ℕ) (f g : Circle T → ℂ)
    (hf : Integrable f (haar T)) (hg : Integrable g (haar T)) :
    fejerMean T N (f - g) = fejerMean T N f - fejerMean T N g := by
  ext x
  simp only [Pi.sub_apply]
  rw [(fejerMean_eq_convolution T _ (hf.sub hg) N x).2,
    (fejerMean_eq_convolution T _ hf N x).2, (fejerMean_eq_convolution T _ hg N x).2]
  simp only [convolution, Pi.sub_apply, sub_mul]
  exact integral_sub (fejerMean_eq_convolution T _ hf N x).1
    (fejerMean_eq_convolution T _ hg N x).1


theorem fejerMean_lp_complex (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → ℂ) (hf : MemLp f p (haar T)) :
    Tendsto (fun N => eLpNorm (fun x => fejerMean T N f x - f x) p (haar T)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (3 : ℝ≥0∞)) (by norm_num) hε.ne'
  obtain ⟨g, hg, hgm⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hfin
    (show (δ : ℝ≥0∞) ≠ 0 from (ENNReal.coe_pos.mpr hδ).ne')
  have hδr : (0 : ℝ) < δ := hδ
  have hu := (Metric.tendstoUniformly_iff.mp
    (fejerMean_uniform_complex T g.toContinuousMap)) (δ : ℝ) hδr
  filter_upwards [hu] with N hN
  change ∀ x, dist (g x) (fejerMean T N g x) < (δ : ℝ) at hN
  have hs : (fun x => fejerMean T N f x - f x) =
      (fejerMean T N (f - (g : Circle T → ℂ))) + (fun x => fejerMean T N g x - g x) + (fun x => g x - f x) := by
    rw [fejerMean_sub T N f g (hf.integrable hp) (hgm.integrable hp)]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hb : eLpNorm (fun x => fejerMean T N g x - g x) p (haar T) ≤ δ := by
    change eLpNorm (fejerMean T N g - (g : Circle T → ℂ)) p (haar T) ≤ δ
    have hm := ((fejerMean_memLp T p hp N g).sub hgm).aestronglyMeasurable
    have hh := eLpNorm_le_of_ae_bound (p := p) hm (ae_of_all _ (fun x => (show
      ‖fejerMean T N g x - g x‖ < (δ : ℝ) by simpa only [dist_eq_norm, norm_sub_rev] using hN x).le))
    simpa only [measure_univ, ENNReal.one_rpow, one_mul, ENNReal.ofReal_coe_nnreal] using hh
  have hc : eLpNorm (fun x => g x - f x) p (haar T) ≤ δ := by
    have he : (fun x => g x - f x) = -(f - (g : Circle T → ℂ)) := by ext x; simp
    rw [he, eLpNorm_neg]
    exact hg
  have ha : eLpNorm (fejerMean T N (f - (g : Circle T → ℂ))) p (haar T) ≤ δ :=
    (fejerMean_contraction_complex T p hp hfin (f - (g : Circle T → ℂ)) (hf.sub hgm) N).2.trans hg
  let a : Circle T → ℂ := fejerMean T N (f - (g : Circle T → ℂ))
  let b : Circle T → ℂ := fun x => fejerMean T N g x - g x
  let c : Circle T → ℂ := fun x => g x - f x
  have hsum : eLpNorm (a + b + c) p (haar T) ≤
      (eLpNorm a p (haar T) + eLpNorm b p (haar T)) + eLpNorm c p (haar T) := by
    exact (eLpNorm_add_le (f := a + b) (g := c) hp).trans
      (add_le_add (eLpNorm_add_le (f := a) (g := b) hp) le_rfl)
  have htotal : eLpNorm (a + b + c) p (haar T) ≤ (δ : ℝ≥0∞) + δ + δ :=
    hsum.trans (add_le_add (add_le_add ha hb) hc)
  have he : (δ : ℝ≥0∞) + δ + δ = (δ : ℝ≥0∞) * 3 := by ring
  have hnorm : eLpNorm (fun x => fejerMean T N f x - f x) p (haar T) =
      eLpNorm (a + b + c) p (haar T) :=
    congrArg (fun h : Circle T → ℂ => eLpNorm h p (haar T)) hs
  exact hnorm.le.trans (htotal.trans (he.le.trans hδε.le))

theorem fejerMean_lp_real (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ∞)
    (f : Circle T → ℝ) (hf : MemLp f p (haar T)) :
    Tendsto (fun N => eLpNorm
      (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re - f x) p (haar T)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp
    (fejerMean_lp_complex T p hp hfin (fun y => (f y : ℂ)) hf.ofReal) ε hε] with N hN
  have hm := ((fejerMean_contraction_real T p hp hfin f hf N).1.sub hf).aestronglyMeasurable
  refine (eLpNorm_mono hm (fun x => ?_)).trans hN
  change |(fejerMean T N (fun y => (f y : ℂ)) x).re - f x| ≤ _
  simpa only [Complex.sub_re, Complex.ofReal_re] using
    Complex.abs_re_le_norm (fejerMean T N (fun y => (f y : ℂ)) x - (f x : ℂ))

end P102.Periodic
