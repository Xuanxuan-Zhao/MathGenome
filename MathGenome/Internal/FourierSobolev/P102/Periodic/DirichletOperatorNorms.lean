import MathGenome.Internal.FourierSobolev.P102.Periodic.Localization
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.DirichletOperatorNorms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace P102.Periodic

/-- The weighted integral is bounded by the L¹ norm of its continuous weight. -/
theorem norm_weightedIntegral_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    (h f : C(K, ℝ)) :
    ‖∫ y, f y * h y ∂μ‖ ≤ (∫ y, |h y| ∂μ) * ‖f‖ := by
  calc
    _ ≤ ∫ y, ‖f y * h y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, |h y| * ‖f‖ ∂μ := by
      apply integral_mono
      · exact (f.continuous.mul h.continuous).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (h.continuous.abs.mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro y
        simp only [norm_mul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (f.norm_coe_le_norm y) (abs_nonneg _)).trans_eq
          (mul_comm _ _)
    _ = _ := integral_mul_const _ _

/-- Integration against a real continuous density on a compact probability space. -/
def weightedIntegral {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    (h : C(K, ℝ)) : C(K, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ y, f y * h y ∂μ
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add ((f * h).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
          ((g * h).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro a f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_assoc]
        exact integral_const_mul _ _ }
    (∫ y, |h y| ∂μ) (norm_weightedIntegral_le μ h)

@[simp] theorem weightedIntegral_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    (h f : C(K, ℝ)) : weightedIntegral μ h f = ∫ y, f y * h y ∂μ := rfl

/-- Soft signs are continuous and certify the full lower operator norm bound. -/
theorem norm_weightedIntegral {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    (h : C(K, ℝ)) : ‖weightedIntegral μ h‖ = ∫ y, |h y| ∂μ := by
  apply le_antisymm
  · exact (weightedIntegral μ h).opNorm_le_bound
      (integral_nonneg fun _ => abs_nonneg _) (norm_weightedIntegral_le μ h)
  · apply le_of_forall_pos_le_add
    intro ε hε
    let f : C(K, ℝ) := ⟨fun y => h y / (|h y| + ε),
      h.continuous.div (h.continuous.abs.add continuous_const)
        (fun y => ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg _) hε))⟩
    have hf : ‖f‖ ≤ 1 := by
      apply (ContinuousMap.norm_le f (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro y
      change |h y / (|h y| + ε)| ≤ 1
      rw [abs_div, abs_of_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) hε)]
      exact (div_le_one (add_pos_of_nonneg_of_pos (abs_nonneg _) hε)).mpr (by linarith)
    have hpoint (y : K) : |h y| ≤ f y * h y + ε := by
      change |h y| ≤ h y / (|h y| + ε) * h y + ε
      have hden : 0 < |h y| + ε := add_pos_of_nonneg_of_pos (abs_nonneg _) hε
      apply (mul_le_mul_iff_of_pos_right hden).mp
      field_simp
      nlinarith [sq_abs (h y), abs_nonneg (h y)]
    have hint : (∫ y, |h y| ∂μ) ≤ weightedIntegral μ h f + ε := by
      have hi : Integrable (fun y => f y * h y) μ :=
        (f * h).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc
        _ ≤ ∫ y, f y * h y + ε ∂μ := integral_mono
          (h.continuous.abs.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          (hi.add (integrable_const ε)) hpoint
        _ = _ := by rw [integral_add hi (integrable_const ε)]; simp
    calc
      _ ≤ weightedIntegral μ h f + ε := hint
      _ ≤ ‖weightedIntegral μ h‖ + ε := by
        gcongr
        exact (le_abs_self _).trans (by simpa using (weightedIntegral μ h).le_opNorm_of_le hf)

variable (T : ℝ) [Fact (0 < T)]

/-- Symmetry of the finite frequency interval makes the Dirichlet kernel real. -/
theorem dirichletKernel_conj (N : ℕ) (y : Circle T) :
    conj (dirichletKernel T N y) = dirichletKernel T N y := by
  classical
  simp only [dirichletKernel, map_sum]
  calc
    (∑ k ∈ frequencies N, conj (mode T k y)) = ∑ k ∈ frequencies N, mode T (-k) y := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [mode]
    _ = ∑ k ∈ frequencies N, mode T k y := by
      apply Finset.sum_nbij (fun k : ℤ => -k)
      · intro k hk
        simp only [frequencies, Finset.mem_Icc] at hk ⊢
        omega
      · intro a ha b hb hab
        exact neg_injective hab
      · intro k hk
        refine ⟨-k, ?_, neg_neg k⟩
        simp only [Finset.mem_coe, frequencies, Finset.mem_Icc] at hk ⊢
        omega
      · intro k hk
        rfl

theorem dirichletKernel_ofReal_re (N : ℕ) (y : Circle T) :
    ((dirichletKernel T N y).re : ℂ) = dirichletKernel T N y := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (dirichletKernel_conj T N y)
    simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

theorem abs_re_dirichletKernel (N : ℕ) (y : Circle T) :
    |(dirichletKernel T N y).re| = ‖dirichletKernel T N y‖ := by
  conv_rhs => rw [← dirichletKernel_ofReal_re T N y]
  simp

/-- The real density of the fixed-point Fourier functional. -/
def dirichletWeight (N : ℕ) (x : Circle T) : C(Circle T, ℝ) :=
  ⟨fun y => (dirichletKernel T N (x - y)).re,
    Complex.continuous_re.comp ((continuous_dirichletKernel T N).comp
      (continuous_const.sub continuous_id))⟩

/-- The bounded real linear Fourier partial-sum functional. -/
def dirichletFunctional (N : ℕ) (x : Circle T) : C(Circle T, ℝ) →L[ℝ] ℝ :=
  weightedIntegral (haar T) (dirichletWeight T N x)

theorem dirichletFunctional_apply (N : ℕ) (x : Circle T) (f : C(Circle T, ℝ)) :
    (dirichletFunctional T N x f : ℂ) = partialSum T N (fun y => (f y : ℂ)) x := by
  have hf : Integrable (fun y => (f y : ℂ)) (haar T) :=
    (Complex.continuous_ofReal.comp f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [partialSum_eq_convolution T _ hf]
  unfold convolution
  rw [← integral_sub_left_eq_self
    (fun y => (f (x - y) : ℂ) * dirichletKernel T N y) (haar T) x]
  simp only [sub_sub_cancel]
  change ((∫ y, f y * (dirichletKernel T N (x - y)).re ∂haar T : ℝ) : ℂ) = _
  rw [← integral_complex_ofReal (μ := haar T)
    (f := fun y => f y * (dirichletKernel T N (x - y)).re)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    simp only [Complex.ofReal_mul, dirichletKernel_ofReal_re])

theorem norm_dirichletFunctional (N : ℕ) (x : Circle T) :
    ‖dirichletFunctional T N x‖ = ∫ y, ‖dirichletKernel T N y‖ ∂haar T := by
  rw [dirichletFunctional, norm_weightedIntegral]
  simp only [dirichletWeight, ContinuousMap.coe_mk, abs_re_dirichletKernel]
  exact integral_sub_left_eq_self (fun y => ‖dirichletKernel T N y‖) (haar T) x

theorem exists_dirichletFunctional (x : Circle T) :
    ∃ Λ : ℕ → (C(Circle T, ℝ) →L[ℝ] ℝ),
      (∀ (N : ℕ) (f : C(Circle T, ℝ)),
        (Λ N f : ℂ) = partialSum T N (fun y => (f y : ℂ)) x) ∧
      (∀ N : ℕ, ‖Λ N‖ = ∫ y, ‖dirichletKernel T N y‖ ∂haar T) := by
  exact ⟨fun N => dirichletFunctional T N x,
    fun N f => dirichletFunctional_apply T N x f,
    fun N => norm_dirichletFunctional T N x⟩

/-- Reflection permutes the symmetric frequency interval. -/
theorem sum_frequencies_neg {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℤ → M) :
    (∑ k ∈ frequencies N, g (-k)) = ∑ k ∈ frequencies N, g k := by
  classical
  apply Finset.sum_nbij (fun k : ℤ => -k)
  · intro k hk
    simp only [frequencies, Finset.mem_Icc] at hk ⊢
    omega
  · intro a ha b hb hab
    exact neg_injective hab
  · intro k hk
    refine ⟨-k, ?_, neg_neg k⟩
    simp only [Finset.mem_coe, frequencies, Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk
    rfl

/-- The elementary integral at a positive half-integer frequency. -/
theorem integral_sin_half_integer (m : ℤ) (hm : 0 ≤ m) :
    (∫ v in 0..Real.pi, Real.sin (((m : ℝ) + 1 / 2) * v)) =
      1 / ((m : ℝ) + 1 / 2) := by
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ) + 1 / 2 ≠ 0 := by positivity
  have hc : Real.cos (((m : ℝ) + 1 / 2) * Real.pi) = 0 := by
    rw [show ((m : ℝ) + 1 / 2) * Real.pi = Real.pi / 2 + m * Real.pi by ring,
      Real.cos_add_int_mul_pi]
    simp
  rw [intervalIntegral.integral_comp_mul_left _ hp, integral_sin]
  simp only [one_div] at hc ⊢
  simp [hc, smul_eq_mul]

/-- A bounded sine test converts the kernel integral to reciprocal sums. -/
theorem integral_cos_mul_sin_half (N : ℕ) (k : ℤ) (hk : k ∈ frequencies N) :
    (∫ v in 0..Real.pi,
      Real.cos ((k : ℝ) * v) * Real.sin (((N : ℝ) + 1 / 2) * v)) =
      (1 / ((N : ℝ) + 1 / 2 + k) + 1 / ((N : ℝ) + 1 / 2 - k)) / 2 := by
  have hk' : -(N : ℤ) ≤ k ∧ k ≤ N := by simpa only [frequencies, Finset.mem_Icc] using hk
  have hplus : 0 ≤ (N : ℤ) + k := by omega
  have hminus : 0 ≤ (N : ℤ) - k := by omega
  have hid (v : ℝ) :
      Real.cos ((k : ℝ) * v) * Real.sin (((N : ℝ) + 1 / 2) * v) =
      (Real.sin ((((N : ℝ) + k) + 1 / 2) * v) +
        Real.sin ((((N : ℝ) - k) + 1 / 2) * v)) / 2 := by
    rw [show (((N : ℝ) + k) + 1 / 2) * v = ((N : ℝ) + 1 / 2) * v + k * v by ring,
      show (((N : ℝ) - k) + 1 / 2) * v = ((N : ℝ) + 1 / 2) * v - k * v by ring,
      Real.sin_add, Real.sin_sub]
    ring
  simp_rw [hid]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add]
  · have h1 := integral_sin_half_integer ((N : ℤ) + k) hplus
    have h2 := integral_sin_half_integer ((N : ℤ) - k) hminus
    push_cast at h1 h2
    rw [h1, h2]
    congr 2 <;> ring
  all_goals exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem angular_dirichletKernel_re (N : ℕ) (v : ℝ) :
    (dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))).re =
      ∑ k ∈ frequencies N, Real.cos ((k : ℝ) * v) := by
  simp only [dirichletKernel, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [angular_mode, Complex.exp_re]
  simp

/-- The sine test evaluates exactly to a sum of positive reciprocals. -/
theorem integral_dirichletKernel_sine_test (N : ℕ) :
    (∫ v in 0..Real.pi,
      (dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))).re *
        Real.sin (((N : ℝ) + 1 / 2) * v)) =
      ∑ k ∈ frequencies N, 1 / ((N : ℝ) + 1 / 2 + k) := by
  simp_rw [angular_dirichletKernel_re, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · trans ∑ k ∈ frequencies N,
        (1 / ((N : ℝ) + 1 / 2 + k) + 1 / ((N : ℝ) + 1 / 2 - k)) / 2
    · exact Finset.sum_congr rfl (fun k hk => integral_cos_mul_sin_half N k hk)
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have hneg : (∑ k ∈ frequencies N, 1 / ((N : ℝ) + 1 / 2 - k)) =
        ∑ k ∈ frequencies N, 1 / ((N : ℝ) + 1 / 2 + k) := by
      simpa only [Int.cast_neg, sub_eq_add_neg] using
        sum_frequencies_neg N (fun k => 1 / ((N : ℝ) + 1 / 2 + k))
    rw [hneg]
    ring
  · intro k hk
    exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- Reindexing the positive reciprocals exposes a harmonic lower bound. -/
theorem harmonic_le_reciprocal_frequencies (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (1 / (j + 1) : ℝ)) ≤
      ∑ k ∈ frequencies N, 1 / ((N : ℝ) + 1 / 2 + k) := by
  have hbij : (∑ j ∈ Finset.range (2 * N + 1), (1 / ((j : ℝ) + 1 / 2))) =
      ∑ k ∈ frequencies N, 1 / ((N : ℝ) + 1 / 2 + k) := by
    apply Finset.sum_nbij (fun j : ℕ => (j : ℤ) - N)
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [frequencies, Finset.mem_Icc]
      omega
    · intro a ha b hb hab
      change (a : ℤ) - N = (b : ℤ) - N at hab
      omega
    · intro k hk
      have hk' : -(N : ℤ) ≤ k ∧ k ≤ N := by
        simpa only [Finset.mem_coe, frequencies, Finset.mem_Icc] using hk
      refine ⟨(k + N).toNat, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_range]
        omega
      · change ((k + N).toNat : ℤ) - N = k
        omega
    · intro j hj
      push_cast
      congr 1
      ring
  rw [← hbij]
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), (1 / ((j : ℝ) + 1 / 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun j hj _ => by positivity)

/-- The kernel dominates a harmonic sum already on the positive half interval. -/
theorem harmonic_le_integral_norm_dirichletKernel (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (1 / (j + 1) : ℝ)) ≤
      ∫ v in 0..Real.pi, ‖dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))‖ := by
  refine (harmonic_le_reciprocal_frequencies N).trans ?_
  rw [← integral_dirichletKernel_sine_test]
  apply intervalIntegral.integral_mono_on Real.pi_pos.le
  · exact ((Complex.continuous_re.comp ((continuous_dirichletKernel _ N).comp
      continuous_quotient_mk')).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact ((continuous_dirichletKernel _ N).comp continuous_quotient_mk').norm.intervalIntegrable _ _
  · intro v hv
    calc
      _ ≤ |(dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))).re *
          Real.sin (((N : ℝ) + 1 / 2) * v)| := le_abs_self _
      _ ≤ |(dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))).re| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      _ = _ := abs_re_dirichletKernel _ N _

/-- Lebesgue constants are unchanged by a positive change of period. -/
theorem integral_norm_dirichletKernel_rescale (U : ℝ) [Fact (0 < U)] (N : ℕ) :
    (∫ y, ‖dirichletKernel T N y‖ ∂haar T) =
      ∫ y, ‖dirichletKernel U N y‖ ∂haar U := by
  calc
    _ = ∫ y, ‖dirichletKernel U N (rescale T U y)‖ ∂haar T := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => congrArg norm (rescale_kernels T U N 0 (fun _ => 0) y).1)
    _ = _ := (rescale_measure T U).integral_comp
      (AddCircle.homeomorphAddCircle T U (Fact.out : 0 < T).ne'
        (Fact.out : 0 < U).ne').isClosedEmbedding.measurableEmbedding
      (fun y => ‖dirichletKernel U N y‖)

/-- A harmonic lower bound with the source's probability normalization. -/
theorem harmonic_le_mul_integral_norm_dirichletKernel (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (1 / (j + 1) : ℝ)) ≤
      (2 * Real.pi) * (∫ y, ‖dirichletKernel T N y‖ ∂haar T) := by
  rw [integral_norm_dirichletKernel_rescale T (2 * Real.pi) N]
  refine (harmonic_le_integral_norm_dirichletKernel N).trans ?_
  have hint : (∫ y, ‖dirichletKernel (2 * Real.pi) N y‖ ∂haar (2 * Real.pi)) =
      (2 * Real.pi)⁻¹ *
        (∫ v in 0..0 + 2 * Real.pi,
          ‖dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))‖) := by
    rw [haar, AddCircle.integral_haarAddCircle,
      ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
    rfl
  rw [hint, ← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
  apply intervalIntegral.integral_mono_interval (by rfl) Real.pi_pos.le (by linarith [Real.pi_pos])
  · exact ae_of_all _ (fun v => norm_nonneg _)
  · exact ((continuous_dirichletKernel _ N).comp continuous_quotient_mk').norm.intervalIntegrable _ _

/-- The Dirichlet kernels have unbounded L¹ norm for every positive period. -/
theorem dirichletKernel_norms_unbounded :
    ¬ BddAbove (Set.range (fun N : ℕ => ∫ y, ‖dirichletKernel T N y‖ ∂haar T)) := by
  rintro ⟨M, hM⟩
  have hlim : Filter.Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), (1 / (j + 1) : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hb : BddAbove (Set.range
      (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), (1 / (j + 1) : ℝ))) := by
    refine ⟨(2 * Real.pi) * M, ?_⟩
    rintro z ⟨N, rfl⟩
    exact (harmonic_le_mul_integral_norm_dirichletKernel T N).trans
      (mul_le_mul_of_nonneg_left (hM (Set.mem_range_self N)) (by positivity))
  exact Filter.not_bddAbove_of_tendsto_atTop hlim hb

/-- A bounded real linear functional at each index, with unbounded operator norms. -/
theorem exists_unbounded_dirichletFunctional (x : Circle T) :
    ∃ Λ : ℕ → (C(Circle T, ℝ) →L[ℝ] ℝ),
      (∀ (N : ℕ) (f : C(Circle T, ℝ)),
        (Λ N f : ℂ) = partialSum T N (fun y => (f y : ℂ)) x) ∧
      (∀ N : ℕ, ‖Λ N‖ = ∫ y, ‖dirichletKernel T N y‖ ∂haar T) ∧
      ¬ BddAbove (Set.range (fun N : ℕ => ‖Λ N‖)) := by
  refine ⟨fun N => dirichletFunctional T N x,
    fun N f => dirichletFunctional_apply T N x f,
    fun N => norm_dirichletFunctional T N x, ?_⟩
  simpa only [norm_dirichletFunctional] using dirichletKernel_norms_unbounded T

end P102.Periodic
