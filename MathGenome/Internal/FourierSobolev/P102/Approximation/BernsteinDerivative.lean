import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import Mathlib.RingTheory.RootsOfUnity.Complex
import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.BernsteinDerivative

noncomputable section
open scoped Real ComplexConjugate
open P102.Periodic

namespace P102.Approximation

variable (T : ℝ) [Fact (0 < T)]

/-- The actual derivative of the periodic lift of a finite Fourier synthesis. -/
def synthesisDerivative (c : ℤ →₀ ℂ) : C(Circle T, ℂ) :=
  ∑ k ∈ c.support, (c k * (2 * Real.pi * Complex.I * k / T)) • mode T k

theorem hasDerivAt_synthesis (c : ℤ →₀ ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => synthesis T c (s : Circle T))
      (synthesisDerivative T c (t : Circle T)) t := by
  simp only [synth_sum, synthesisDerivative, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  simpa only [mode, mul_assoc, Finset.sum_apply] using HasDerivAt.fun_sum (fun k (_ : k ∈ c.support) =>
    (hasDerivAt_fourier T k t).const_mul (c k))

theorem complexTrigDegree_hasDerivative {n : ℕ} (P : C(Circle T, ℂ))
    (hP : P ∈ complexTrigDegree T n) :
    ∃ Q : C(Circle T, ℂ), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t := by
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨synthesisDerivative T c, hasDerivAt_synthesis T c⟩

/-- Uniqueness makes the circle witness independent of the coefficient presentation. -/
theorem circleDerivative_unique {𝕜 : Type*} [RCLike 𝕜]
    (P Q R : C(Circle T, 𝕜))
    (hQ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t)
    (hR : ∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (R (t : Circle T)) t) :
    Q = R := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (hQ t).unique (hR t)

/-- Taking real parts commutes with the derivative of the real lift. -/
def realSynthesisDerivative (c : ℤ →₀ ℂ) : C(Circle T, ℝ) :=
  ⟨fun x => (synthesisDerivative T c x).re,
    Complex.continuous_re.comp (synthesisDerivative T c).continuous⟩

theorem hasDerivAt_realSynthesis (c : ℤ →₀ ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => realSynthesis T c (s : Circle T))
      (realSynthesisDerivative T c (t : Circle T)) t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_synthesis T c t)

theorem realTrigDegree_hasDerivative {n : ℕ} (P : C(Circle T, ℝ))
    (hP : P ∈ realTrigDegree T n) :
    ∃ Q : C(Circle T, ℝ), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t := by
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨realSynthesisDerivative T c, hasDerivAt_realSynthesis T c⟩

theorem synthesisDerivative_eq_zero_of_degree_zero (c : ℤ →₀ ℂ)
    (hc : c ∈ Finsupp.supported ℂ ℂ (Set.Icc (-(0 : ℤ)) 0)) :
    synthesisDerivative T c = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k = 0 := by
    have := (Finsupp.mem_supported ℂ c).mp hc hk
    simpa using this
  simp [hk0]

theorem bernstein_complex_zero (P : C(Circle T, ℂ))
    (hP : P ∈ complexTrigDegree T 0) :
    ∃ Q : C(Circle T, ℂ),
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t) ∧
      ‖Q‖ ≤ (2 * Real.pi / T) * (0 : ℕ) * ‖P‖ := by
  obtain ⟨c, hc, rfl⟩ := hP
  refine ⟨synthesisDerivative T c, hasDerivAt_synthesis T c, ?_⟩
  simp [synthesisDerivative_eq_zero_of_degree_zero T c hc]

theorem bernstein_real_zero (P : C(Circle T, ℝ))
    (hP : P ∈ realTrigDegree T 0) :
    ∃ Q : C(Circle T, ℝ),
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t) ∧
      ‖Q‖ ≤ (2 * Real.pi / T) * (0 : ℕ) * ‖P‖ := by
  obtain ⟨c, hc, rfl⟩ := hP
  refine ⟨realSynthesisDerivative T c, hasDerivAt_realSynthesis T c, ?_⟩
  have hzero : realSynthesisDerivative T c = 0 := by
    ext x
    simp [realSynthesisDerivative, synthesisDerivative_eq_zero_of_degree_zero T c hc.1]
  simp [hzero]

theorem mode_translate (k : ℤ) (x y : Circle T) :
    mode T k (x + y) = mode T k x * mode T k y := by
  simp only [mode, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Differentiate with respect to the angular coordinate. -/
def angularSynthesisDerivative (c : ℤ →₀ ℂ) : C(Circle T, ℂ) :=
  ∑ k ∈ c.support, (c k * (Complex.I * k)) • mode T k

theorem synthesisDerivative_eq_angular (c : ℤ →₀ ℂ) :
    synthesisDerivative T c = (2 * Real.pi / T : ℂ) • angularSynthesisDerivative T c := by
  ext x
  simp only [synthesisDerivative, angularSynthesisDerivative, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Exact finite sampling moments give the derivative interpolation formula.
This lemma has explicit hypotheses; no sampling certificate is assumed by the
Bernstein theorem itself. -/
theorem angularSynthesisDerivative_sampling {ι : Type*} [Fintype ι]
    (n : ℕ) (nodes : ι → Circle T) (weights : ι → ℂ)
    (hmom : ∀ k : ℤ, k ∈ Set.Icc (-(n : ℤ)) n →
      ∑ j, weights j * mode T k (nodes j) = Complex.I * k)
    (c : ℤ →₀ ℂ)
    (hc : c ∈ Finsupp.supported ℂ ℂ (Set.Icc (-(n : ℤ)) n)) (x : Circle T) :
    angularSynthesisDerivative T c x =
      ∑ j, weights j * synthesis T c (x + nodes j) := by
  symm
  simp only [synth_sum, Finset.mul_sum, mode_translate]
  rw [Finset.sum_comm]
  simp only [angularSynthesisDerivative, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hm := hmom k ((Finsupp.mem_supported ℂ c).mp hc hk)
  calc
    ∑ j, weights j * (c k * (mode T k x * mode T k (nodes j))) =
        (c k * mode T k x) * ∑ j, weights j * mode T k (nodes j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c k * (Complex.I * k) * mode T k x := by rw [hm]; ring

theorem synthesisDerivative_norm_le_of_sampling {ι : Type*} [Fintype ι]
    (n : ℕ) (nodes : ι → Circle T) (weights : ι → ℂ)
    (hmom : ∀ k : ℤ, k ∈ Set.Icc (-(n : ℤ)) n →
      ∑ j, weights j * mode T k (nodes j) = Complex.I * k)
    (hmass : ∑ j, ‖weights j‖ ≤ (n : ℝ))
    (c : ℤ →₀ ℂ)
    (hc : c ∈ Finsupp.supported ℂ ℂ (Set.Icc (-(n : ℤ)) n)) :
    ‖synthesisDerivative T c‖ ≤ (2 * Real.pi / T) * n * ‖synthesis T c‖ := by
  have hang : ‖angularSynthesisDerivative T c‖ ≤ n * ‖synthesis T c‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    rw [angularSynthesisDerivative_sampling T n nodes weights hmom c hc x]
    calc
      ‖∑ j, weights j * synthesis T c (x + nodes j)‖ ≤
          ∑ j, ‖weights j * synthesis T c (x + nodes j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖weights j‖ * ‖synthesis T c‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((synthesis T c).norm_coe_le_norm _) (norm_nonneg _)
      _ = (∑ j, ‖weights j‖) * ‖synthesis T c‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ n * ‖synthesis T c‖ := mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
  rw [synthesisDerivative_eq_angular, norm_smul]
  have hω : 0 ≤ 2 * Real.pi / T := le_of_lt (div_pos (by positivity) Fact.out)
  have hnorm : ‖(2 * Real.pi / T : ℂ)‖ = 2 * Real.pi / T := by
    norm_cast
    exact Real.norm_of_nonneg hω
  rw [hnorm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hang hω

theorem norm_synthesis_eq_realSynthesis (c : ℤ →₀ ℂ)
    (hc : c ∈ symmetricCoefficients) :
    ‖synthesis T c‖ = ‖realSynthesis T c‖ := by
  simp only [ContinuousMap.norm_eq_iSup_norm]
  congr 1
  funext x
  rw [← symmetric_synthesis T c hc x, Complex.norm_real]

theorem norm_realSynthesisDerivative_le (c : ℤ →₀ ℂ) :
    ‖realSynthesisDerivative T c‖ ≤ ‖synthesisDerivative T c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact (show ‖(synthesisDerivative T c x).re‖ ≤ ‖synthesisDerivative T c x‖ from Complex.abs_re_le_norm _).trans ((synthesisDerivative T c).norm_coe_le_norm x)

/-- The real conclusion follows from the complex estimate without changing the norm. -/
theorem bernstein_real_of_complex
    (hcomplex : ∀ (n : ℕ) (P : C(Circle T, ℂ)), P ∈ complexTrigDegree T n →
      ∃ Q : C(Circle T, ℂ),
        (∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t) ∧
        ‖Q‖ ≤ (2 * Real.pi / T) * n * ‖P‖)
    (n : ℕ) (P : C(Circle T, ℝ)) (hP : P ∈ realTrigDegree T n) :
    ∃ Q : C(Circle T, ℝ),
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t) ∧
      ‖Q‖ ≤ (2 * Real.pi / T) * n * ‖P‖ := by
  obtain ⟨c, hc, rfl⟩ := hP
  obtain ⟨Q, hQ, hbound⟩ := hcomplex n (synthesis T c) ⟨c, hc.1, rfl⟩
  have hQeq : Q = synthesisDerivative T c :=
    circleDerivative_unique T _ _ _ hQ (hasDerivAt_synthesis T c)
  refine ⟨realSynthesisDerivative T c, hasDerivAt_realSynthesis T c, ?_⟩
  calc
    ‖realSynthesisDerivative T c‖ ≤ ‖synthesisDerivative T c‖ := norm_realSynthesisDerivative_le T c
    _ ≤ (2 * Real.pi / T) * n * ‖synthesis T c‖ := hQeq ▸ hbound
    _ = (2 * Real.pi / T) * n * ‖realSynthesis T c‖ := by
      rw [norm_synthesis_eq_realSynthesis T c hc.2]

/-- The odd half-grid in angular coordinates. -/
def rieszNode (n : ℕ) (j : Fin (2 * n)) : Circle (2 * Real.pi) :=
  (((2 * (j : ℝ) + 1) * Real.pi / (2 * n) : ℝ) : Circle (2 * Real.pi))

/-- A positive Fejér square with a unimodular factor. This equals the
usual alternating cosecant-square Riesz weight at the odd half-grid. -/
def rieszWeight (n : ℕ) (j : Fin (2 * n)) : ℂ :=
  (-Complex.I / (2 * n)) * mode (2 * Real.pi) n (rieszNode n j) *
    (‖∑ r ∈ Finset.range n, mode (2 * Real.pi) (r : ℤ) (rieszNode n j)‖ ^ 2 : ℝ)

theorem rieszNode_top_mode_sq (n : ℕ) (hn : 0 < n) (j : Fin (2 * n)) :
    (mode (2 * Real.pi) n (rieszNode n j)) ^ 2 = -1 := by
  rw [mode, pow_two, ← fourier_add]
  change mode (2 * Real.pi) ((n : ℤ) + n) (rieszNode n j) = -1
  rw [rieszNode, angular_mode]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : Complex.I * ((n : ℤ) + n) *
      (((2 * (j : ℝ) + 1) * Real.pi / (2 * n) : ℝ) : ℂ) =
      (j.val : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
    push_cast
    field_simp [hnC]
    ring
  simp only [Int.cast_add, Int.cast_natCast] at heq ⊢
  rw [heq, Complex.exp_add, Complex.exp_nat_mul]
  simp [Complex.exp_two_pi_mul_I, Complex.exp_pi_mul_I]

theorem rieszWeight_norm (n : ℕ) (hn : 0 < n) (j : Fin (2 * n)) :
    ‖rieszWeight n j‖ =
      (‖∑ r ∈ Finset.range n, mode (2 * Real.pi) (r : ℤ) (rieszNode n j)‖ ^ 2) / (2 * n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [rieszWeight, norm_mul, norm_div, norm_neg, Complex.norm_I,
    Complex.norm_ofNat, norm_natCast, Circle.norm_coe,
    mode, fourier_apply, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  ring

theorem rieszWeight_norm_eq_im (n : ℕ) (hn : 0 < n) (j : Fin (2 * n)) :
    ‖rieszWeight n j‖ =
      (rieszWeight n j * mode (2 * Real.pi) n (rieszNode n j)).im := by
  rw [rieszWeight_norm n hn j]
  have heq : rieszWeight n j * mode (2 * Real.pi) n (rieszNode n j) =
      (Complex.I / (2 * n)) *
        (‖∑ r ∈ Finset.range n, mode (2 * Real.pi) (r : ℤ) (rieszNode n j)‖ ^ 2 : ℝ) := by
    dsimp only [rieszWeight]
    calc
      _ = (-Complex.I / (2 * n)) *
          (mode (2 * Real.pi) n (rieszNode n j)) ^ 2 *
          (‖∑ r ∈ Finset.range n, mode (2 * Real.pi) (r : ℤ) (rieszNode n j)‖ ^ 2 : ℝ) := by ring
      _ = _ := by rw [rieszNode_top_mode_sq n hn j]; ring
  rw [heq]
  have heq' : (Complex.I / (2 * n)) *
      (‖∑ r ∈ Finset.range n, mode (2 * Real.pi) (r : ℤ) (rieszNode n j)‖ ^ 2 : ℝ) =
      Complex.I * ((‖∑ r ∈ Finset.range n,
        mode (2 * Real.pi) (r : ℤ) (rieszNode n j)‖ ^ 2 / (2 * n) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq']
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]

/-- Normalization follows from the top-frequency moment because every summand
has the same imaginary phase after multiplication by that mode. -/
theorem rieszWeight_mass_of_top_moment (n : ℕ) (hn : 0 < n)
    (htop : ∑ j : Fin (2 * n), rieszWeight n j *
      mode (2 * Real.pi) n (rieszNode n j) = Complex.I * n) :
    ∑ j : Fin (2 * n), ‖rieszWeight n j‖ = (n : ℝ) := by
  simp_rw [rieszWeight_norm_eq_im n hn]
  rw [← Complex.im_sum, htop]
  simp

theorem mode_eq_zpow (k : ℤ) (x : Circle T) :
    mode T k x = (mode T 1 x) ^ k := by
  simp only [mode, fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, one_zsmul]

/-- The inverse discrete Fourier derivative kernel for the frequency window
-n+1,...,n. Its top and bottom endpoint samples differ by a minus sign. -/
def inverseDerivativeKernel (n : ℕ) (j : Fin (2 * n)) : ℂ :=
  (Complex.I / (2 * n)) * ∑ r ∈ Finset.range (2 * n),
    (((r : ℤ) - n + 1 : ℤ) : ℂ) *
      mode (2 * Real.pi) (-((r : ℤ) - n + 1)) (rieszNode n j)

/-- The independent algebraic square factorization identifies the discrete
Fourier kernel with the Riesz weight used in the norm proof. -/
theorem rieszWeight_eq_inverseDerivativeKernel (n : ℕ) (hn : 0 < n)
    (hfactor : ∀ z : ℂ, ‖z‖ = 1 → z ^ (2 * n) = -1 →
      (∑ r ∈ Finset.range (2 * n), (((r : ℤ) - n + 1 : ℤ) : ℂ) *
        z ^ ((n : ℤ) - 1 - r)) =
      -(z ^ (n : ℤ)) * (‖∑ r ∈ Finset.range n, z ^ r‖ ^ 2 : ℝ))
    (j : Fin (2 * n)) :
    rieszWeight n j = inverseDerivativeKernel n j := by
  let z : ℂ := mode (2 * Real.pi) 1 (rieszNode n j)
  have hz : ‖z‖ = 1 := by simp [z, fourier_apply, Circle.norm_coe]
  have hzN : z ^ (2 * n) = -1 := by
    have h := rieszNode_top_mode_sq n hn j
    rw [mode_eq_zpow] at h
    simpa only [zpow_natCast, ← pow_mul, Nat.mul_comm n 2] using h
  have hf := hfactor z hz hzN
  have he : ∀ r : ℕ, -((r : ℤ) - n + 1) = (n : ℤ) - 1 - r := by
    intro r
    ring
  have hs : (∑ r ∈ Finset.range (2 * n), (((r : ℤ) - n + 1 : ℤ) : ℂ) *
      mode (2 * Real.pi) (-((r : ℤ) - n + 1)) (rieszNode n j)) =
      ∑ r ∈ Finset.range (2 * n), (((r : ℤ) - n + 1 : ℤ) : ℂ) * z ^ ((n : ℤ) - 1 - r) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [mode_eq_zpow, he]
  have hA : (∑ r ∈ Finset.range n, mode (2 * Real.pi) (r : ℤ) (rieszNode n j)) =
      ∑ r ∈ Finset.range n, z ^ r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [mode_eq_zpow, zpow_natCast]
  have hnm : mode (2 * Real.pi) n (rieszNode n j) = z ^ n := by
    rw [mode_eq_zpow, zpow_natCast]
  rw [rieszWeight, hnm, hA, inverseDerivativeKernel, hs, hf, zpow_natCast]
  ring

/-- Orthogonality on the odd half-grid, in the positive frequency window used below. -/
theorem rieszNode_mode_sum (n : ℕ) (hn : 0 < n) (m : ℕ)
    (hm : 0 < m) (hm4 : m < 4 * n) :
    (∑ j : Fin (2 * n), mode (2 * Real.pi) m (rieszNode n j)) =
      if m = 2 * n then -(2 * n : ℂ) else 0 := by
  have hn0 : 2 * n ≠ 0 := by omega
  by_cases heq : m = 2 * n
  · subst m
    rw [ite_eq_left rfl]
    have hj (j : Fin (2 * n)) : mode (2 * Real.pi) (↑(2 * n)) (rieszNode n j) = -1 := by
      have h := rieszNode_top_mode_sq n hn j
      simpa only [pow_two, mode, ← fourier_add, Nat.cast_mul, Nat.cast_ofNat,
        two_mul, Nat.cast_add] using h
    simp_rw [hj]
    simp
  · rw [ite_eq_right heq]
    let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * n))
    have hq : IsPrimitiveRoot q (2 * n) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using Complex.isPrimitiveRoot_exp (2 * n) hn0
    have hne : q ^ m ≠ 1 := by
      intro h
      obtain ⟨d, hd⟩ := (hq.pow_eq_one_iff_dvd m).mp h
      have hd0 : 0 < d := by nlinarith
      have hd2 : d < 2 := by nlinarith
      have : d = 1 := by omega
      simp_all
    have hpow : (q ^ m) ^ (2 * n) = 1 := by
      rw [← pow_mul, Nat.mul_comm m (2 * n), pow_mul, hq.pow_eq_one, one_pow]
    have hgeom : ∑ j ∈ Finset.range (2 * n), (q ^ m) ^ j = 0 := by
      rw [geom_sum_eq hne, hpow, sub_self, zero_div]
    have hj (j : Fin (2 * n)) : mode (2 * Real.pi) m (rieszNode n j) =
        Complex.exp (Complex.I * m * Real.pi / (2 * n)) * (q ^ m) ^ (j : ℕ) := by
      rw [rieszNode, angular_mode]
      have hex : Complex.I * (m : ℤ) *
          (((2 * (j : ℝ) + 1) * Real.pi / (2 * n) : ℝ) : ℂ) =
          Complex.I * m * Real.pi / (2 * n) +
          (j : ℂ) * ((m : ℂ) * (2 * Real.pi * Complex.I / (2 * n))) := by
        push_cast
        ring
      rw [hex, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul]
    simp_rw [hj]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range, hgeom, mul_zero]

/-- Number of ordered pairs in a finite interval with prescribed nonnegative difference. -/
theorem count_shift_pairs (n d : ℕ) (hd : d ≤ n) :
    (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
      if a = b + d then (1 : ℂ) else 0) = (n - d : ℕ) := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_range]
  have h := Finset.sum_range_add (fun b => if b + d < n then (1 : ℂ) else 0) (n - d) d
  have hn : n - d + d = n := Nat.sub_add_cancel hd
  rw [hn] at h
  rw [h]
  have h1 : (∑ b ∈ Finset.range (n - d), if b + d < n then (1 : ℂ) else 0) = (n-d : ℕ) := by
    rw [Finset.sum_congr rfl (fun b hb =>
      ite_eq_left (by have := Finset.mem_range.mp hb; omega))]
    simp
  have h2 : (∑ b ∈ Finset.range d, if n - d + b + d < n then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [ite_eq_right (by omega)]
  rw [h1, h2, add_zero]

theorem rieszWeight_conj (n : ℕ) (hn : 0 < n) (j : Fin (2 * n)) :
    conj (rieszWeight n j) = rieszWeight n j := by
  let z := mode (2 * Real.pi) n (rieszNode n j)
  have hz : ‖z‖ = 1 := by simp [z, fourier_apply, Circle.norm_coe]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hsq : z ^ 2 = -1 := rieszNode_top_mode_sq n hn j
  have hconj : conj z = -z := by
    apply mul_left_cancel₀ hz0
    rw [Complex.mul_conj', hz]
    norm_num only [Complex.ofReal_one, one_pow]
    calc
      (1 : ℂ) = -(z ^ 2) := by rw [hsq]; ring
      _ = z * -z := by ring
  let A : ℝ := ‖∑ a ∈ Finset.range n, mode (2 * Real.pi) (a : ℤ) (rieszNode n j)‖ ^ 2
  change conj ((-Complex.I / (2 * n)) * z * (A : ℂ)) =
    (-Complex.I / (2 * n)) * z * (A : ℂ)
  simp only [map_mul, map_div₀, map_neg, Complex.conj_I, map_ofNat, map_natCast,
    Complex.conj_ofReal, hconj]
  norm_num; ring

/-- Expand a squared Fourier sum into its differences of frequencies. -/
theorem mode_square_sum (n : ℕ) (x : Circle (2 * Real.pi)) :
    ((‖∑ a ∈ Finset.range n, mode (2 * Real.pi) (a : ℤ) x‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
        mode (2 * Real.pi) ((a : ℤ) - b) x := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, ← fourier_neg, ← fourier_add]
  rfl

/-- For a nonnegative frequency, precisely `k` index pairs survive orthogonality. -/
theorem riesz_sampling_moments_nat (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    (∑ j : Fin (2 * n), rieszWeight n j * mode (2 * Real.pi) k (rieszNode n j)) =
      Complex.I * k := by
  have hcore : (∑ j : Fin (2 * n), mode (2 * Real.pi) n (rieszNode n j) *
      ((‖∑ a ∈ Finset.range n, mode (2 * Real.pi) (a : ℤ) (rieszNode n j)‖ ^ 2 : ℝ) : ℂ) *
      mode (2 * Real.pi) k (rieszNode n j)) = -(2 * n : ℂ) * k := by
    simp_rw [mode_square_sum, Finset.mul_sum, Finset.sum_mul, ← fourier_add]
    calc
      _ = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ j : Fin (2 * n),
          mode (2 * Real.pi) ((n : ℤ) + ((a : ℤ) - b) + k) (rieszNode n j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
      _ = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
          if a = b + (n - k) then -(2 * n : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        have ha' := Finset.mem_range.mp ha
        have hb' := Finset.mem_range.mp hb
        have hm : 0 < n + k + a - b := by omega
        have hm4 : n + k + a - b < 4 * n := by omega
        have hcast : ((n + k + a - b : ℕ) : ℤ) = (n : ℤ) + ((a : ℤ) - b) + k := by omega
        rw [← hcast, rieszNode_mode_sum n hn _ hm hm4]
        have he : n + k + a - b = 2 * n ↔ a = b + (n - k) := by omega
        simp only [he]
      _ = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
          if a = b + (n - k) then (1 : ℂ) else 0) * -(2 * n : ℂ) := by
        simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = -(2 * n : ℂ) * k := by
        rw [count_shift_pairs n (n - k) (by omega)]
        have : n - (n - k) = k := by omega
        rw [this]
        ring
  simp only [rieszWeight]
  simp_rw [mul_assoc (-Complex.I / (2 * n : ℂ))]
  rw [← Finset.mul_sum]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ = (-Complex.I / (2 * n : ℂ)) * (-(2 * n : ℂ) * k) := by
      simpa only [mul_assoc] using
        congrArg (fun z : ℂ => (-Complex.I / (2 * n : ℂ)) * z) hcore
    _ = Complex.I * k := by field_simp

/-- Exact moments of the finite Riesz sampling weights. -/
theorem riesz_sampling_moments (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : k ∈ Set.Icc (-(n : ℤ)) n) :
    ∑ j : Fin (2 * n), rieszWeight n j * mode (2 * Real.pi) k (rieszNode n j) =
      Complex.I * k := by
  change -(n : ℤ) ≤ k ∧ k ≤ n at hk
  by_cases hk0 : 0 ≤ k
  · have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    have h := riesz_sampling_moments_nat n hn k.toNat (by omega)
    simpa only [hkn, ← Int.cast_natCast] using h
  · have hkn : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have h := riesz_sampling_moments_nat n hn (-k).toNat (by omega)
    have h' := congrArg conj h
    simp only [map_sum, map_mul, rieszWeight_conj n hn, ← fourier_neg,
      Complex.conj_I, map_natCast] at h'
    simpa only [hkn, neg_neg, ← Int.cast_natCast, hkn, Int.cast_neg, neg_mul_neg] using h'

/-- Sharp complex Bernstein estimate, with the derivative on the original circle. -/
theorem bernstein_complex : Expected.bernsteinComplexStatement := by
  intro T hT n P hP
  change P ∈ complexTrigDegree T n at hP
  by_cases hn : n = 0
  · subst n
    exact bernstein_complex_zero T P hP
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨c, hc, rfl⟩ := hP
  let nodes : Fin (2 * n) → Circle T := fun j => (toAngle T).symm (rieszNode n j)
  have hmode (k : ℤ) (j : Fin (2 * n)) :
      mode T k (nodes j) = mode (2 * Real.pi) k (rieszNode n j) := by
    rw [← rescale_mode T (2 * Real.pi) k (nodes j)]
    simp [nodes, toAngle]
  have hmom (k : ℤ) (hk : k ∈ Set.Icc (-(n : ℤ)) n) :
      ∑ j, rieszWeight n j * mode T k (nodes j) = Complex.I * k := by
    simp_rw [hmode]
    exact riesz_sampling_moments n hnpos k hk
  have hmass : ∑ j : Fin (2 * n), ‖rieszWeight n j‖ ≤ (n : ℝ) := by
    apply le_of_eq
    exact rieszWeight_mass_of_top_moment n hnpos
      (riesz_sampling_moments n hnpos n ⟨by omega, le_rfl⟩)
  exact ⟨synthesisDerivative T c, hasDerivAt_synthesis T c,
    synthesisDerivative_norm_le_of_sampling T n nodes (rieszWeight n) hmom hmass c hc⟩

/-- Sharp real Bernstein estimate, using the real derivative and real supremum norm. -/
theorem bernstein_real : Expected.bernsteinRealStatement := by
  intro T hT n P hP
  exact bernstein_real_of_complex T (bernstein_complex T) n P hP

end P102.Approximation
