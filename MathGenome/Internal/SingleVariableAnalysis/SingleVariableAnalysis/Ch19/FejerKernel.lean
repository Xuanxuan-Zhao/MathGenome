import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FejerKernel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Convolution

noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators

abbrev fejerKernel := Specs.SingleVariableAnalysis.Ch19.FejerKernel.kernelValue
abbrev fejerMean := Specs.SingleVariableAnalysis.Ch19.FejerKernel.meanValue

namespace Fourier

/-- The one-sided exponential sum whose squared modulus is the Fejer numerator. -/
def positiveModeSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+1), fourierMode (j : ℤ) t

@[simp] theorem mode_zero (t : ℝ) : fourierMode 0 t = 1 := by
  simp [fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue]

theorem mode_add (n m : ℤ) (t : ℝ) :
    fourierMode (n+m) t = fourierMode n t * fourierMode m t := by
  unfold fourierMode Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mode_conj (n : ℤ) (t : ℝ) : star (fourierMode n t) = fourierMode (-n) t := by
  rw [mode_euler, mode_euler]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem mode_mul_star (n : ℤ) (t : ℝ) :
    fourierMode n t * star (fourierMode n t) = 1 := by
  rw [mode_conj, ← mode_add, add_neg_cancel, mode_zero]

@[simp] theorem positiveModeSum_zero (t : ℝ) : positiveModeSum 0 t = 1 := by
  simp [positiveModeSum]

theorem positiveModeSum_succ (N : ℕ) (t : ℝ) :
    positiveModeSum (N+1) t = positiveModeSum N t + fourierMode ((N : ℤ)+1) t := by
  simp only [positiveModeSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]

theorem positiveModeSum_succ_shift (N : ℕ) (t : ℝ) :
    positiveModeSum (N+1) t = 1 + fourierMode 1 t * positiveModeSum N t := by
  rw [positiveModeSum, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mode_add, mode_zero,
    positiveModeSum, Finset.mul_sum]
  simp only [mul_comm, add_comm]

/-- Splitting positive and negative frequencies without a quotient. -/
theorem dirichletKernel_positiveModeSum (N : ℕ) (t : ℝ) :
    dirichletKernel N t = positiveModeSum N t + star (positiveModeSum N t) - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [dirichletKernel_succ_modes, ih, positiveModeSum_succ, star_add, mode_conj]
    ring

/-- A finite algebraic identity, valid also at every multiple of 2π. -/
theorem sum_dirichletKernel_eq_square (N : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (N+1), dirichletKernel k t =
      positiveModeSum N t * star (positiveModeSum N t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, dirichletKernel_positiveModeSum,
      positiveModeSum_succ_shift, star_add, star_mul, star_one]
    have hu := mode_mul_star 1 t
    linear_combination -(positiveModeSum N t * star (positiveModeSum N t)) * hu

/-- The elementary difference-of-squares identity used for the sine formula. -/
theorem sin_square_step (a b : ℝ) :
    Real.sin (a+b)^2 - Real.sin a^2 = Real.sin b * Real.sin (2*a+b) := by
  have h := Real.two_mul_sin_mul_sin b (2*a+b)
  rw [show b-(2*a+b) = -(2*a) by ring, Real.cos_neg,
    show b+(2*a+b) = 2*(a+b) by ring] at h
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  linarith

/-- The sine identity is uncancelled, so it also holds at the lattice. -/
theorem sum_dirichletKernel_sine_mul (N : ℕ) (t : ℝ) :
    (Real.sin (t/2) : ℂ)^2 * (∑ k ∈ Finset.range (N+1), dirichletKernel k t) =
      (Real.sin (((N : ℝ)+1)*t/2)^2 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih,
      show (Real.sin (t/2) : ℂ)^2 * dirichletKernel (N+1) t =
        (Real.sin (t/2) : ℂ) * ((Real.sin (t/2) : ℂ) * dirichletKernel (N+1) t) by ring,
      dirichletKernel_sine_mul]
    have h := sin_square_step (((N : ℝ)+1)*t/2) (t/2)
    have h₁ : ((N : ℝ)+1)*t/2 + t/2 = (((N+1 : ℕ) : ℝ)+1)*t/2 := by
      push_cast; ring
    have h₂ : 2*(((N : ℝ)+1)*t/2)+t/2 = (((N+1 : ℕ) : ℝ)+1/2)*t := by
      push_cast; ring
    rw [h₁, h₂] at h
    exact_mod_cast (show Real.sin (((N : ℝ)+1)*t/2)^2 +
      Real.sin (t/2) * Real.sin ((((N+1 : ℕ) : ℝ)+1/2)*t) =
      Real.sin ((((N+1 : ℕ) : ℝ)+1)*t/2)^2 by linarith)

end Fourier
open Fourier
open Specs.SingleVariableAnalysis.Ch19.FejerKernel

theorem fejerKernel_normSquare : kernelNormSquare := by
  intro N t
  change ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
    (∑ k ∈ Finset.range (N+1), dirichletKernel k t) = _
  rw [sum_dirichletKernel_eq_square]
  rw [Complex.star_def, Complex.mul_conj']
  change _ = ((‖positiveModeSum N t‖^2 / ((N : ℝ)+1) : ℝ) : ℂ)
  push_cast
  ring

theorem fejerKernel_real : kernelReal := by
  intro N t
  rw [fejerKernel_normSquare]
  rfl

theorem fejerKernel_nonnegative : kernelNonnegative := by
  intro N t
  rw [fejerKernel_normSquare, Complex.ofReal_re]
  positivity

theorem fejerKernel_quotient : kernelQuotient := by
  intro N t ht
  have hs : Real.sin (t/2) ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hz
    exact ht k (by linarith)
  have hc : (Real.sin (t/2) : ℂ)^2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs)
  have he : (∑ k ∈ Finset.range (N+1), dirichletKernel k t) =
      ((Real.sin (((N : ℝ)+1)*t/2)^2 : ℝ) : ℂ) / (Real.sin (t/2) : ℂ)^2 := by
    apply (eq_div_iff hc).mpr
    rw [mul_comm]
    exact sum_dirichletKernel_sine_mul N t
  change ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
    (∑ k ∈ Finset.range (N+1), dirichletKernel k t) = _
  rw [he, ← Complex.ofReal_pow, ← Complex.ofReal_div, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hn : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp

namespace Fourier

theorem sum_dirichletKernel_at_lattice (N : ℕ) (k : ℤ) :
    ∑ j ∈ Finset.range (N+1), dirichletKernel j ((k : ℝ)*(2*Real.pi)) =
      (((N : ℝ)+1)^2 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hk := dirichletKernel_at_lattice (N+1) k
    change dirichletKernel (N+1) ((k : ℝ)*(2*Real.pi)) = _ at hk
    rw [Finset.sum_range_succ, ih, hk]
    push_cast
    ring

end Fourier

theorem fejerKernel_at_lattice : kernelAtLattice := by
  intro N k
  change ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
    (∑ j ∈ Finset.range (N+1), dirichletKernel j ((k : ℝ)*(2*Real.pi))) = _
  rw [sum_dirichletKernel_at_lattice]
  push_cast
  have hn : (N : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (N : ℝ)+1 ≠ 0 by positivity)
  field_simp

theorem fejerKernel_continuous : kernelContinuous := by
  intro N
  exact continuous_const.mul (continuous_finsetSum _ (fun k _ => dirichletKernel_continuous k))

theorem fejerKernel_integrable : kernelIntegrability := by
  intro N
  exact complexIntegrable_of_continuousOn (by linarith [Real.pi_pos])
    (fejerKernel_continuous N).continuousOn

namespace Fourier

/-- Finite averaging for the proper complex Riemann integral. -/
theorem complexIntegral_average (g : ℕ → ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ k, ComplexIntegrable (g k) a b) (N : ℕ) :
    ∃ hs : ComplexIntegrable (fun t => ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (N+1), g k t) a b,
      complexIntegral _ hs = ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (N+1), complexIntegral _ (h k) := by
  obtain ⟨hs, hsv⟩ := complexIntegral_finset_linear (Finset.range (N+1))
    (fun _ => ((1 / ((N : ℝ)+1) : ℝ) : ℂ)) g hab h
  have heq : (fun t => ∑ k ∈ Finset.range (N+1),
      ((1 / ((N : ℝ)+1) : ℝ) : ℂ) * g k t) =
      (fun t => ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (N+1), g k t) := by
    funext t
    rw [Finset.mul_sum]
  have hs' := heq ▸ hs
  refine ⟨hs', ?_⟩
  have hi : complexIntegral _ hs' = complexIntegral _ hs := by
    congr 1; exact heq.symm
  rw [hi, hsv, Finset.mul_sum]

end Fourier

theorem fejerKernel_integral_mean : kernelIntegralMean := by
  intro N h
  obtain ⟨hs, hsv⟩ := complexIntegral_average dirichletKernel
    (by linarith [Real.pi_pos]) dirichletKernel_integrable N
  have hi : complexIntegral _ h = complexIntegral _ hs := rfl
  change ((1 / (2*Real.pi) : ℝ) : ℂ) * complexIntegral _ h = 1
  rw [hi, hsv, mul_left_comm, Finset.mul_sum]
  have hm (k : ℕ) : ((1 / (2*Real.pi) : ℝ) : ℂ) *
      complexIntegral _ (dirichletKernel_integrable k) = 1 :=
    dirichletKernel_integral_mean k (dirichletKernel_integrable k)
  simp_rw [hm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hn : (N : ℂ)+1 ≠ 0 := by exact_mod_cast (show (N : ℝ)+1 ≠ 0 by positivity)
  field_simp

theorem fejerMean_convolution : meanConvolution := by
  intro f hf h N x
  classical
  choose hy ht hyv htv using (fun k : ℕ => fourierPartialSum_convolution f hf h k x)
  obtain ⟨hs, hsv⟩ := complexIntegral_average
    (fun k t => f (x-t) * dirichletKernel k t)
    (by linarith [Real.pi_pos]) ht N
  have heq : (fun t => ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (N+1), f (x-t) * dirichletKernel k t) =
      (fun t => f (x-t) * fejerKernel N t) := by
    funext t
    change _ = f (x-t) * (((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (N+1), dirichletKernel k t)
    rw [← Finset.mul_sum]
    ring
  have hs' := heq ▸ hs
  refine ⟨hs', ?_⟩
  have hi : complexIntegral _ hs' = complexIntegral _ hs := by
    congr 1; exact heq.symm
  change ((1 / ((N : ℝ)+1) : ℝ) : ℂ) *
    (∑ k ∈ Finset.range (N+1), fourierPartialSum f h k x) =
      ((1 / (2*Real.pi) : ℝ) : ℂ) * complexIntegral _ hs'
  rw [hi, hsv, mul_left_comm]
  apply congrArg (fun z : ℂ => ((1 / ((N : ℝ)+1) : ℝ) : ℂ) * z)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => htv k)

theorem fejerMean_real_convolution : realMeanConvolution := by
  intro f hf h N x
  have hc : PeriodicRiemannIntegrable (fun y => (f y : ℂ)) :=
    ⟨hf.1.comp Complex.ofReal, fourierRealEmbedding_integrable f hf.2⟩
  exact fejerMean_convolution _ hc h N x

end SingleVariableAnalysis
